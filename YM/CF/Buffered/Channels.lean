import YM.CF.Buffered.Evolution

/-!
# Channels in the two slabs

Use `chord` **also within the regrouping of the two-slab trace**. Thus the
Koszul sign when crossing two odd factors (same-layer as well as subsequent
layers) is built into multiplication of squares. No hypothesis that only even
seam indices are needed! With this method the answer for TWO slabs is given
in terms of the cross-channel Hilbert-Schmidt contraction, and we will not
need to put phase factors of modulus one on the individual slab kernel. (This
normalization of the kernel is for precisely the two-slab Gram calculation,
not the many-slab transfer of pressure.)
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra

section algebra
variable {J : Type*} [Fintype J] [LinearOrder J]
local notation "A" => FC J
lemma square_mul (U : UNI J) (S : Finset J) {b c : Bool} {f g f' g' : A}
    (h : Sector S b g) (k : Sector S c f') (e : twist U (cutM S) = cutM Sᶜ) :
    pairSquare U b f g * pairSquare U c f' g' = pairSquare U (b.xor c) (f * f') (g * g') := by
  -- same calculation as Reflect/Cone. Here the two sides needn't use the same mark.
  let X := g; let P := theta U f; let B := theta U f'; let Y := g'
  change (chord b • (P * X)) * (chord c • (B * Y)) = chord (b.xor c) • (theta U (f*f')*(X*Y)); rw [theta_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  have he : X*B=Sector.grainB b c • (B*X) := Sector.apart h (theta_carries U k e) disjoint_compl_right
  rw [←mul_assoc (P*X),mul_assoc P,he, Algebra.mul_smul_comm,Algebra.smul_mul_assoc, smul_smul, smul_smul,grade_phase]; unfold P B; simp only [mul_assoc]
lemma sector_real {f : A} {s : Finset J} {b : Bool} (t : ℝ) (h : Sector s b f) : Sector s b (t • f) := by
  rw [← show (t:ℂ) • f = t • f by ext i j; simp [Complex.real_smul]]; exact h.scale _
lemma sector_exp {f : A} {s : Finset J} (h : Sector s false f) : Sector s false (exp f) := by
  let V : Subalgebra ℂ A :=
    { carrier := {a|Sector s false a}
      mul_mem' := fun g h => Sector.mul g h
      add_mem' := fun g h => Sector.add g h
      zero_mem' := Sector.zero _
      one_mem' := Sector.one
      algebraMap_mem' c := by rw [Algebra.algebraMap_eq_smul_one]; exact Sector.one.scale c }
  exact NormedSpace.exp_mem (R := ℂ) (s := V) V.toSubmodule.closed_of_finiteDimensional (show f ∈ V from h)
lemma theta_exp (U : UNI J) (f : A) : exp (theta U f) = theta U (exp f) := by
  let T : A →+* A :=
    { toFun := theta U
      map_one' := theta_one U
      map_zero' := theta_zero U
      map_add' := theta_add U
      map_mul' := theta_mul U }
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact (map_exp T (theta_cont _) _).symm
end algebra

variable {m B : Side}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
variable (i : Axis)
local notation "T" => RP.finger m B i
local notation "S" => colony m B i
abbrev Choices (m B : Side) := Option (Modes m B)

def picked (r : ℝ) (b : Bool) (x : Pack m B) : Choices m B → FC (Xmind m B)
  | none => 1
  | some a => Real.sqrt r • channel i b x a

lemma picked_sector (r : ℝ) (b) (x : Pack m B) (c) : Sector S c.isSome (picked i r b x c) := by
  cases c; exact Sector.one; exact sector_real _ (channel_sector ..)
lemma picked_cont (r : ℝ) (b) (c) : Continuous (fun x:Pack m B => picked i r b x c) := by
  cases c; exact continuous_const; exact Continuous.smul (continuous_const (y := Real.sqrt r)) (channel_cont ..)

lemma crossHop_expand (r : ℝ) (h : 0 ≤ r) (b : Bool) (x y z : Pack m B) :
    let a := tiedK m B i x;
    1 + r • crossHop i b (a y z) = ∑ j : Choices m B, pairSquare T j.isSome (picked i r b (a z z) j) (picked i r b (a y y) j) := by
  intro a
  rw [crossHop_sewn i b x y z, smul_sum, Fintype.sum_option]
  have he : pairSquare T false 1 1=1 := by rw [pairSquare,theta_one,chord,if_neg (by decide),one_mul,one_smul]
  rw [show Option.isSome (none:Choices m B)=false from rfl,picked,picked,he]
  congr 1; refine sum_congr rfl fun j _ => ?_
  dsimp only [Option.isSome,picked]
  unfold pairSquare; rw [theta_rsmul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    smul_smul, ← pow_two, Real.sq_sqrt h, smul_comm]

-- Channel tape per seam. Explicit finite products, from the layer nearest the BRA first.
def Tape (m B : Side) : ℕ → Type
  | 0 => Unit
  | n+1 => Choices m B × Tape m B n

instance Tape.finiteType : (n : ℕ) → Fintype (Tape m B n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by letI := Tape.finiteType n; exact inferInstanceAs (Fintype (Choices m B × Tape m B n))

def handStep (c : Foot m B) (r : ℝ) (x : Pack m B) (a b : Choices m B) : FC (Xmind m B) :=
  exp (r • slabGen i c x) * (picked i r false x a * picked i r true x b)
def hand (c : Foot m B) (r : ℝ) (x : Pack m B) : (n : ℕ) → Tape m B n → Tape m B n → FC (Xmind m B)
  | 0, _, _ => 1
  | n+1, a, b =>
    let u : Choices m B × Tape m B n := a; let v : Choices m B × Tape m B n := b
    handStep i c r x u.1 v.1 * hand c r x n u.2 v.2

def parityStep (a b : Choices m B) := a.isSome.xor b.isSome
def parityTape : (n : ℕ) → Tape m B n → Tape m B n → Bool
  | 0, _, _ => false
  | n+1, a, b =>
    let u : Choices m B × Tape m B n := a; let v : Choices m B × Tape m B n := b
    (parityStep u.1 v.1).xor (parityTape n u.2 v.2)
lemma handStep_sector (c : Foot m B) (r : ℝ) (x : Pack m B) (a b) :
    Sector S (parityStep a b) (handStep i c r x a b) := by
  simpa only [handStep, parityStep, Bool.false_xor] using (sector_exp (sector_real r (slabGen_sector i c x))).mul ((picked_sector i r false x a).mul (picked_sector i r true x b))
lemma hand_sector (c : Foot m B) (r : ℝ) (x : Pack m B) (n : ℕ) (a b) :
    Sector S (parityTape n a b) (hand i c r x n a b) := by
  induction n with
  | zero => exact Sector.one
  | succ n ih => exact (handStep_sector i c r x _ _).mul (ih _ _)
lemma handStep_cont (c : Foot m B) (r : ℝ) (a b) : Continuous (fun x : Pack m B => handStep i c r x a b) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact ((exp_continuous (𝔸:=A)).comp ((slabGen_cont i c).const_smul r)).mul ((picked_cont i r false a).mul (picked_cont i r true b))
lemma hand_cont (c : Foot m B) (r : ℝ) (n : ℕ) (a b) : Continuous (fun x : Pack m B => hand i c r x n a b) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (handStep_cont i c r _ _).mul (ih _ _)

section sums

lemma layer_expand (c : Foot m B) (u t : ℝ) (h : 0 ≤ t*u) (x y z : Pack m B) :
    let a := tiedK m B i x;
    Trotter.layer (u • theta T (slabGen i c (Pbar m B i (a y z)))) (u • slabGen i c (a y z))
      (u • crossHop i false (a y z)) (u • crossHop i true (a y z)) t =
        ∑ j : Choices m B,∑ k : Choices m B, pairSquare T (parityStep j k) (handStep i c (t*u) (a z z) j k)
          (handStep i c (t*u) (a y y) j k) := by
  intro a; let r:=t*u; let E(x:X) := exp (r • slabGen i c x)
  have hx(x y:X): exp (r • theta T (slabGen i c y))*exp (r • slabGen i c x) = pairSquare T false (E y) (E x) := by
    rw [← theta_rsmul, theta_exp,pairSquare]; exact (one_smul ..).symm
  unfold Trotter.layer; simp_rw [smul_smul]; rw [crossHop_expand i (t*u) h false x y z, crossHop_expand i (t*u) h true x y z,
    sew i, slabGen_local i c (strum i x y z y), slabGen_local i c (strum i x z y z), hx]
  rw [Finset.mul_sum (a:=pairSquare T false (E _) (E _)), Finset.sum_mul] -- distribute left * sum E then times sum and next
  refine sum_congr rfl fun j _=> ?_; rw [mul_sum]; refine sum_congr rfl fun k _=> ?_
  rw [mul_assoc, square_mul T S (picked_sector ..) (picked_sector ..) (movedCol ..)]
  simpa only [Bool.false_xor, handStep, parityStep] using square_mul T S (f:=E (a z z)) (g':=picked i r false (a y y) j * picked i r true (a y y) k) (sector_exp (sector_real r (slabGen_sector i c (a y y))))
    ((picked_sector i r false (a z z) j).mul (picked_sector i r true (a z z) k)) (movedCol ..)
end sums
lemma tapes_split_sum {n : ℕ} (f : Tape m B (n+1) → A) :
    ∑ t, f t = ∑ a : Choices m B, ∑ b : Tape m B n, f (show Tape m B (n+1) from (a,b)) := by
  exact Fintype.sum_prod_type (fun p : Choices m B × Tape m B n => f (show Tape m B (n+1) from p))

lemma n_layer_expand (c : Foot m B) (u t : ℝ) (h : 0 ≤ t*u) (x y z : Pack m B) (n : ℕ) :
    let a := tiedK m B i x;
    (Trotter.layer (u • theta T (slabGen i c (Pbar m B i (a y z)))) (u • slabGen i c (a y z))
      (u • crossHop i false (a y z)) (u • crossHop i true (a y z)) t)^n =
        ∑ j : Tape m B n, ∑ k : Tape m B n, pairSquare T (parityTape n j k)
          (hand i c (t*u) (a z z) n j k) (hand i c (t*u) (a y y) n j k) := by
  intro a; induction n with
  | zero =>
    rw [pow_zero]
    letI : Unique (Tape m B 0) := inferInstanceAs (Unique Unit)
    simp only [Fintype.sum_unique, parityTape, hand, pairSquare, theta_one, mul_one, chord, Bool.false_eq_true, ↓reduceIte, one_smul]
  | succ n ih =>
    rw [pow_succ', ih, layer_expand i c u t h x y z, tapes_split_sum, Finset.sum_mul]
    refine sum_congr rfl fun j _=> ?_
    conv_rhs => arg 2; ext b; rw [tapes_split_sum]
    rw [sum_mul]; conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine sum_congr rfl fun l _=> ?_
    rw [Finset.mul_sum]; refine sum_congr rfl fun m _=> ?_
    exact square_mul T S (handStep_sector ..) (hand_sector ..) (movedCol ..)
end YM.CF.Buffered.Heat
