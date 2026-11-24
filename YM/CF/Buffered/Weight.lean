import YM.CF.Buffered.Channels

/-!
# On the support of the scalar indicators

Expand the (ordered) numerator with any two half marks. Work with the actual
phase controlled `pairWave`, not a sesquilinear fermionic determinant
assumption. We use the zero matrix as extension of `pair` for the Fock
expression off the actual support, only for convenient Borel versions.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "U" => upperP (CSide m B)

def seedArg (e : ℝ) := (TallyR m B e 0).indicator (fun x : X => Phase.pair m B x.1 x.2)
def seedOp (e : ℝ) (x : X) : A := exp (seedR U (seedArg e x))
def halfSeed (e : ℝ) (i : Axis) (x : X) : A :=
  exp (seedR U (Ledge m B i * seedArg e x * Ledge m B i))
section seed
lemma seedArg_env (b : Budget B e d) : Envelope (seedArg (m:=m) (B:=B) e) := by
  apply env_piece (TallyR m B e 0) (tally_meas ..) ((pair_cont b.1).mono fun _ p => tallyP p) 1
  intro x p; exact (CStarRing.norm_of_mem_unitary (kappa (0:Phase.Part m B) b.1 (tallyP p).1 (tallyP p).2).1).le
lemma seedOp_env (b : Budget B e d) : Envelope (seedOp (m:=m) (B:=B) e) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact Girt.pole_w (seedArg e) (fun v : Op I => exp (seedR U v))
    ((exp_continuous (𝔸:=A)).comp (continuous_seed U)) (seedArg_env b)
lemma halfSeed_env (b : Budget B e d) (i) : Envelope (halfSeed (m:=m) (B:=B) e i) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  refine Girt.pole_w (seedArg e) (fun v : Op I => exp (seedR U (Ledge m B i*v*Ledge m B i)))
    ?_ (seedArg_env b)
  exact (exp_continuous (𝔸:=A)).comp ((continuous_seed U).comp ((continuous_const.mul continuous_id).mul continuous_const))
lemma seed_match (b : Budget B e d) {x : Pack m B} (p : x ∈ TallyR m B e 0) :
    acts (seedOp e x) (linearB (CSide m B)) = pairWave (Phase.pair m B x.1 x.2) := by
  unfold seedOp seedArg; rw [Set.indicator_of_mem p]; exact (harvest_x (c:=0) b.1 (tallyP p)).symm
lemma seed_split (b : Budget B e d) (i : Axis) {x y z : Pack m B} (p : tiedK m B i x y z ∈ TallyR m B e 0) :
    let Q := tiedK m B i x;
    seedOp e (Q y z) = pairSquare (RP.finger m B i) false (halfSeed e i (Q z z)) (halfSeed e i (Q y y)) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  intro Q
  unfold seedOp halfSeed seedArg
  let V x := RP.Slater m B i x
  have he (v w:Pack m B) (h : NorthOf m B i v w) : V v=V w := congrArg (seedR U) (opens_pair i h)
  have ht := (RP.apt ..).mp p
  rw [Set.indicator_of_mem p, Set.indicator_of_mem ht.1, Set.indicator_of_mem ht.2, pairSquare]
  rw [initial_think i b.1 (tallyP p),show Pbar m B i (Q y z)=Q z y from sew ..]
  change exp (V (Q y z)+theta (RP.finger m B i) (V (Q z y))) = (1:ℂ) • _
  let a := V (Q y y); let c := V (Q z z); let F := RP.finger m B i
  have h : Commute (theta F c) a := by
    have x := Sector.apart (theta_carries F (initial_sector i (Q z z)) (movedCol ..)) (initial_sector i (Q y y)) disjoint_compl_left
    change _=(1:ℂ) • _ at x; rw [one_smul] at x; exact x
  rw [one_smul, he (Q y z) (Q y y) (strum ..), he (Q z y) (Q z z) (strum ..), add_comm,exp_add_of_commute h, ← theta_exp]
end seed

structure NorthMark (i : Axis) (f : RP.Test m B) : Prop where
  envelope : Envelope f
  sector (x) : Sector (colony m B i) false (f x)
  loc x y : NorthOf m B i x y → f x=f y

def testProduct (i : Axis) (f g : RP.Test m B) : RP.Test m B := fun x => theta (RP.finger m B i) (f (Pbar m B i x)) * g x
lemma product_env (i : Axis) {f g : RP.Test m B} (h : Envelope f) (k : Envelope g) : Envelope (testProduct i f g) :=
  env_mult (Girt.pole_w _ (theta (RP.finger m B i)) (theta_cont _) (Env.along h ((slideM m i).convey B).measurable)) k

def slabTerm (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t e : ℝ) (f E : RP.Test m B) (x : X) :=
  scalarWeight p W clip β t e x * (f x * E x * seedOp e x) U U

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
lemma heatTerm_slab (b : Budget B e d) (i : Axis) (cut : Foot m B) (f : RP.Test m B) :
    heatTerm p W clip β t e u (axisCut m B i cut) f = slabTerm p W clip β t e f (actualEvol i cut u) := by
  funext x
  unfold heatTerm slabTerm scalarWeight
  by_cases H : x∈TallyR m B e 0
  · rw [Set.indicator_of_mem H, Set.indicator_of_mem H]
    rw [actualEvol_quant, ← bra_fix (f x * quant (grow (wiel m B (axisCut m B i cut) x.1) u) * seedOp e x), act_mul (_ * _) (seedOp e x),seed_match b H, neg_one_mul, Complex.ofReal_mul]
    ring
  rw [Set.indicator_of_notMem H, Set.indicator_of_notMem H]; rw [mul_zero,zero_mul]

-- kernel with integration not yet made. Tape parity mismatches have zero entry
local notation "λ₀" => fun (i : ℕ)=> (i+1:ℝ)⁻¹
def rightHand (i : Axis) (cut : Foot m B) (u e : ℝ) (n : ℕ) (f : RP.Test m B)
    (x : Pack m B) (a b : Tape m B (n+1)) : FC (Xmind m B) :=
  f x * hand i cut ((λ₀ n) * u) x (n+1) a b * halfSeed e i x

def kernelInside (e : ℝ) (i : Axis) (cut : Foot m B) (n : ℕ)
    (f : RP.Test m B) (a b : Tape m B (n+1)) (x : Pack m B) : ℂ :=
  halfWeight p W clip β t e i x * rightHand i cut u e n f x a b U U

section
variable {p W}
lemma rightHand_sector (i : Axis) (cut : Foot m B) (n : ℕ)
    (f : RP.Test m B) (h : NorthMark i f) (a b : Tape m B (n+1)) (x : X) (e : ℝ) :
    Sector (colony m B i) (parityTape _ a b) (rightHand i cut u e n f x a b) := by
  have he := sector_exp (RP.letter U (colony m B i) (seedArg e x))
  simpa only [rightHand, Bool.xor_false, Bool.false_xor] using (((h.sector x).mul (hand_sector i cut _ x _ a b)).mul he : Sector (colony m B i) _ (rightHand i cut u e n f x a b))
lemma rightHand_env (i : Axis) (cut : Foot m B) (n : ℕ) (B' : Budget B e d) (f : RP.Test m B)
    (h : Envelope f) (a b : Tape m B (n+1)) : Envelope (fun x=>rightHand i cut u e n f x a b) :=
  env_mult (env_mult h (Env.compact (hand_cont ..))) (halfSeed_env B' i)
variable (p W) {a₁ a₂ : ℝ} (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include b H
lemma kernelInside_env (i : Axis) (cut : Foot m B) (n : ℕ) (f : RP.Test m B)
    (h : Envelope f) (a k : Tape m B (n+1)) : Envelope (kernelInside p W clip β t u e i cut n f a k) :=
  env_mult (halfWeight_env p H b clip β t i)
    (Girt.pole_w (fun x=> rightHand i cut u e n f x a k) (fun x:A=>x U U) (continuous_id.matrix_elem U U) (rightHand_env u i cut n b f h a k))
lemma slabTerm_env (f E : RP.Test m B) (h : Envelope f) (k : Envelope E) : Envelope (slabTerm p W clip β t e f E) :=
  env_mult (scalarWeight_env p H b clip β t)
    (Girt.pole_w _ (fun x:A=>x U U) (continuous_id.matrix_elem U U)
      (env_mult (env_mult h k) (seedOp_env b)))
lemma heatTerm_env (cut : Foot m B) (f : RP.Test m B) (h : Envelope f) : Envelope (heatTerm p W clip β t e u cut f) := by
  have hv (x : Pack m B) : heatTerm p W clip β t e u cut f x = scalarWeight p W clip β t e x *
      (f x * quant (grow (wiel m B cut x.1) u) * seedOp e x) U U := by
    unfold heatTerm scalarWeight
    by_cases k : x∈ TallyR m B e 0
    · rw [Set.indicator_of_mem k, Set.indicator_of_mem k]
      rw [← bra_fix (f x * quant (grow (wiel m B cut x.1) u) * seedOp e x), act_mul (_ * _) (seedOp e x),seed_match b k, neg_one_mul, Complex.ofReal_mul]; ring
    rw [Set.indicator_of_notMem k, Set.indicator_of_notMem k, mul_zero, zero_mul]
  rw [funext hv]; exact slabTerm_env p W clip β t b H f _ h (Env.compact (actualC ..))
lemma sewn_sum (hu : 0 ≤ u) (i : Axis) (cut : Foot m B) (n : ℕ) (f g : RP.Test m B) (hf : NorthMark i f) (hg : NorthMark i g)
    (x y z : Pack m B) : let Q := tiedK m B i x
    slabTerm p W clip β t e (testProduct i f g) (hotEvol i cut u n) (Q y z) =
      ∑ a : Tape m B (n+1), ∑ k : Tape m B (n+1),
        star (kernelInside p W clip β t u e i cut n f a k (Q z z)) * kernelInside p W clip β t u e i cut n g a k (Q y y) := by
  intro Q
  unfold slabTerm
  rw [scalarWeight_split p H b]
  by_cases k : Q y z ∈ TallyR m B e 0
  · let T := RP.finger m B i; let S := RP.colony m B i; let σ := Q z z; let γ := Q y y
    let F := f σ; let G := g γ
    let P := pairSquare T false F G
    let r := λ₀ n * u
    let A' := hand i cut r γ (n+1); let B' := hand i cut r σ (n+1)
    have ht : testProduct i f g (Q y z)= P := by
      unfold testProduct P pairSquare
      rw [show Pbar m B i (Q y z)=Q z y from sew .., hf.loc _ σ (strum ..), hg.loc _ γ (strum ..)]; exact (one_smul ..).symm
    have hE : hotEvol i cut u n (Q y z)= ∑ a,∑ b, pairSquare T (parityTape _ a b) (B' a b) (A' a b) := n_layer_expand i cut u _ (by positivity) x y z _
    rw [ht,hE,seed_split b i k]; simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply,Finset.mul_sum]; refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    let z' := halfSeed e i σ; let y' := halfSeed e i γ
    let w := parityTape _ a b
    have hz : Sector S false z' := sector_exp (RP.letter ..)
    have hA : Sector S w (A' a b) := hand_sector ..
    have hB : Sector S w (B' a b) := hand_sector ..
    have hv :
        P * pairSquare T w (B' a b) (A' a b) * pairSquare T false z' y' =
         pairSquare T w (rightHand i cut u e n f σ a b) (rightHand i cut u e n g γ a b) := by
      unfold P
      rw [square_mul T S (hg.sector γ) hB (movedCol ..), square_mul T S ((hg.sector γ).mul hA) hz (movedCol ..), Bool.false_xor, Bool.xor_false]; rfl
    let V₁ := rightHand i cut u e n f σ a b; let V₂ := rightHand i cut u e n g γ a b
    let h x := halfWeight p W clip β t e i x
    change star (h σ)*h γ * (P * pairSquare T w _ _ * pairSquare T false z' y') U U = star (h σ * V₁ U U) * (h γ * V₂ U U)
    rw [hv, show pairSquare T w V₁ V₂ U U = star (V₁ U U)*V₂ U U from
      theta_square U T (slide_plus i) S (movedCol ..) V₁ V₂ w (rightHand_sector u i cut n f hf a b σ _) (rightHand_sector u i cut n g hg a b γ _), star_mul']; ring
  dsimp only [kernelInside, halfWeight]
  rcases not_and_or.mp (show ¬ (Q y y∈ TallyR m B e 0 ∧ Q z z ∈ TallyR m B e 0) from fun h => k ((RP.apt ..).2 h)) with l|l
  all_goals dsimp only [Q] at l ⊢; simp_rw [Set.indicator_of_notMem l]; simp
end
end YM.CF.Buffered.Heat
