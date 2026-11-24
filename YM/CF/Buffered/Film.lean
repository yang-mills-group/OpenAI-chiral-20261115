import YM.CF.Buffered.Cascade
/-!
# A slab in local coordinates and transfer kernel

Don't require Hermitian individual films. Keep seam-data order fixed on
representation (entry then exit). Reflection will compare two such films,
alternating throughout.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Fock NormedSpace Finset Filter MeasureTheory Lattice Reflect RG Push.SectorMeasure Cin
open Sector (grainB)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
attribute [local instance] opCStarAlgebra
abbrev Cell (X Y:Type*) := (X×X)×Y
variable (X Y B J:Type*) [TopologicalSpace X][TopologicalSpace Y][MeasurableSpace X][MeasurableSpace Y][LinearOrder J][Fintype J]
structure Film where
 weight : Cell X Y→ℂ
 mark : Cell X Y→FC J
 seed : Cell X Y → FC J
 core : Cell X Y → FC J -- includes heat scalar
 side : Bool → B→ Cell X Y→FC J -- right = out; values scaled with sqrt(heat)
 regularA : Envelope weight
 regularB : Envelope mark
 regularC : Envelope seed
 regularD : Continuous core
 regularE b i : Continuous (side b i)
 sectorM z : Sector univ false (mark z)
 sectorV z : Sector univ false (seed z)
 sectorC z : Sector univ false (core z)
 sectorS b i z : Sector univ true (side b i z)
 sparse z i j : side false i z * side true j z = -(side true j z*side false i z)

def mirrorCell (x:Cell X Y):Cell X Y := (x.1.swap,x.2)
namespace Film
variable {X Y B J}
def port (F:Film X Y B J) (d:ℝ) (x:Cell X Y) (b:Bool) : Option B → FC J := fun i=> match i with
 | none=>1
 | some h=>d • F.side b h x
def ready (F:Film X Y B J) (x:Cell X Y) (t:ℝ) := exp (t • F.core x)
def stretch (F:Film X Y B J)(x:Cell X Y)(t:ℝ):Board J (Option B) := bind (ready F x t) Option.isSome (F.port (Real.sqrt t) x false) (F.port (Real.sqrt t) x true)

structure Reversed (F G:Film X Y B J) (U:UNI J) : Prop where
 gate x : G.weight (mirrorCell X Y x)=star (F.weight x)
 gen x: G.core (mirrorCell X Y x)=theta U (F.core x)
 stamp x: G.mark (mirrorCell X Y x)=theta U (F.mark x)
 set x: G.seed (mirrorCell X Y x)=theta U (F.seed x)
 endG b i x : G.side (!b) i (mirrorCell X Y x)=theta U (F.side b i x)

variable (F : Film X Y B J) (t:ℝ)
open Heat
lemma port_grade (b:Bool) (i:Option B) (x:Cell X Y) : Sector univ i.isSome (F.port t x b i):= by
 cases i; exact Sector.one; exact sector_real _ (F.sectorS ..)
lemma spare (i j:Option B) (x:Cell X Y) : F.port t x false i *F.port t x true j= grainB i.isSome j.isSome • (F.port t x true j * F.port t x false i) := by
  cases i <;> cases j <;> simp [port,grainB]; rw [F.sparse]; simp
lemma berth (x:Cell X Y)(i l:Option B):Sector univ (i.isSome.xor l.isSome) (F.stretch x t i l):= bind_local (Heat.sector_exp (sector_real _ (F.sectorC x))) _ _ (port_grade F _ _ i x) (port_grade F _ _ l x)
abbrev Leaf (p:ℕ)(B:Type*) := Tablet (Option B) p
def lace (k:ℕ)(j l: Leaf k B) (x:Cell X Y) := F.mark x * issue Option.isSome (F.stretch x t) k j l * F.seed x
def evaluate (b:Finset J)(k:ℕ)(j l:Leaf k B)(x:Cell X Y):ℂ:=F.weight x* lace F t k j l x b b

variable {G:Film X Y B J} {U:UNI J}
lemma turn (h:Reversed F G U) (k:ℕ) (x:Cell X Y)(i j:Leaf k B) :
 theta U (lace F t k i j x)=star (chord ((Stack.parity Option.isSome k i).xor (Stack.parity Option.isSome k j))) • lace G t k j i (mirrorCell X Y x) := by
  let y:=mirrorCell X Y x
  have he(b:Bool)(k:Option B): G.port (Real.sqrt t) y (!b) k=theta U (F.port (Real.sqrt t) x b k):=by cases k; exact (theta_one _).symm; unfold port; dsimp; rw [theta_rsmul,h.endG b]
  have hp(a b): theta U (F.stretch x t a b) = star (chord (a.isSome.xor b.isSome)) • G.stretch y t b a:= by
    refine bind_cov _ ?_ (he true) (he false) (fun i j=> G.spare _ i j y) _ _; rw [ready,ready,h.gen x,←theta_rsmul, Heat.theta_exp]
  unfold lace; rw [theta_mul,theta_mul,prism _ _ U hp,←h.stamp x,←h.set x,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma lace_sector (x:Cell X Y)(k:ℕ)(i j:Leaf k B) : Sector univ ((Stack.parity Option.isSome k i).xor (Stack.parity Option.isSome k j)) (lace F t k i j x):= by
 simpa only [lace,Bool.false_xor,Bool.xor_false] using (((F.sectorM x).mul (issue_here _ _ (berth F t x) k i j)).mul (F.sectorV x) : Sector univ _ _)
lemma wraps (h:Reversed F G U) (b:Finset J) (v:twist U (cutM bᶜ)=cutM b) (k:ℕ) (x:Cell X Y)(i j:Leaf k B) :
 star (Film.evaluate F t b k i j x)=evaluate G t b k j i (mirrorCell X Y x) := by
  let y:=mirrorCell X Y x; let c:=(Stack.parity Option.isSome k i); let d:=(Stack.parity Option.isSome k j)
  have he: theta U (lace F t k i j x) b b= _ := sea_vac b U v (lace F t k i j x)
  unfold evaluate; rw [h.gate x,star_mul',←he, F.turn t h, Matrix.smul_apply]; by_cases hz:c=d; swap
  · rw [(show Sector univ true (lace G t k j i y) from ?_).odd_lost, smul_zero]; have hh: d.xor c=true:= by cases f:c<;> cases e:d <;> first| rfl| rw [f,e] at hz; contradiction
    exact hh ▸ G.lace_sector t y k j i
  unfold c d at hz; rw [hz,Bool.xor_self, Reflect.chord]; simp

lemma stretch_cont (i j:Option B): Continuous fun x=> F.stretch x t i j := by
 letI : NormedAlgebra ℚ (FC J) := NormedAlgebra.restrictScalars ℚ ℝ (FC J)
 have hp(b:Bool)(k:Option B) : Continuous fun x=> F.port (Real.sqrt t) x b k := by cases k; exact continuous_const; exact Continuous.smul (f:=fun _=> Real.sqrt t) continuous_const (F.regularE ..)
 exact ((exp_continuous (𝔸:=FC J)).comp ((F.regularD).const_smul t)).mul (((hp false i).mul (hp true j)).const_smul (chord j.isSome))
lemma laceCore_cont (k:ℕ)(i j: Leaf k B): Continuous fun x=> issue Option.isSome (F.stretch x t) k i j := by
 induction k with | zero=> exact continuous_const | succ k ih=> exact (( (stretch_cont F t (i 0) (j 0)).mul (ih (Fin.tail i) (Fin.tail j))).const_smul (grainB ((i 0).isSome.xor (j 0).isSome) (Stack.parity Option.isSome k (Fin.tail i))))

variable [OpensMeasurableSpace (Cell X Y)] [CompactSpace X][CompactSpace Y]
lemma evalE (b:Finset J)(k:ℕ)(i j:Leaf k B): Envelope (F.evaluate t b k i j) := env_mult F.regularA (Girt.pole_w _ (fun A:FC J=>A b b) (continuous_id.matrix_elem _ _) (env_mult (env_mult F.regularB (Env.compact (laceCore_cont F t k i j))) F.regularC))
variable [MeasurableSpace B][DiscreteMeasurableSpace B][Fintype B]
def closure (μ:Measure Y) [IsFiniteMeasure μ] (b:Finset J)(k:ℕ)(x y : Leaf k B)(v:X×X):= ∫ z,F.evaluate t b k x y (v,z)∂μ
lemma closureE (μ:Measure Y) [IsFiniteMeasure μ] (b:Finset J)(k:ℕ)(x y : Leaf k B) : Envelope (F.closure t μ b k x y) := marginal (F.evaluate t b k x y) (evalE F t b k x y) μ
lemma closure_star (h:Reversed F G U)(μ:Measure Y)[IsFiniteMeasure μ](b:Finset J)(v:twist U (cutM bᶜ)=cutM b)(k:ℕ)(x y : Leaf k B)(z:X×X): star (F.closure t μ b k x y z)=G.closure t μ b k y x z.swap:=by unfold Film.closure; rw [←starRingEnd_apply, ←integral_conj (𝕜:=ℂ)]; exact integral_congr_ae (Eventually.of_forall fun i=> F.wraps t h b v k (z,i) x y)
end Film
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.Film.wraps
