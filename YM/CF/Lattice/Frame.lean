import YM.Lattice.Path
import YM.CF.Lattice.Cliff
import YM.CF.Operator.Gap
import YM.CF.Operator.Commute

/-! Negative-mass Wilson kernel on a cubic fermion lattice.
Here links go from head to tail as in YM. Applied after refinement by taking a
fermion link = product of two gauge links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
open YM.Lattice
open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker Topology BigOperators
attribute [local instance] opCStarAlgebra
variable {N : Side}
def advance (i : Axis) : Equiv.Perm (Site N) where
  toFun x := x+step i
  invFun x := x-step i
  left_inv x := by simp
  right_inv x := by simp

variable {K n : Type*} [Group K] [Fintype n] [DecidableEq n]
abbrev RLink (N : Side) (K : Type*) := Links (Per N) K
abbrev Tx (N : Side) (n : Type*) := Site N × SpinIdx × n

/-- Put signs on the positive-direction hops from x at `x i=cut i`. -/
def seam (cut x : Site N) (i : Axis) : ℂ := if x i=cut i then -1 else 1
@[simp] lemma seam_norm (cut x : Site N) (i) : ‖seam cut x i‖ = 1 := by unfold seam; split <;> simp
@[simp] lemma seam_real (cut x : Site N) (i) : star (seam cut x i) = seam cut x i := by unfold seam; split <;> simp

variable (R : K →* UNI n) (U : RLink N K) (cut : Site N)
/-- spin replica of color link with seam. -/
def color (u : K) : Op (SpinIdx × n) := (1:Op SpinIdx) ⊗ₖ (R u).val
lemma color_mem (u : K) : color R u ∈ unitary (Op (SpinIdx × n)) := by
  rw [color, ← jump_replicate]
  exact jump_unitary _ _ fun _ => (R u).property
def hop (i : Axis) (x : Site N) := seam cut x i • color R (U (x,i))
lemma hop_mem (i) (x): hop R U cut i x ∈ unitary (Op _) := by
  unfold hop seam; split
  · simp only [neg_smul, one_smul]; have h := color_mem R (U (x,i))
    constructor
    · rw [star_neg,neg_mul_neg]; exact h.1
    rw [star_neg,neg_mul_neg]; exact h.2
  simpa using color_mem R _

def shift (i) := jump (advance i) (hop R U cut i)

def spin (N : Side) (n : Type*) [DecidableEq n] (A : Op SpinIdx) := jump (Equiv.refl (Site N)) (fun _ => A ⊗ₖ (1:Op n))

variable (N n) in
lemma spin_mul (A B) : spin N n A * spin N n B = spin N n (A*B) := by simp [spin,jump_mul,op_kron_mul]
variable (N n) in
lemma spin_one : spin N n 1 = 1 := by simp only [spin,Matrix.one_kronecker_one,jump_id]
variable (N n) in
lemma spin_adj (A : Op SpinIdx) : star (spin N n A) = spin N n (star A) := by simp only [spin,jump_star,Equiv.refl_symm, op_star_kron, star_one]
variable (N n) in
lemma spin_neg (A : Op SpinIdx) : spin N n (-A) = -spin N n A := by simp only [spin,op_kron_neg]; exact jump_neg _ _
lemma spin_shift (A) (i) : Commute (spin N n A) (shift R U cut i) := by
  rw [Commute, SemiconjBy,spin,shift,jump_mul,jump_mul]
  simp only [Equiv.refl_trans, Equiv.trans_refl,Equiv.refl_apply]
  unfold hop color; simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, op_kron_mul, mul_one, one_mul]

def frame : WilsonFrame (Tx N n) where
  T := shift R U cut
  gamma i := spin N n (gammaOp i)
  chir := spin N n grading
  shiftU i := jump_unitary _ _ (hop_mem R U cut i)
  spins i j := spin_shift ..
  signs i := spin_shift ..
  gammaSA i := by rw [isSelfAdjoint_iff,spin_adj,(gammaAdj i).star_eq]
  chirSA := by rw [isSelfAdjoint_iff,spin_adj,gradingAdj.star_eq]
  gammaSq i := by rw [spin_mul,gammaOne,spin_one]
  chirSq := by rw [spin_mul,gradingOne,spin_one]
  cliff i j h := by rw [spin_mul,spin_mul,gammaSwap i j h,spin_neg]
  graded i := by rw [spin_mul,spin_mul,gradingSwap,spin_neg]

lemma color_mul (u v : K) : color R (u*v) = color R u * color R v := by
  unfold color; rw [op_kron_mul, map_mul, mul_one]; rfl
lemma color_inv (u : K) : color R u⁻¹ = star (color R u) := by unfold color; rw [map_inv,op_star_kron,star_one]; rfl
lemma color_comm_cost {u v : K} :
    ‖color R u-color R v‖ ≤ ‖(R (u*v⁻¹)).val-1‖ := by
  unfold color; rw [← op_kron_sub]
  apply le_trans (replicas_bound (X:=SpinIdx) _) ?_
  rw [← CStarRing.norm_mul_coe_unitary ((R u).val - (R v).val) (star (R v))]
  apply le_of_eq
  change ‖((R u).val-(R v).val)*star (R v).val‖ = _
  rw [sub_mul, show (R v).val * star (R v).val = 1 from (R v).property.2,map_mul, map_inv]; rfl

/-- Plaquette test with operator norm in R. Uses all oriented i != j. -/
def PlaqBound (ε : ℝ) := ∀ (x : Site N) i j, i ≠ j → ‖(R (travel U x (square i j))).val-1‖ ≤ ε

lemma shiftNear (i j : Axis) (hne : i ≠ j) {ε : ℝ} (he : 0 ≤ ε) (hw : PlaqBound R U ε) :
    Switch ((frame R U cut).T i) ((frame R U cut).T j) ε := by
  change Switch (shift R U cut i) (shift R U cut j) ε
  unfold Switch shift
  rw [jump_mul,jump_mul,show (advance i).trans (advance j)=(advance j).trans (advance (N:=N) i) by
    ext x : 1; change x+_+_ = x+_+_; abel, ← jump_sub]
  apply jump_bound _ _ he; intro x
  simp only [advance,Equiv.coe_fn_mk,Pi.sub_apply]
  let a := U (x,i)
  let b := U (x+step i,j)
  let c := U (x,j)
  let d := U (x+step j,i)
  have hm := hw x i j hne
  have hz : travel U x (square i j)=a*b*(c*d)⁻¹ := by
    simp only [square,travel,Step.pos_read, Step.vec_pos, Step.neg_read,Step.vec_neg,
      mul_one]
    rw [show x+step i+step j-step i=x+step j by abel, show x+step i+step j+-step i-step j=x by abel]
    simp only [mul_inv_rev]; change _ = a*b*(d⁻¹*c⁻¹); rw [mul_assoc]
  change ‖seam cut x i • color R a * (seam cut (x+step i) j • color R b) -
    seam cut x j • color R c * (seam cut (x+step j) i • color R d)‖ ≤ _
  rw [show seam cut (x+step i) j=seam cut x j by simp [seam,hne.symm],
    show seam cut (x+step j) i=seam cut x i by simp [seam,hne],
    Algebra.smul_mul_assoc,Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
    smul_comm (seam cut x j), ← smul_sub, ← smul_sub, norm_smul,norm_smul, seam_norm,seam_norm,
    one_mul, one_mul, ← color_mul, ← color_mul]
  rw [hz] at hm
  exact (color_comm_cost ..).trans hm

theorem band [Nonempty n] (hw : PlaqBound R U (1/60)) : Safe (frame R U cut).H := by
  let W := frame R U cut
  refine ⟨W.selfadjoint, W.bounded.trans (by norm_num), ?_⟩
  convert W.gap (fun i j hij => shiftNear R U cut i j hij.ne (by norm_num) hw) using 2
  ring
end YM.CF.Lat
