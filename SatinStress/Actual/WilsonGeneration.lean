import SatinStress.Actual.Settles
import YM.CF.Tulip.Tag
import YM.CF.Sedge.Pause

/-!
# generation commutation through the actual Wilson matrix

Uniform in the **same** link field, even for nonunitary factorizations of
Flavor operators (we'll use the SL3 extension with `fixedSea`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open Function Filter NormedSpace Finset MeasureTheory Matrix
open SU Lat Lattice Cube Tulip Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra

variable (N : Side)

def actualRep (x : Piece) := jump (Equiv.refl (Site N)) fun _ => (1:Op SpinIdx) ⊗ₖ x
lemma actual_one : actualRep N 1 = 1 := by simp [actualRep,jump_id]
lemma actual_star (x : Piece) : star (actualRep N x)=actualRep N (star x) := by simp [actualRep, jump_star,op_star_kron]
lemma actual_mul (x y : Piece) : actualRep N (x*y)=actualRep N x*actualRep N y := by simp [actualRep,jump_mul,op_kron_mul]

lemma projector_commutes {n : Type*} [Fintype n] [DecidableEq n] {X H : Op n} (h : Commute X H) : Commute X (projector H) := by
  have hS : Commute X (slack H) :=
    (Commute.one_right X).sub_right ((h.pow_right 2).smul_right _)
  have he : Commute X (rsEval H) := Commute.tsum_right _ (fun k => (hS.pow_right k).smul_right _)
  exact ((Commute.one_right X).add_right ((h.smul_right (1/16:ℝ)).mul_right he)).smul_right _
lemma through_spin (X : Piece) (A : Op SpinIdx) : Commute (actualRep N X) (spin N Slot A) := by
  unfold actualRep spin Commute SemiconjBy; simp [jump_mul,op_kron_mul]

variable {N}
local notation "ℍ" => Site N × SpinIdx × Slot
variable (P : RLink N E) (t : Site N) (g h : Op Age)

lemma through_shift (i : Axis) : Commute (actualRep N (pool g h)) (shift matter P t i) := by
  unfold actualRep shift Commute SemiconjBy; simp only [jump_mul, Equiv.refl_trans, Equiv.trans_refl, Equiv.refl_apply]
  unfold hop color
  simp only [Matrix.mul_smul, Matrix.smul_mul,op_kron_mul,mul_one,pure_pool g h (P (_,i))] -- meta `_` not binder; use fun g lemma
lemma through_H : Commute (actualRep N (pool g h)) (frame matter P t).H := by
  let X := actualRep N (pool g h)
  let W := frame matter P t
  have he (i : Axis) : Commute X (W.T i) := through_shift P t g h i
  have hf (i : Axis) : Commute X (star (W.T i)) := by
    have hh := (through_shift P t (star g) (star h) i).star_star
    change Commute _ (star (W.T i)) at hh
    rw [pool_star, actual_star, star_star] at hh; exact hh
  refine (through_spin N _ grading).mul_right ((Commute.one_right X).neg_right.add_right ?_)
  exact Commute.sum_right _ _ _ (fun i _ =>
    ((Commute.one_right X).sub_right (((he i).add_right (hf i)).smul_right (1/2:ℝ))).add_right
      ((through_spin N (pool g h) (gammaOp i)).mul_right (((he i).sub_right (hf i)).smul_right (1/2:ℝ))))

variable (N) in
def gen (x : Piece) : Op (Single N) := portW (helix N).symm (actualRep N x)
-- Useful lemma: matches simple constant action on `Single`
lemma entry_gen (x : Piece) : gen N x = (1: Op (Site N × SpinIdx)) ⊗ₖ x := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨A,B⟩,C⟩; unfold gen portW actualRep; simp only [submatrix_apply];
  change (jump (Equiv.refl (Site N)) _) (a,b,c) (A,B,C) = _
  by_cases t:a=A <;> by_cases g:b=B <;> simp [jump_apply, t,g]

variable (N) in
lemma gen_one : gen N 1=1 := by simp [entry_gen]
lemma gen_mul (x y : Piece) : gen N (x*y)=gen N x*gen N y := by simp [entry_gen,op_kron_mul]
lemma gen_star (x : Piece) : star (gen N x)=gen N (star x) := by simp [entry_gen,op_star_kron]

set_option quotPrecheck false
local notation "Φ" => portW (helix N).symm (projector (frame matter P t).H)
lemma keeps : Commute Φ (gen N (pool g h)) := by
  unfold Commute SemiconjBy portW gen -- new portW
  unfold portW
  simp_rw [submatrix_mul_equiv]; rw [← (projector_commutes (through_H P t g h)).eq]
variable (N) in
def ageRep (s : Bool) : SL3 →* Op (Single N) where
  toFun x := gen N (if s then pool x.val 1 else pool 1 x.val)
  map_one' := by cases s <;> simp [gen_one,pool_one] -- spread
  map_mul' x y := by cases s <;> simp [← gen_mul, ← pool_mul]

lemma gen_life (w : Wave (Single N)) (e : Safe (frame matter P t).H) (p : Sea Φ w) (g h : Op Age) (hg : g.det=1) (hh : h.det=1) :
    acts (quant (gen N (pool g h))) w=w := by
  let i : SL3 := ⟨g,hg⟩; let j : SL3 := ⟨h,hh⟩
  have hl : ∀ b : Bool, ∀ i, Commute Φ (ageRep N b i) := by
    intro b i; cases b <;> exact keeps P t _ _
  have he b i := fixedSea _ (carts_p _ e.projection) w p (ageRep N b) (hl b) i
  have ht : gen N (pool g h) = ageRep N true i * ageRep N false j := by
    change _ = gen N (pool g 1)*gen N (pool 1 h); rw [← gen_mul, ← pool_mul]; simp
  rw [ht,quant_mul,act_mul,he,he]
lemma flavor_here (w : Wave (Single N)) (e : Safe (frame matter P t).H) (p : Sea Φ w) (g : Flavor) :
    acts (quant (gen N (turn g))) w=w :=
  gen_life P t w e p _ _ (Menu.pos_det g.1.val g.1.property) (Menu.pos_det g.2.val g.2.property)
end YM.CF.SatinStressData
