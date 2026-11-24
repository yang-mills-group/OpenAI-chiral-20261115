import YM.CF.Lattice.Frame

/-! This is covariance at the chiral cutoff, covering all lattice gauge rotations
including large ones (no infinitesimal/weak-field assumption). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
open YM.Lattice
open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker Topology BigOperators
attribute [local instance] opCStarAlgebra
variable {N : Side} {K n : Type*} [Group K] [Fintype n] [DecidableEq n]
variable (R : K →* UNI n) (t : Site N → K) (U : RLink N K) (cut : Site N)

def conjG : UNI (Tx N n) :=
  ⟨jump (Equiv.refl (Site N)) (fun x => color R (t x)), jump_unitary _ _ fun _ => color_mem ..⟩
@[simp] lemma conjG_one : conjG (N:=N) R 1 = 1 := by
  apply Subtype.ext
  simp only [conjG,color,Pi.one_apply,map_one]
  change jump _ (fun _ => (1:Op SpinIdx) ⊗ₖ (1:Op n))=1
  rw [Matrix.one_kronecker_one,jump_id]
lemma conjG_mul (s : Site N → K) : conjG R (t*s)=conjG R t * conjG R s := by
  apply Subtype.ext; change _ = (conjG R t).val * (conjG R s).val; unfold conjG; dsimp only; rw [jump_mul]
  simp only [Pi.mul_apply,color_mul,Equiv.refl_trans,Equiv.refl_apply]
lemma twist_shift (i) : shift R (gauge t U) cut i = twist (conjG R t) (shift R U cut i) := by
  rw [twist_formula]; simp only [conjG, shift, jump_star,jump_mul,Equiv.refl_apply,
    Equiv.refl_trans, Equiv.refl_symm, Equiv.trans_refl]
  congr 1; funext x
  simp only [hop,Lattice.gauge,advance,Equiv.coe_fn_mk]
  simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
  change _ • color R _ = _ • (color R _ * color R _ * star (color R _))
  rw [color_mul,color_mul,color_inv]
lemma twist_spin (A) : twist (conjG R t) (spin N n A) = spin N n A := by
  rw [twist_formula]; simp only [conjG,jump_star,spin,jump_mul,Equiv.refl_apply, Equiv.refl_trans,Equiv.refl_symm]
  congr 1; funext x; rw [color,op_star_kron,op_kron_mul,op_kron_mul,one_mul,star_one,mul_one,mul_one]
  rw [show (R _).val*star (R _).val=1 from (R (t x)).property.2]
lemma twist_H0 : (frame R (gauge t U) cut).H0 = twist (conjG R t) (frame R U cut).H0 := by
  let F := frame R U cut; let E := frame R (gauge t U) cut; let G := twist (conjG R t)
  have hi (i) : G (F.inc i)= E.inc i := by
    have ht i : E.T i = G (F.T i) := twist_shift ..
    rw [WilsonFrame.inc,WilsonFrame.inc,map_add,map_mul, WilsonFrame.lap, WilsonFrame.diff, map_sub,map_one,map_smul,
      map_smul,map_add,map_star,map_sub,map_star, WilsonFrame.diff,WilsonFrame.lap,← ht]
    rw [show G (F.gamma i)= E.gamma i from twist_spin ..]
  change E.H0=G F.H0; simp only [WilsonFrame.H0,map_add,map_neg,map_one,map_sum,hi]
lemma twistH : (frame R (gauge t U) cut).H = twist (conjG R t) (frame R U cut).H := by
  unfold WilsonFrame.H; rw [map_mul,← twist_H0, show twist (conjG R t) (frame R U cut).chir = spin N n grading from twist_spin ..]; rfl
lemma plaq_gauge {ε : ℝ} (h : PlaqBound R U ε) : PlaqBound R (gauge t U) ε := by
  intro x i j he
  have hu : travel (gauge t U) x (square i j) = t x*travel U x (square i j)*(t x)⁻¹ := by rw [travel_gauge,square_stop]
  rw [hu,map_mul,map_mul,map_inv]
  let A := (R (travel U x (square i j))).val
  change ‖(R (t x)).val*A*star (R (t x)).val-1‖ ≤ _
  rw [← twist_formula, show twist _ A-1 = twist (R (t x)) (A-1) by rw [map_sub,map_one], twist_norm]
  exact h x i j he
lemma twist_projection [Nonempty n] (hw : PlaqBound R U (1/60)) :
    projector (frame R (gauge t U) cut).H = twist (conjG R t) (projector (frame R U cut).H) := by rw [twistH, projector_twist (band R U cut hw)]
section
variable [TopologicalSpace K] (hc : Continuous (fun x : K => (R x).val))
omit hc in
lemma jump_cont (f : Equiv.Perm (Site N)) : Continuous (jump (n:=n) f) := by
  refine continuous_matrix ?_
  rintro ⟨x,i⟩ ⟨y,j⟩
  simp only [jump_apply]; split <;> fun_prop
include hc
lemma color_cont : Continuous (color R) := by
  refine continuous_matrix ?_
  rintro ⟨x,i⟩ ⟨y,j⟩; simp only [color, Matrix.kronecker_apply]; exact continuous_const.mul (hc.matrix_elem i j)
lemma conjG_cont : Continuous (conjG (N:=N) R) := by
  apply Continuous.subtype_mk
  exact (jump_cont _).comp (continuous_pi fun x => (color_cont R hc).comp (continuous_apply _))
lemma shift_cont (i) : Continuous (fun U => shift R U cut i) :=
  (jump_cont _).comp (continuous_pi fun x => (continuous_const (y:=seam cut x i)).smul ((color_cont R hc).comp (continuous_apply (x,i))))
lemma H_cont : Continuous (fun U => (frame R U cut).H) := by
  unfold WilsonFrame.H
  apply Continuous.mul continuous_const
  unfold WilsonFrame.H0
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro i _
  unfold WilsonFrame.inc
  apply Continuous.add
  · unfold WilsonFrame.lap
    exact continuous_const.sub <| (continuous_const (y:=(1/2:ℝ))).smul ((shift_cont R cut hc i).add (shift_cont R cut hc i).star)
  unfold WilsonFrame.diff
  exact continuous_const.mul <| (continuous_const (y:=(1/2:ℝ))).smul ((shift_cont R cut hc i).sub (shift_cont R cut hc i).star)
lemma projector_cont [Nonempty n] : ContinuousOn (fun U => projector (frame R U cut).H)
    {U : RLink N K | PlaqBound R U (1/60)} :=
  (continuousOn_projector rho_lt rho_pos.le).comp (H_cont R cut hc).continuousOn (fun U h => (band R U cut h).good)
end
end YM.CF.Lat
