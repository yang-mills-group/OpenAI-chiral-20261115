import YM.CF.Matter.North
/-! Equivariant real form using S9. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SU.Pair
open scoped Matrix.Norms.L2Operator Matrix BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
open Matrix ExTwo

lemma reachable (u : Ket F) (h : ‖u‖=1) : ∃ U:E, (fund U)*ᵥ e0=u.ofLp := by
  let V : F → Ket F := fun _ => u
  have ho : Orthonormal ℂ (({0}:Set F).restrict V) := by
    constructor
    · intro i; exact h
    intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  let e := EuclideanSpace.basisFun F ℂ
  let A := e.toBasis.toMatrix b.toBasis
  have hv := e.toMatrix_orthonormalBasis_mem_unitary b
  let d : F → ℂ := fun i => if i=1 then star A.det else 1
  let B := Matrix.diagonal d
  have hy : A.det * star A.det=1 := (Matrix.det_of_mem_unitary hv).2
  have hB : B ∈ unitary (Op F) := by
    apply mem_unitaryGroup_iff.mpr
    have hh : star B = diagonal (fun i => star (d i)) := by
      ext i j; by_cases e:i=j <;> simp [e,B, Ne.symm]
    rw [hh,show B=diagonal d from rfl,diagonal_mul_diagonal]; rw [show (fun i=>d i * star (d i))=1 by
      ext i; by_cases h:i=(1:F) <;> simp [d,h] <;> exact mul_eq_one_comm.mpr hy]; rfl
  have hx : (A*B).det=1 := by rw [Matrix.det_mul]; unfold B; simp [d,det_diagonal]; exact hy
  let W : UNI F := ⟨A*B,(unitary _).mul_mem hv hB⟩
  refine ⟨(⟨W,hx⟩:E),?_⟩
  change (A * B) *ᵥ _ = _
  rw [← mulVec_mulVec, show B *ᵥ e0 = e0 by simp [B,d,e0,basisVec,F]]
  unfold e0 basisVec
  rw [mulVec_single_one]
  rw [show u=b 0 from (hb _ (Set.mem_singleton _)).symm]
  rfl
lemma pair_laws (u : Ket F) (h : ‖u‖=1) :
    let M := pairM u.ofLp; Mᵀ=M ∧ M.det=1 ∧ M ∈ unitary (Op Sheet) := by
  dsimp only
  obtain ⟨U,hu⟩ := reachable u h
  rw [← hu, pairM_cong U e0]
  refine ⟨?_,?_, (unitary (Op Sheet)).mul_mem ((unitary _).mul_mem (each_mem U) northU) (transpose_mem_unitaryGroup_iff.mpr (each_mem U))⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul,Matrix.transpose_transpose,symmetric, Matrix.mul_assoc]
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,northOrientation,each_det]; norm_num

def fullM (u : Ket F) : Op Slot := (1:Op (Fin 3)) ⊗ₖ pairM u.ofLp
lemma full_laws (u : Ket F) (h : ‖u‖=1) :
    let M := fullM u; Mᵀ=M ∧ M.det=1 ∧ M ∈ unitary (Op Slot) := by
  obtain ⟨hl,hk,hc⟩ := pair_laws u h
  dsimp only; unfold fullM
  constructor
  · rw [← kroneckerMap_transpose,hl,transpose_one]
  refine ⟨?_,Matrix.kronecker_mem_unitary (unitary _).one_mem hc⟩
  rw [Matrix.det_kronecker,det_one,hk]; norm_num
lemma full_cong (g:E) (u:Ket F) : fullM (acts (fund g) u) =
    (matter g).val*fullM u*(matter g).valᵀ := by
  simp only [fullM,matter_matrix,triple,← kroneckerMap_transpose, transpose_one, op_kron_mul,mul_one]
  rw [show (acts (fund g) u).ofLp = (fund g) *ᵥ u.ofLp from rfl,pairM_cong]
lemma full_cont : Continuous fullM := by
  have he : Continuous (fun u:Ket F => pairM u.ofLp) := by
    apply continuous_matrix
    intro i j; cases i <;> cases j
    · simp only [pairM,Matrix.fromBlocks_apply₁₁,cc_apply,eps,Matrix.of_apply]
      apply Continuous.star
      apply Continuous.matrix_det
      apply continuous_matrix; intro i j; fin_cases i <;> simp [rows] <;> fun_prop
    all_goals simp only [pairM,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,mix,lone,
      Matrix.transpose_apply,Matrix.of_apply,exterior, Matrix.neg_apply, Matrix.vecMulVec_apply] <;> fun_prop
  apply continuous_matrix
  rintro ⟨x,i⟩ ⟨y,j⟩; exact continuous_const.mul (he.matrix_elem i j)
lemma full_uniform : UniformContinuousOn fullM {u | ‖u‖=1} :=
  (show IsCompact _ by
    rw [show {u : Ket F | ‖u‖=1}=Metric.sphere 0 1 by ext; simp]; exact isCompact_sphere ..).uniformContinuousOn_of_continuous full_cont.continuousOn
end YM.CF.SU.Pair
