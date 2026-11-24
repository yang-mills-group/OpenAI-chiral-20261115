import YM.CF.Matter.Pair
import YM.CF.Fock.Ket
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! SU(N) explicit local frame transport for the bending around flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Matrix Filter
open scoped Topology Matrix.Norms.Frobenius NNReal BigOperators ComplexConjugate InnerProductSpace
variable {n : Type*} [Fintype n] [DecidableEq n]

def trueS (U : Op n) : Prop := U∈unitary (Op n) ∧ U.det=1
lemma suit_one : trueS (1:Op n):=⟨(unitary _).one_mem,Matrix.det_one⟩
lemma suit_mul {A B:Op n} (h:trueS A)(g:trueS B): trueS (A*B):=⟨(unitary _).mul_mem h.1 g.1, by rw [Matrix.det_mul,h.2,g.2,mul_one]⟩
lemma suit_star {A:Op n} (h:trueS A):trueS (star A):=⟨by simpa using h.1,by simp [Matrix.star_eq_conjTranspose,h.2]⟩

def jet (A:Op n)(u:Ket n) : Ket n := WithLp.toLp _ (A *ᵥ u.ofLp)
lemma jet_mul (A B:Op n)(u:Ket n) : jet (A*B) u = jet A (jet B u) := by simp [jet, Matrix.mulVec_mulVec]
lemma jet_one (u:Ket n): jet 1 u=u := by simp [jet]
lemma jet_norm (A:Op n)(h:A∈unitary (Op n))(u:Ket n): ‖jet A u‖=‖u‖ := by
  exact (act_unit_norm (⟨A,h⟩ : UNI n) u)
lemma reachable (i j:n)(hi : i≠j)(u:Ket n)(h:‖u‖=1) : ∃ A:Op n,trueS A ∧ A*ᵥ Pi.single i 1=u.ofLp := by
  let V:n→Ket n:=fun _=>u
  have ho : Orthonormal ℂ (({i}:Set n).restrict V) := by
    constructor
    · intro x; exact h
    intro k l h; exact (h (Subsingleton.elim _ _)).elim
  obtain ⟨b,hb⟩:= ho.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  let e:=EuclideanSpace.basisFun n ℂ
  let A:= e.toBasis.toMatrix b.toBasis
  have hv := e.toMatrix_orthonormalBasis_mem_unitary b
  let d:n→ℂ:=fun x=>if x=j then star A.det else 1
  let B:=Matrix.diagonal d
  have hy:A.det*star A.det=1:=(Matrix.det_of_mem_unitary hv).2
  have hB:B ∈ unitary (Op n):=by
    apply mem_unitaryGroup_iff.mpr
    have hh : star B = diagonal (fun i=> star (d i)):=by ext x y; by_cases e:x=y <;> simp [e,B,Ne.symm]
    rw [hh,show B=diagonal d from rfl,diagonal_mul_diagonal];rw [show (fun i=>d i*star (d i))=1 by
      ext i; by_cases h:i=j <;> simp [d,h] <;> exact mul_eq_one_comm.mpr hy]; rfl
  refine ⟨A*B,⟨(unitary _).mul_mem hv hB,?det⟩,?_⟩
  case det => rw [Matrix.det_mul]; unfold B; simp [d,det_diagonal]; exact hy
  rw [← mulVec_mulVec,show B *ᵥ Pi.single i 1=Pi.single i 1 by simp [B,d,hi], mulVec_single_one]
  rw [show u=b i from (hb _ (Set.mem_singleton _)).symm]; rfl

private def qin (u v:Ket n):ℂ:= inner ℂ v u
private lemma qin_dot (u v:Ket n): qin u v= dotProduct (star v.ofLp) u.ofLp := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,qin,dotProduct_comm] -- check

def plate (u : Ket n):Op n:=Matrix.of fun i j=> u.ofLp i * star (u.ofLp j)
lemma cooker (u: Ket n): star (plate u)=plate u := by ext i j; simp [plate,mul_comm]
lemma cooker_plate (u:Ket n): plate u*plate u= qin u u • plate u := by
  ext i j
  simp only [qin_dot,Matrix.mul_apply,plate, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply]
  rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
private lemma plate_apply (u v:Ket n): plate u*ᵥ v.ofLp=qin v u • u.ofLp := by
  ext i
  simp only [mulVec,dotProduct,plate, Matrix.of_apply,qin_dot, Pi.star_apply, Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring

private def difference (u v:Ket n):ℂ:= inner ℂ (u-v) u
lemma difference_non {u v:Ket n}(hu:‖u‖=1)(hv:‖v‖=1)(h:u≠v) :
    let d:= difference u v; d+star d=qin (u-v) (u-v) ∧ d ≠ 0 := by
  have ha : inner ℂ u u=1:=by rw [inner_self_eq_norm_sq_to_K]; simp [hu]
  have hb : inner ℂ v v=1:=by rw [inner_self_eq_norm_sq_to_K]; simp [hv]
  have hm : difference u v + star (difference u v)=qin (u-v) (u-v):=by
    unfold difference qin; rw [inner_sub_right];
    simp only [inner_sub_left,ha,hb, ← starRingEnd_apply,map_sub,map_one,inner_conj_symm]; abel
  refine ⟨hm,fun hx=> ?_⟩
  rw [hx,star_zero,add_zero,qin] at hm; exact h (sub_eq_zero.mp (inner_self_eq_zero.mp hm.symm))
def rotary (u v: Ket n):Op n:=1-(difference u v)⁻¹ • plate (u-v)
lemma rotary_n {u v:Ket n}(hu:‖u‖=1)(hv:‖v‖=1)(h:u≠v) :
    rotary u v ∈ unitary (Op n) ∧ jet (rotary u v) u=v := by
  let d:=difference u v; let M:=plate (u-v); obtain ⟨hs,hh⟩:= difference_non hu hv h
  change d+star d=_ at hs; change d≠0 at hh
  constructor
  · change (1-d⁻¹ • M)∈_
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [star_sub,star_one,star_smul,star_inv₀, cooker, sub_mul,one_mul,mul_sub,mul_one,Matrix.smul_mul,Matrix.mul_smul, cooker_plate, ← hs, smul_smul,smul_smul]
    rw [show d⁻¹*(star d)⁻¹*(d+star d)=(star d)⁻¹+d⁻¹ by field_simp [hh]]
    rw [add_smul]; abel
  apply WithLp.ofLp_injective
  unfold jet rotary; rw [WithLp.ofLp_toLp,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,plate_apply,
    show qin u (u-v)=d from rfl, smul_smul, show difference u v=d from rfl,inv_mul_cancel₀ hh,one_smul,WithLp.ofLp_sub]
  abel

def shaft (i:n)(A:Op n):=WithLp.toLp 2 (A *ᵥ Pi.single i 1)
def wrapR (j:n)(A:Op n):Op n:= A * Matrix.diagonal (fun i=>if i=j then star A.det else 1)
lemma wrap_n {A:Op n}(h:A∈unitary (Op n))(j:n) : trueS (wrapR j A) ∧ ∀ i ≠ j, shaft i (wrapR j A)=shaft i A := by
  let d i:= if i=j then star A.det else 1
  have hy := (Matrix.det_of_mem_unitary h).2
  constructor
  · constructor
    · apply (unitary _).mul_mem h
      change Matrix.diagonal d ∈ _
      apply mem_unitaryGroup_iff.mpr
      rw [show star (Matrix.diagonal d)= Matrix.diagonal (fun i=>star (d i)) by ext i j; by_cases e:i=j <;> simp [e,d,Ne.symm],
        Matrix.diagonal_mul_diagonal, show (fun i=>d i * star (d i))=1 by
          ext i; by_cases v:i=j <;> simp [d,v] <;> exact mul_eq_one_comm.mp hy]; rfl
    unfold wrapR; rw [Matrix.det_mul]; simpa [Matrix.det_diagonal]
  intro i e; unfold shaft wrapR; rw [← Matrix.mulVec_mulVec]; simp [e]

section
-- Matrix smooth despite Frobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma mat_entry (i j:n) : ContDiff ℝ 1 (fun A:Op n=> A i j) := by
  let Z : Op n →ₗ[ℝ] ℂ := ⟨⟨fun A=> A i j,fun _ _=> rfl⟩, fun _ _=> rfl⟩
  exact Z.toContinuousLinearMap.contDiff
lemma mat_smooth (A:E→Op n) (x:E) (h:∀ i j, ContDiffAt ℝ 1 (fun x=>A x i j) x) : ContDiffAt ℝ 1 A x := by
  let Z:(n→n→ℂ)→ₗ[ℝ] Op n:=⟨⟨Matrix.of,fun _ _=> rfl⟩,fun _ _=> rfl⟩
  exact Z.toContinuousLinearMap.contDiff.contDiffAt.comp x (show ContDiffAt ℝ 1 (fun x i j=>A x i j) x from contDiffAt_pi.mpr fun i=>contDiffAt_pi.mpr fun j=> h i j)
end
lemma rotary_smooth (u v:Ket n)(hu:‖u‖=1)(hv:‖v‖=1)(h:u≠v): ContDiffAt ℝ 1 (rotary u) v := by
  have hg (k:n): ContDiffAt ℝ 1 (fun x:Ket n=> (u-x).ofLp k) v := (show ContDiff ℝ 1 (fun x:Ket n=> x.ofLp k) from (PiLp.proj (p:=2) (𝕜:=ℝ) (fun _=>ℂ) k).contDiff).contDiffAt.comp v (contDiffAt_const.sub contDiffAt_id)
  apply mat_smooth; intro i j
  unfold rotary plate
  simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul, Matrix.of_apply]
  apply ContDiffAt.sub contDiffAt_const
  apply ContDiffAt.mul
  · apply ContDiffAt.inv _ ((difference_non hu hv h).2)
    exact (contDiffAt_const.sub contDiffAt_id).inner ℂ contDiffAt_const
  exact (hg i).mul ((Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp v (hg j)))
lemma det_smooth (A:Op n) : ContDiffAt ℝ 1 Matrix.det A := by
  show ContDiffAt ℝ 1 (fun X : Op n=> X.det) A
  simp_rw [Matrix.det_apply]; apply ContDiffAt.sum; intro p _
  have ht : ContDiffAt ℝ 1 (fun X:Op n => ∏ i,X (p i) i) A := contDiffAt_prod (fun i _=> (mat_entry _ _).contDiffAt)
  rcases Int.units_eq_one_or p.sign with h|h <;> rw [h]
  · simpa using ht
  simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]; exact ht.neg
lemma wrap_smooth (j:n)(A:Op n) : ContDiffAt ℝ 1 (wrapR j) A:=by
  unfold wrapR; apply ContDiffAt.mul contDiffAt_id
  apply mat_smooth; intro i k; by_cases h:i=k
  · subst k; by_cases e:i=j <;> simp only [Matrix.diagonal_apply_eq, *, if_true,if_false]
    · exact (Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp A (det_smooth A))
    exact contDiffAt_const
  simp only [Matrix.diagonal_apply_ne _ h]; exact contDiffAt_const
lemma atlas (i j:n)(h:i≠j)(u:Ket n)(hu:‖u‖=1) : ∃ F:Ket n→Op n, ∀ v:Ket n,‖v‖=1→u≠v→trueS (F v)∧shaft i (F v)=v∧ ContDiffAt ℝ 1 F v := by
  obtain ⟨A,H,hA⟩:= reachable i j h u hu
  refine ⟨fun v=>wrapR j (rotary u v*A),fun v hv e=>?_⟩
  obtain ⟨hs,hd⟩:= rotary_n hu hv e; obtain ⟨hi,hj⟩:= wrap_n ((unitary _).mul_mem hs H.1) j
  refine ⟨hi,?_,(wrap_smooth j _).comp v ((rotary_smooth u v hu hv e).mul contDiffAt_const)⟩
  rw [hj i h,shaft,← Matrix.mulVec_mulVec,hA]; exact hd
end YM.CF.Mesa
