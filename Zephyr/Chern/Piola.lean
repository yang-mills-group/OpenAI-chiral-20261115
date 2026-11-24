import Zephyr.Chern.Grad
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Matrix Silk


/-!
# Algebraic Piola identity

Use the exceptional (grading) coordinate first, with pole **+1**.
Divergence and contractions are in the Laurent algebra, not pointwise
determinant identities assuming a gap or an invertible Jacobian.
-/

section
variable {I : Type} [DecidableEq I] (a : Axis)

open Finset in
private lemma D_prod (s : Finset I) (f : I → Silk) (F : I → I → Silk)
    (he : ∀ i,D a (f i)=F i i) (hn : ∀ i j,j≠i → F i j=f j) :
    D a (∏ i∈s, f i) = ∑ i∈s, ∏ j∈s, F i j := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have htail : (∏ j∈s, F i j)=(∏ j∈s, f j) := Finset.prod_congr rfl
      (fun j hj => hn i j fun e => hi (e ▸ hj))
    simp_rw [Finset.prod_insert hi]
    rw [sum_insert hi, D_mul, he, htail, ih, add_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [hn j i (fun e=> hi (e.symm ▸ hj))]

open Finset in
lemma D_det [Fintype I] (M : Matrix I I Silk) :
    D a M.det = ∑ i, (M.updateRow i (fun c => D a (M i c))).det := by
  conv_lhs => rw [←det_transpose, det_apply, map_sum]
  simp_rw [←det_transpose (updateRow _ _ _), det_apply]

  conv_rhs => rw [sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [transpose_apply,Units.smul_def]
  rw [map_zsmul,←smul_sum]
  refine congrArg _ (D_prod a Finset.univ (fun i=> M i (σ i))
    (fun i j=> M.updateRow i (fun c => D a (M i c)) j (σ j))
    (by intro; rw [updateRow_self]) ?_)
  intro i j h; rw [updateRow_ne h]

lemma det_flip [Fintype I] {i j : I} (hne : i≠j) (M N : Matrix I I Silk)
    (hi : M i=N j) (hj : M j=N i)
    (ho : ∀ k,k≠i → k≠j → M k=N k) :
    M.det = -N.det := by
  have e : M=N.submatrix (Equiv.swap i j) id := by
    ext k c
    rw [submatrix_apply,id_eq]
    by_cases a : k=i
    · subst k; rw [Equiv.swap_apply_left, hi]
    by_cases b : k=j
    · subst k; rw [Equiv.swap_apply_right,hj]
    rw [Equiv.swap_apply_of_ne_of_ne a b,ho k a b]
  rw [e, det_permute,Equiv.Perm.sign_swap hne]
  simp

end

abbrev Five := Fin 5
abbrev Streams := Five → Silk

def frameM (f : Streams) : Matrix Five Five Silk :=
  Matrix.of (Fin.cases f (fun (a : Axis) j => D a (f j)))

@[simp] lemma frame_0 (f) : frameM f 0=f := by rfl
@[simp] lemma frame_succ (f) (a : Axis) : frameM f a.succ= fun j=>D a (f j) := by rfl

/-- top form coefficient -/
def jac (f : Streams) := (frameM f).det

/-- unit vector (algebraically, no real condition) -/
def Sphere (f : Streams) := f ⬝ᵥ f=1

private def pole : Streams := Pi.single 0 1

variable (f : Streams)

private def altered (i : Five) := (frameM f).updateRow i pole
private def T (i : Five) := det (altered f i)

private def derivand (a : Axis) (i : Five) : Matrix Five Five Silk :=
  let M := altered f a.succ
  M.updateRow i (fun j=> D a (M i j))

private lemma front (a : Axis) : det (derivand f a 0) = -T f 0 := by
  have ne := a.succ_ne_zero
  unfold derivand T altered
  apply det_flip ne
  · rw [updateRow_ne ne, updateRow_self, updateRow_self]
  · rw [updateRow_self,updateRow_ne ne,updateRow_ne ne.symm,frame_0,frame_succ]
  intro k h ha
  rw [updateRow_ne ha,updateRow_ne h,updateRow_ne ha]

private lemma flip (a b : Axis) :
    det (derivand f a b.succ)= -(det (derivand f b a.succ)) := by

  by_cases p : a=b
  · subst b
    rw [det_eq_zero_of_row_eq_zero (A:=derivand f a a.succ) a.succ,neg_zero]
    intro j
    simp only [derivand, altered,updateRow_self]
    change D a (pole j)=0
    by_cases j=0 <;> simp_all [pole]
  have h : a.succ≠b.succ := by simpa
  unfold derivand altered
  -- a.succ is pole in LHS and double derivative in RHS
  apply det_flip h
  · rw [updateRow_ne h,updateRow_self,updateRow_ne h.symm,updateRow_self]
  · rw [updateRow_self,updateRow_self,updateRow_ne h.symm, updateRow_ne h,
      frame_succ,frame_succ]
    exact funext fun j=> D_symm .. 
  intro k ha hb
  rw [updateRow_ne hb,updateRow_ne ha,updateRow_ne ha,updateRow_ne hb]

private lemma half0 (z : Silk) (h : z = -z) : z=0 := by
  apply E_ext
  intro t
  rw [map_zero]
  have e : E t z = -E t z := by rw [← map_neg,←h]
  apply (mul_eq_zero.mp (_ : (2:ℂ)* E t z = 0)).resolve_left two_ne_zero
  rw [two_mul]
  exact add_eq_zero_iff_eq_neg.mpr e

private lemma divT :
    ∑ a : Axis, D a (T f a.succ) = -(4 * T f 0) := by
  have ht : ∑ a : Axis, ∑ b : Axis, det (derivand f a b.succ)=0 := by
    apply half0
    conv_rhs => rw [Finset.sum_comm]
    simp_rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl (fun b _ => flip f a b))

  have sumD (a : Axis) : D a (T f a.succ) = -T f 0+
      ∑ b : Axis, det (derivand f a b.succ) := by
    rw [T,D_det]
    change ∑ i : Five, det (derivand f a i) = _
    rw [Fin.sum_univ_succ,front]
  simp_rw [sumD, Finset.sum_add_distrib,ht, Finset.sum_const]
  simp [Axis,nsmul_eq_mul]

private lemma crater : T f ᵥ* frameM f = jac f • pole := by
  have e : T f = (frameM f)ᵀ.cramer pole := funext fun i => by
    rw [cramer_apply,updateCol_transpose,det_transpose];rfl
  rw [e,←mulVec_transpose,mulVec_cramer,det_transpose];rfl

variable {f}
private lemma Sphere.normal (h : Sphere f) : frameM f *ᵥ f = pole := by
  funext i
  change frameM f i ⬝ᵥ f = pole i
  induction i using Fin.cases
  · rw [frame_0,h, pole,Pi.single_eq_same]
  · rename_i a
    rw [pole,Pi.single_eq_of_ne a.succ_ne_zero]
    apply half0
    rw [← add_eq_zero_iff_eq_neg]
    have d := congrArg (D a) h
    simp only [dotProduct,map_sum, D_mul, Derivation.map_one_eq_zero] at d
    rw [← d,frame_succ, dotProduct,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _=> by rw [mul_comm]

private lemma Sphere.Tzero (h : Sphere f) : T f 0 = jac f * f 0 := by
  have e := dotProduct_mulVec (T f) (frameM f) f
  rw [Sphere.normal h, crater, smul_dotProduct, dotProduct_comm pole, pole, dotProduct_single,dotProduct_single,
    mul_one,mul_one,smul_eq_mul] at e
  exact e

private lemma Sphere.crest (h : Sphere f) :
    ∑ a : Axis, D a (f 0) * T f a.succ = jac f * ((1+f 0)*(1-f 0)) := by
  have e := congrFun (crater f) 0
  change (∑ i : Five, T f i * frameM f i 0) = _ at e
  rw [Fin.sum_univ_succ,h.Tzero,pole,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one,frame_0] at e
  simp_rw [frame_succ,mul_comm (T f _)] at e
  rw [eq_sub_of_add_eq' e]
  ring

private lemma Sphere.form (h : Sphere f) (n : ℕ) :
    ∑ a : Axis,D a ((1+f 0)^n * T f a.succ) =
      ((2*(n:Silk)+4)*((1+f 0)^n*jac f)-
        ((n:Silk)+4)*((1+f 0)^(n+1)*jac f)) := by
  simp_rw [D_mul, Finset.sum_add_distrib, ←Finset.mul_sum,divT,Sphere.Tzero h,
    Derivation.leibniz_pow,map_add, Derivation.map_one_eq_zero,zero_add,nsmul_eq_mul,smul_eq_mul]
  conv => enter [1,2,2,x]; rw [mul_assoc,mul_assoc]
  rw [←Finset.mul_sum,←Finset.mul_sum, h.crest]
  cases n
  · push_cast;ring
  · rw [Nat.succ_sub_one]
    ring

def moment (f : Streams) (n : ℕ) := τ ((1+f 0)^n*jac f)

/-- Concentrating moments from divergence (the averaging functional is
positive on nonnegative functions, but `jac` itself needn't be). -/
lemma Sphere.recur (h : Sphere f) (n : ℕ) :
    ((n:ℂ)+4)*moment f (n+1)=(2*n+4)*moment f n := by
  have e:= congrArg τ (h.form n)
  have hnum : ((n:Silk)+4) = algebraMap _ _ ((n:ℂ)+4) := by simp [map_ofNat]
  have hnum' : (2*(n:Silk)+4)=algebraMap _ _ (2*(n:ℂ)+4) := by simp [map_ofNat]
  rw [map_sum,map_sub,hnum,hnum',←Algebra.smul_def,←Algebra.smul_def,
    map_smul,map_smul,smul_eq_mul,smul_eq_mul] at e
  simp_rw [τ_D, Finset.sum_const,smul_zero] at e
  exact (sub_eq_zero.mp e.symm).symm
