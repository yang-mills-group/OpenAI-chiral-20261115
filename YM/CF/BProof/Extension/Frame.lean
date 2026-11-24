import YM.CF.BProof.Extension.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Sphere extension on successive columns, using the Lipschitz variation in orthogonal projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension
open Function Filter Metric Set Submodule Module
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexConjugate Classical

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

lemma ortho_span {ι : Type*} {f : ι → Y} {x : Y} : x∈ (span ℂ (range f))ᗮ ↔ ∀ i, ⟪f i,x⟫_ℂ=0 := by
 constructor; exact fun h i=> inner_right_of_mem_orthogonal (subset_span (mem_range_self i)) h
 intro h; apply (mem_orthogonal ..).mpr; intro y hy; induction hy using Submodule.span_induction with
 | mem y hy => obtain ⟨i,rfl⟩:=hy; exact h i
 | zero=> simp
 | add _ _ _ _ h k=> simp [inner_add_left,h,k]
 | smul _ _ _ h=> simp [inner_smul_left,h]

local instance realInner (Y : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] : InnerProductSpace ℝ Y := InnerProductSpace.rclikeToReal ℂ Y
-- force all inst in scope use this. supply modules.
local instance : IsScalarTower ℝ ℂ Y := RestrictScalars.isScalarTower .. -- tune
local instance : FiniteDimensional ℝ Y := FiniteDimensional.trans ℝ ℂ Y

private lemma compat (V : Submodule ℂ Y) (x : Y) :
    (V.restrictScalars ℝ).starProjection x=V.starProjection x := by
 apply eq_starProjection_of_mem_orthogonal (by exact (V.orthogonalProjectionOnto x).property)
 intro w hw
 change RCLike.re (⟪w, x-V.starProjection x⟫_ℂ)=0
 rw [inner_right_of_mem_orthogonal (show w∈ V from hw) (sub_starProjection_mem_orthogonal x)]; rfl

private lemma currency {J : Type*} [Fintype J] (F : J→Y) (h : Orthonormal ℂ F) (x : Y) :
    (span ℂ (range F)).starProjection x= ∑ i,⟪F i,x⟫_ℂ • F i := by
 apply eq_starProjection_of_mem_orthogonal
 · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
 apply ortho_span.mpr; intro i
 simp_rw [inner_sub_right,inner_sum,inner_smul_right,orthonormal_iff_ite.mp h]; simp

private lemma projectionLip {J : Type*} [Fintype J] (F : X→J→Y)(S : Set X)(h : ∀ x∈ S,Orthonormal ℂ (F x)) (K : ℝ) (k : 0≤K) (p : ∀ i,Lip S K (fun x=> F x i)) :
    Lip S (2*K*Fintype.card J) (fun x=> ((span ℂ (range (F x)))ᗮ.restrictScalars ℝ).starProjection) := by
 intro x hx y hy; apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
 intro z; rw [ContinuousLinearMap.sub_apply,compat,compat]; simp only [Submodule.starProjection_orthogonal', ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]; rw [currency (F x) (h x hx),currency (F y) (h y hy),sub_sub_sub_cancel_left,norm_sub_rev,← Finset.sum_sub_distrib]
 refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=> (K*dist x y*‖z‖)*2) (fun i _=> ?_)).trans_eq ?_)
 · let a:= F x i; let b:=F y i; change ‖⟪a,z⟫_ℂ • a-⟪b,z⟫_ℂ • b‖≤_
   have ha : ‖a‖=1:= (h x hx).1 _; have hb: ‖b‖=1:=(h y hy).1 _
   rw [show ⟪a,z⟫_ℂ • a-⟪b,z⟫_ℂ • b=⟪a-b,z⟫_ℂ • a+⟪b,z⟫_ℂ • (a-b) by rw [smul_sub,inner_sub_left, sub_smul]; abel]
   apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,ha,mul_one,mul_two]
   apply add_le_add
   · exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (p i x hx y hy) (norm_nonneg _))
   rw [mul_comm ‖⟪b,z⟫_ℂ‖]; exact mul_le_mul (p i x hx y hy) ((norm_inner_le_norm ..).trans (by rw [hb,one_mul])) (norm_nonneg _) (by positivity)
 simp; ring

private lemma codim {J : Type*} [Fintype J] (F : J→Y) (h : Orthonormal ℂ F) (hk : Fintype.card J+2 ≤ finrank ℂ Y) :
    4 ≤ finrank ℝ ((span ℂ (range F))ᗮ.restrictScalars ℝ) := by
 let V:= (span ℂ (range F)); let L:= Vᗮ
 have he:=V.finrank_add_finrank_orthogonal; rw [show finrank ℂ V=Fintype.card J from finrank_span_eq_card h.linearIndependent] at he
 have hm:= Module.finrank_mul_finrank ℝ ℂ L
 rw [Complex.finrank_real_complex] at hm
 change 4≤ finrank ℝ L; rw [← hm]; unfold L; omega

/-- Typical use on a k-face of scaled length one. Fill a partial orthonormal frame
of n-1 columns in ℂⁿ, n≥2. -/
theorem columns (n : ℕ) (K C : ℝ) (hk : 0<K) (hc : 0<C) (d : finrank ℝ X ≤ 3) (H : n < finrank ℂ Y) :
    ∃ L : ℝ,0<L ∧ ∀ (S T : Set X) (F : X→Fin n→Y), S ⊆ closedBall 0 K → T ⊆ S → T.Nonempty →
    (∀ x∈T,Orthonormal ℂ (F x)) → (∀ i, Lip T C (fun x=>F x i)) →
    ∃ G : X→Fin n→Y, EqOn F G T ∧ (∀ x∈S,Orthonormal ℂ (G x)) ∧ ∀ i, Lip S L (fun x=> G x i) := by
 induction n with
 | zero=>
    refine ⟨1,one_pos,fun S T F _ _ _ _ _=>⟨F,fun _ _=>rfl,fun x hx=>?_,finZeroElim⟩⟩; exact ⟨finZeroElim,fun ⦃i⦄=>i.elim0⟩
 | succ n ih=>
    obtain ⟨L,hl,V⟩:= ih (by omega)
    obtain ⟨c,hc',A⟩:=sphere_extend (X:=X) (Y:=Y) K (1+2*L*n) C hk (by positivity) hc
    refine ⟨max L c,hl.trans_le (le_max_left ..),fun S T F h hp he hT HG=>?_⟩
    obtain ⟨G,hw,w,g⟩:= V S T (fun x i=> F x i.succ) h hp he (fun x hx=> (hT x hx).comp _ (fun _ _=>Fin.succ_inj.mp)) (fun i=>HG i.succ) -- tune
    let U(x:X):= (span ℂ (range (G x)))ᗮ.restrictScalars ℝ
    have hv : Lip S (1+2*L*n) (fun x=> (U x).starProjection) := (projectionLip G S w L hl.le g).mono (Subset.refl _) (by simp)
    have ht'(x:X)(p:x∈ T) : ‖F x 0‖=1 ∧ F x 0∈ U x := by refine ⟨(hT x p).1 0,ortho_span.mpr fun i=>?_⟩; rw [← hw p]; exact (hT x p).2 (Fin.succ_ne_zero _)
    obtain ⟨b,hb,HZ,B⟩:= A S T U (fun x=> F x 0) h hp he (fun x hx=> by have ht:=codim _ (w x hx) (by rw [Fintype.card_fin]; exact H); exact (show finrank ℝ X<4 by omega).trans_le ht) hv ht' (HG 0)
    refine ⟨fun x=> Fin.cons (b x) (G x),?_,fun x hx=>?_ ,?_⟩
    · intro x hx; funext i; exact Fin.cases (hb hx) (fun j => by simpa using congrFun (hw hx) j) i
    · rw [orthonormal_iff_ite]; intro i j
      have ht:=ortho_span.mp (show b x∈(span ℂ (range (G x)))ᗮ from (HZ x hx).2)
      refine Fin.cases ?_ (fun i=> ?_) i
      · refine Fin.cases ?_ (fun j=>?_) j
        · simp [inner_self_eq_norm_sq_to_K,(HZ x hx).1]
        simp only [Fin.cons_zero,Fin.cons_succ,if_neg (Fin.succ_ne_zero j).symm]; exact inner_eq_zero_symm.mpr (ht j)
      refine Fin.cases ?_ (fun j=>?_) j
      · rw [if_neg (Fin.succ_ne_zero _)]; exact ht i
      simpa using orthonormal_iff_ite.mp (w x hx) i j
    intro i; refine Fin.cases ?_ (fun j=>?_) i
    · exact B.mono (Subset.refl _) (le_max_right ..)
    simpa using (g j).mono (Subset.refl _) (le_max_left L c)
end YM.CF.BProof.Extension
