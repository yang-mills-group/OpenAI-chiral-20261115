import HectorA.Squeak
import HectorA.Jets
set_option autoImplicit false
noncomputable section
namespace Yoland
open Filter Function Finset Set
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace Classical
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℂ X][CompleteSpace X]
-- real instance use `InnerProductSpace.complexToReal`
#check InnerProductSpace.complexToReal
variable [NormedSpace ℝ X][IsScalarTower ℝ ℂ X][SMulCommClass ℝ ℂ X]
variable (f:ℝ→X)(A:AnalyticOnNhd ℝ f (Set.Ioi 0)) (a: ℝ)
-- translation property on strictly right times
local notation "P" => Ioi (0:ℝ)
variable (C:Civil f)
include C
open Submodule
lemma corpus (K:Submodule ℂ X)(p:FiniteDimensional ℂ K)(t:0<a)(h:∀ n:ℕ,iteratedDeriv n f a∈ K): ∀x∈Ioi (0:ℝ), f x∈K:=by
 let F:= (Submodule.orthogonal K).starProjection; let L:= F.restrictScalars ℝ
 let g:= L ∘ f
 have he : AnalyticOnNhd ℝ g P:=fun x h=> (L.analyticAt _).comp (C.price _ h)
 have hg : g =ᶠ[𝓝 a] 0:= by
    apply garage (he _ t)
    intro n; unfold g; rw [transport (C.price a t)]
    -- use min projection K or explicit
    change F (iteratedDeriv n f a)=0
    exact Submodule.starProjection_orthogonal_apply_eq_zero (K:=K) (h n)
 have hu:= he.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_Ioi) t hg
 intro x px; have hl:F (f x)=0:=hu px
 rw [show F=(Submodule.orthogonal K).starProjection from rfl, Submodule.starProjection_orthogonal,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,sub_eq_zero] at hl; exact K.starProjection_eq_self_iff.mp hl.symm
lemma animosity(k:ℕ)(c:ℕ→ℂ)(hc:c k ≠0)(ha:0<a)(h:(∑ i∈Finset.range (k+1), c i • iteratedDeriv i f a)=0):
 ∃ T:Submodule ℂ X,FiniteDimensional ℂ T ∧ ∀ x∈Ioi (0:ℝ), f x∈T:=by
 let T:= Submodule.span ℂ ((fun i=>iteratedDeriv i f (a+1)) '' {n:ℕ|n<k})
 have i:FiniteDimensional ℂ T:=FiniteDimensional.span_of_finite ℂ ((Set.finite_lt_nat _).image _)
 exact ⟨T,i,corpus f (a+1) C T i (by positivity) (liable f a C k c hc ha h)⟩
lemma package {n:ℕ}(ha:0<a)(h: ¬ LinearIndependent ℂ (fun i:Fin n=> iteratedDeriv (i.val+1) f a)):
 ∃ T:Submodule ℂ X,FiniteDimensional ℂ T ∧ ∀ x∈Ioi (0:ℝ), f x∈ T:=by
 obtain ⟨g,he,i,hy⟩:=Fintype.not_linearIndependent_iff.mp h
 -- reindex univ Fin (n params) trailing max. Easier iv. Define coef f
 let S:Finset (Fin n):= Finset.univ.filter fun i=>g i≠0; have hi:i∈S:=Finset.mem_filter.mpr ⟨Finset.mem_univ i,hy⟩
 let p:=S.max' ⟨i,hi⟩; have hp:p∈S:=Finset.max'_mem _ _
 let k:=p.val+1
 let e(i:Fin n):=i.val+1
 let c(j:ℕ):ℂ:=if h:j ∈ S.image e then g ⟨j-1,by obtain ⟨x,v,H⟩:=Finset.mem_image.mp h; rw [←H]; unfold e; simp⟩ else 0
 have hc(i:Fin n)(hi:i∈S): c (e i)=g i:=by unfold c; rw [dif_pos (Finset.mem_image_of_mem _ hi)]; congr
 apply animosity f a C k c (show c k ≠ 0 from (hc p hp).symm ▸ (Finset.mem_filter.mp hp).2) ha
 rw [← sum_subset (s₁:= S.image e) _ _]
 swap; · rintro j hj; obtain ⟨v,b,rfl⟩:=Finset.mem_image.mp hj; rw [Finset.mem_range]; have he: v≤p:= Finset.le_max' _ _ b; change v.val≤ p.val at he; unfold e k; omega
 swap; · intro i _ u; simp only [c,dif_neg u,zero_smul]
 rw [Finset.sum_image (by intro i _ j _ hv; apply Fin.ext; unfold e at hv; omega)] -- weird. use h'
 rw [← Finset.sum_subset (f:=fun i:Fin n=> g i • iteratedDeriv ((i:ℕ)+1) f a) (s₁:=S) (Finset.subset_univ S) ?_] at he
 swap; · intro j _ hj; rw [show g j=0 from not_not.mp fun e=>hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,e⟩),zero_smul]
 refine (Finset.sum_congr rfl (fun i hi=>?_)).trans he; rw [hc i hi]
#print axioms animosity
#check Finset.sum_subset
#check finite_lt_nat
end Yoland
