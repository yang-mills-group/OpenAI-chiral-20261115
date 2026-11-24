import Mathlib
set_option autoImplicit false
noncomputable section
namespace Zippy
open Function Finset Filter Submodule
open scoped Topology BigOperators InnerProductSpace Classical
variable {Y Z D:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedAddCommGroup Z][NormedSpace ℂ Z]
variable (F:ℕ→Y→L[ℂ]Z)
-- finite.domain composition with sequence bounded
lemma elevator (C:ℝ)(hc:0≤ C)(p:∀i,‖F i‖≤C) (h:∀ x:Y,Tendsto (fun d=>F d x) atTop (𝓝 0)) (K:Submodule ℂ Y)[q:FiniteDimensional ℂ K] (a:ℝ)(hv:0<a): ∀ᶠ d:ℕ in atTop,∀ x∈K, ‖F d x‖ ≤ a*‖x‖:=by
 have := ProperSpace.isCompact_closedBall (0:K) 1
 by_contra w; push Not at w
 obtain ⟨f,u,hp⟩:= extraction_of_frequently_atTop w
 choose z t hx using hp
 have e(i):0<‖z i‖:=by
   contrapose! hx
   refine ⟨i,?_⟩; simp [norm_le_zero_iff.mp hx,map_zero,norm_zero,mul_zero]
 let Z'(d:ℕ):K:= ⟨(‖z d‖⁻¹:ℂ) • z d, Submodule.smul_mem _ _ (t d)⟩
 have he(d): ‖Z' d‖=1:=by change ‖(‖z d‖⁻¹:ℂ) • z d‖=1; rw [norm_smul,norm_inv, Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (e d).ne']
 obtain ⟨x,hx',s,g,w⟩:=this.isSeqCompact (x:=Z') (fun n=>by rw [Metric.mem_closedBall, dist_zero_right,he])
 have ht:Tendsto (fun d=> (Z' (s d)).val-x.val) atTop (𝓝 0):=by have hp:= ((continuous_subtype_val (p:=fun x:Y=>x∈K)).continuousAt.tendsto.comp w).sub_const x.val; rw [sub_self] at hp; exact hp
 have hL:Tendsto (fun d=> F (f (s d)) (Z' (s d)).val - F (f (s d)) x.val) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; have hr:Tendsto (fun d=> C*‖(Z' (s d)).val-x.val‖) atTop (𝓝 0):=by simpa only [norm_zero,mul_zero] using ht.norm.const_mul C
    refine squeeze_zero (fun _=> norm_nonneg _) (fun d=>?_) hr; rw [← map_sub]; exact ((F _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (p _) (norm_nonneg _))
 have U:= (h x.val).comp ((u.comp g).tendsto_atTop)
 have hw:= (hL.add U).norm; simp only [sub_add_cancel,Function.comp_def, add_zero,norm_zero] at hw
 obtain ⟨i,v⟩:= (hw.eventually (ge_mem_nhds hv)).exists; change ‖F (f (s i)) ((‖z (s i)‖⁻¹:ℂ) • z (s i))‖ ≤ _ at v
 rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _), inv_mul_le_iff₀ (e _)] at v
 linarith [hx (s i)]
#print axioms elevator
end Zippy
