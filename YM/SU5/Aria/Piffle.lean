import YM.SU5.Aria.Troupe
/-! # Implement an LOS (ℝ) reflection as an anti-linear involution. abstract Gram transport. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter Metric Analysis
open scoped Topology InnerProductSpace
variable {H:Hilbert}{I : Type*}(x y:I→H)(s:Dense (Submodule.span ℂ (range x) : Set H))(t:∀ i j,inner ℂ (y i) (y j)=star (inner ℂ (x i) (x j)))
abbrev Muse(H:Hilbert):= H.space→L⋆[ℂ] H.space
local notation "W"=> Finsupp.linearCombination ℂ
local notation "ξ"=> (starLinearEquiv ℂ:ℂ≃ₗ⋆[ℂ] ℂ)
noncomputable def upside : (I→₀ℂ) →ₗ⋆[ℂ]H := (W y).comp (Finsupp.mapRange.linearMap (ξ).toLinearMap)
lemma upside_one(i:I)(b:ℂ): upside y (Finsupp.single i b) = star b • y i:=by
 unfold upside; rw [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single]; rfl
include t
lemma upside_cost (u v:I→₀ℂ): inner ℂ (upside y u) (upside y v)=star (inner ℂ (W x u) (W x v)):=by induction u using Finsupp.induction_linear with
 | zero=> simp
 | add f g i j=> simp [i,j,inner_add_left]
 | single i a=>
   induction v using Finsupp.induction_linear with
   | zero=>simp
   | add b h p q=> simp only [map_add, inner_add_right, p, q,star_add]
   | single j b=> simp only [upside_one,Finsupp.linearCombination_single,inner_smul_left,inner_smul_right, t,star_mul]; -- W maybe parser
                  simp [Complex.star_def]; ring
include s
lemma coupon_witness : ∃ U: Muse H,(∀ i,U (x i)=y i) ∧ (∀ u, ‖U u‖=‖u‖) ∧ (∀ a b:H, inner ℂ (U a) (U b)=star (inner ℂ a b)) := by
 classical
 let F:= W x; let U:=(upside y).extendOfNorm F
 have hu:DenseRange F:= by change Dense (range F); rw [← Finsupp.range_linearCombination] at s; exact s
 have he(z:I→₀ℂ):‖upside y z‖= ‖F z‖:= by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [←@inner_self_eq_norm_sq ℂ H.space,←@inner_self_eq_norm_sq ℂ H.space,upside_cost x y t]; rfl
 have hU(z:I→₀ℂ): U (F z)=upside y z:=LinearMap.extendOfNorm_eq hu ⟨1,fun i=> by rw [he,one_mul]⟩ _
 refine ⟨U,fun i=>?_, fun v=>?_,fun u v=>?_⟩
 · convert hU (Finsupp.single i 1) using 1; simp [F]; simp [upside_one]
 · exact congrFun (hu.equalizer (g:=fun a=>‖U a‖) (h:=fun a=>‖a‖) U.continuous.norm continuous_norm (funext fun z=> (congrArg norm (hU z)).trans (he z))) v
 apply congrFun (hu.equalizer (g:=fun v=> inner ℂ (U u) (U v)) (h:=fun v=> star (inner ℂ u v)) (continuous_const.inner U.continuous) ((continuous_const.inner continuous_id).star) (funext ?_))
 intro i; apply congrFun (hu.equalizer (g:=fun u=> inner ℂ (U u) (U (F i))) (h:=fun u=> star (inner ℂ u (F i))) (U.continuous.inner continuous_const) ((continuous_id.inner continuous_const).star) (funext ?_)); intro j; exact (congrArg₂ (inner ℂ) (hU j) (hU i)).trans (upside_cost x y t j i)
-- if intertwinement on generator only
omit t
lemma starinter (U V: Muse H) (u:∀ i: I, U (x i)=V (x i)): U=V:=by apply ContinuousLinearMap.ext_on s; rintro _ ⟨i,rfl⟩; exact u i
include t in
lemma poetry (f:I→ I)(h: y=x∘f)(b:∀ i,x (f (f i))=x i): ∃ U: Muse H,(∀ i,U (x i)= y i)∧(∀ a:H,U (U a)=a)∧(∀ u, ‖U u‖=‖u‖)∧ (∀ a b:H, inner ℂ (U a) (U b)=star (inner ℂ a b)):= by
 obtain ⟨U,e,h₁,H'⟩:=coupon_witness x y s t; have hx: (U.comp U:H.Op)=ContinuousLinearMap.id ℂ _:=by
   apply ContinuousLinearMap.ext_on s; rintro _ ⟨i,rfl⟩; rw [ContinuousLinearMap.comp_apply,e,h]; change U (x (f i))=_; rw [e,h]; exact b i
 exact ⟨U,e,fun a=>DFunLike.congr_fun hx a,h₁,H'⟩
end YM.CF.Buffered.Afterglow.Tower.Aria
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.poetry
