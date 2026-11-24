import YM.Gauge.Chart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Local nearest-point test for use in eq:B-mood. The local parameter need not be onto. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Filter Function ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
lemma strict_lower {f : E→ F} {x : E} {u : E →L[ℝ] F} (h : HasStrictFDerivAt f u x) (p : Injective u) :
    ∃ C : ℝ, 0<C ∧ ∃ s∈𝓝 x, ∀ a∈s,∀ b∈s, dist a b ≤ C * dist (f a) (f b) := by
  obtain ⟨K,p,L⟩:= u.toLinearMap.injective_iff_antilipschitz.mp p; have hp : 0<(K:ℝ):= by exact_mod_cast p
  obtain ⟨s,o,v,R⟩:= exists_nhds_square (h.isLittleO.def (show 0 < (2*(K:ℝ))⁻¹ from by positivity)); refine ⟨2*K,by positivity,s,o.mem_nhds v, fun a ha b hb=> ?_⟩
  have he:‖f a-f b-(u a-u b)‖ ≤ (2*(K:ℝ))⁻¹ * ‖a-b‖ := (map_sub u a b) ▸ R (Set.mk_mem_prod ha hb)
  have hy := L.le_mul_dist a b; change dist a b ≤ (K:ℝ)* dist (u a) (u b) at hy
  have hl : ‖u a-u b‖ ≤ ‖f a-f b‖+(2*(K:ℝ))⁻¹ * ‖a-b‖:= by
    rw [norm_sub_rev (f a-f b)] at he; refine le_trans ?_ (add_le_add_right he (‖f a-f b‖)); simpa only [sub_zero, add_comm] using norm_sub_le_norm_sub_add_norm_sub (u a-u b) (f a-f b) 0
  rw [dist_eq_norm, dist_eq_norm] at hy ⊢; replace hy:=hy.trans (mul_le_mul_of_nonneg_left hl hp.le); field_simp at hy; linarith
end
section regular
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma unique_stationary {f : E→F} (h : ContDiff ℝ ω f) (p : Injective (fderiv ℝ f 0)) :
    ∃ U ∈ 𝓝 (f 0), ∃ W ∈ 𝓝 (0:E), ∀ u∈U, ∀ a∈W, ∀ b∈W,
      IsLocalMin (fun x=> dist (f x) u) a → IsLocalMin (fun x=> dist (f x) u) b → a=b := by
  let X : F × E := (f 0,0)
  let l := fun x : F × E => f x.2 - x.1
  let M := fderiv ℝ f
  let g := fun x : F × E=> (innerSL ℝ (l x)).comp (M x.2)
  let G := fun x : F × E=> (x.1,g x)
  -- apply strict_lower to the first-order test (includes the target variable)
  have hl : ContDiff ℝ ω l:= (h.comp contDiff_snd).sub contDiff_fst
  have e : ContDiff ℝ ω (fun x : F × E=> M x.2):= (h.fderiv_right (by simp)).comp contDiff_snd
  -- innerSL real CLM
  have he : ContDiff ℝ ω G:= contDiff_fst.prodMk (((show F →L[ℝ] F →L[ℝ] ℝ from innerSL ℝ).contDiff.comp hl).clm_comp e)
  let D:=fderiv ℝ G X; have d := he.hasStrictFDerivAt (x:=X) (by simp)
  have hX : Injective D:= by
    apply (LinearMap.ker_eq_bot.mp ?_ : Injective D.toLinearMap)
    rw [LinearMap.ker_eq_bot']; rintro ⟨a,b⟩ w
    let Y := M 0
    let T := ContinuousLinearMap.fst ℝ F E; let R := ContinuousLinearMap.snd ℝ F E; let J : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
    have ha : HasFDerivAt (fun x=> f x.2) (Y.comp R) X:= (h.differentiable (by simp) X.2).hasFDerivAt.comp _ hasFDerivAt_snd
    have hx : HasFDerivAt l (Y.comp R-T) X:= ha.sub hasFDerivAt_fst
    have hg:= (J.hasFDerivAt.comp X hx).clm_comp ((e.differentiable (by simp) X).hasFDerivAt)
    change D (a,b)=0 at w
    have hh:= (d.hasFDerivAt.unique (hasFDerivAt_fst.prodMk (f₂:=g) hg))
    unfold D at w; rw [hh] at w; have hF:a=0:=congrArg Prod.fst w; subst a
    have hp:=congrArg (fun x : F × (E →L[ℝ] ℝ)=> x.2 b) w
    simp [T,R,X,l,J,Y] at hp
    have he : Y b=0:= (inner_self_eq_zero (𝕜:=ℝ)).mp hp
    exact Prod.ext rfl (show b=0 from p (he.trans (map_zero Y).symm))
  have vanish (u : F) (a : E) (p : IsLocalMin (fun x=> dist (f x) u) a) : g (u,a)=0:=by
    have hp : IsLocalMin (fun x=> ‖f x-u‖^2) a:= by
      apply Filter.Eventually.mono p; intro x t
      simp only [dist_eq_norm] at t; exact pow_le_pow_left₀ (norm_nonneg _) t 2
    have hy : HasFDerivAt (fun x=> f x-u) (M a) a:= by convert ((h.differentiable (by simp) a).hasFDerivAt.sub_const u) using 1
    have ht := hy.norm_sq
    have he : (2:ℕ) • (g (u,a))=0:= ht.fderiv.symm.trans hp.fderiv_eq_zero
    rw [← Nat.cast_smul_eq_nsmul ℝ] at he; exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  obtain ⟨C,p,W,t,e'⟩:= strict_lower d hX; rw [nhds_prod_eq,mem_prod_iff] at t; obtain ⟨U,h,W',r,H⟩:=t
  refine ⟨U,h,W',r,fun u m a k b j x y=>?_⟩; have ht:=e' (u,a) (H (Set.mk_mem_prod m k)) (u,b) (H (Set.mk_mem_prod m j)); unfold G at ht; rw [vanish u a x,vanish u b y,dist_self,mul_zero] at ht; exact congrArg Prod.snd (dist_le_zero.mp ht)
end regular
end YM.CF.BPress
