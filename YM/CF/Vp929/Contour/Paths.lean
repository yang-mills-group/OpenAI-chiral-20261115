import YM.CF.Vp929.Analysis.Wood
import YM.CF.Vp929.Contour.Accounts
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Py.Rate
open Complex VolumeRate Function Set Filter Topology Metric
open scoped ComplexConjugate
structure Thorough(S:Set ℂ) :Prop where
 cover:IsOpen S
 wake : IsPreconnected S
 can:0 ∈ S
 comet : Complex.I∈ S
-- exposes parameters. All equality frames real-linear and uniqueness.
variable {S:Set ℂ}(p:Thorough S)
include p
lemma leg_transfer {f g:ℂ→ℂ}(h:DifferentiableOn ℂ f S)(hg:DifferentiableOn ℂ g S)(b:∀ x:ℝ,(x:ℂ)∈S→ f x=g x): EqOn f g S:= by
 refine (h.analyticOnNhd p.cover).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd p.cover) p.wake p.can ?_
 have t:Tendsto ofReal (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℂ)):= by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_ , (show ∀ᶠ x in 𝓝[≠] (0:ℝ), x ≠0 from self_mem_nhdsWithin).mono (fun x q=>ofReal_ne_zero.mpr q)⟩; simpa only [ContinuousWithinAt,ofReal_zero] using ((continuous_ofReal.continuousAt (x:=(0:ℝ))).continuousWithinAt (s:={(0:ℝ)}ᶜ))
 by_contra k; push Not at k; obtain ⟨x,h,h'⟩:= ((t.eventually k).and (t.eventually (mem_nhdsWithin_of_mem_nhds (p.cover.mem_nhds p.can)))).exists; exact h (b x h')
omit p
lemma LedgeS_star {n:ℕ}{t y:ℝ}{z:ℂ} (hp:z∈ Ledge n t y): star z∈ Ledge n t y:= by change conj z∈_; exact ⟨hp.1,hp.2.1,by rw [conj_im,abs_neg]; exact hp.2.2⟩
lemma sea_convex (n:ℕ)(t y:ℝ): Convex ℝ (Ledge n t y):= by
 let A:=y/2+(widthS n+3)*t; let B:=2*y-(widthS n+3)*t
 rw [show Ledge n t y= (Complex.reLm ⁻¹' Ioo A B) ∩ Complex.imLm ⁻¹' ball (0:ℝ) t from Set.ext fun i=>by simp only [Ledge,mem_setOf_eq, mem_inter_iff,mem_preimage, mem_Ioo,mem_ball_zero_iff,Real.norm_eq_abs]; rw [and_assoc]; rfl]; exact ((convex_Ioo A B).linear_preimage reLm).inter ((convex_ball (0:ℝ) t).linear_preimage imLm)
abbrev fluid (z:ℂ)(w:ℂ) := z.re + (z.im:ℂ) * w
lemma leg (n:ℕ)(t y:ℝ)(z:ℂ)(h:z∈ Ledge n t y) : Thorough ((fluid z) ⁻¹' (Ledge n t y) ∩ ball 0 2):= by
 have u:Continuous (fluid z):= by unfold fluid; fun_prop
 have he: Convex ℝ ((fluid z) ⁻¹' (Ledge n t y)):= by
    intro x u k p a b l j A; apply (?_: fluid z (a • x+b • k)=a • fluid z x+b •fluid z k) |>.symm ▸ (sea_convex n t y u p l j A : _∈Ledge n t y); apply Complex.ext<;>simp [fluid,mul_re,mul_im]<;> nlinarith [show z.re*(a+b)=z.re from by rw [A,mul_one]]
 refine ⟨((ledge_open.preimage u).inter isOpen_ball), (he.inter (convex_ball (0:ℂ) 2)).isPreconnected, ⟨?_,mem_ball_self (by norm_num)⟩, ⟨?_,mem_ball_zero_iff.mpr (by simp)⟩⟩
 · simp only [mem_preimage,fluid,mul_zero,add_zero,Ledge,mem_setOf_eq,ofReal_re,ofReal_im,abs_zero]; exact ⟨h.1,h.2.1,Ledge.pos h⟩
 change fluid z I ∈ Ledge n t y; rw [fluid,re_add_im]; exact h
section
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{f g:ℂ→ Pair X}
include p
lemma Thorough.compare (h:Form S f)(hg:Form S g)(hu:∀ (x:ℝ),(x:ℂ)∈S→ f x=g x): EqOn f g S:= by
 have he (A:X→L[ℝ]ℝ):= leg_transfer p (h A) (hg A) (fun x k=> congrArg _ (hu x k))
 have H(x y:X)(u:∀ A:X→L[ℝ]ℝ,A x=A y): x=y:=by
    obtain ⟨v,p,h⟩:= exists_dual_vector'' ℝ (x-y); change v (x-y)= ‖x-y‖ at h; rw [map_sub,u,sub_self] at h; exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
 intro z t; apply Prod.ext
 · exact H _ _ (fun p=>by simpa only [prob_re] using congrArg re (he p t))
 exact H _ _ (fun p=>by simpa only [prob_im] using congrArg im (he p t))
end
end YM.CF.Py.Rate
