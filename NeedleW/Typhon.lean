import HectorA.Iota
import Mathlib.Analysis.Analytic.Uniqueness
set_option autoImplicit false
noncomputable section
namespace NeedleW
open Filter Function Metric NormedSpace MeasureTheory Set YM.OS YM Yoland
open scoped Topology NNReal BigOperators Classical InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
variable (f:ℝ→H)(p:AnalyticOnNhd ℝ f (Ioi 0))
variable(h:∀ n:ℕ,AntitoneOn (fun t:ℝ=> ‖iteratedDeriv n f t‖) (Ioi 0))(u:Tendsto (fun t=>‖f t‖) (𝓝[>] 0) atTop)
include p h u
lemma rises :∀ n:ℕ,Tendsto (fun t=> ‖iteratedDeriv n f t‖) (𝓝[>] 0) atTop:=by
 intro n
 induction n with
 | zero=> simp_rw [iteratedDeriv_zero]; exact u
 | succ n ih=>
    let V:=iteratedDeriv n f; let dn:= fun t:ℝ=> ‖iteratedDeriv (n+1) f t‖
    have hv:AnalyticOnNhd ℝ V (Ioi 0):= fun t h=> aoe p n h
    apply Filter.tendsto_atTop.2; intro C
    suffices ∃ v∈Ioi (0:ℝ),C< dn v by
       obtain ⟨v,g,b⟩:=this
       have he:∀ᶠ i:ℝ in 𝓝[>] 0, 0 < i ∧ i ≤ v:= (show ∀ᶠ i in (𝓝[>] (0:ℝ)), 0 < i from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds g))
       exact he.mono fun i ⟨e,t⟩=>b.le.trans (h (n+1) e g t)
    by_contra! he
    -- V Lipschitz on positive half
    have hL{z:ℝ}(t:0<z) : ‖V z - V 1‖ ≤ C * ‖z-1‖:= Convex.norm_image_sub_le_of_norm_deriv_le (fun t↦fun k:t∈ Ioi (0:ℝ)=> (hv t k).differentiableAt)
     (fun t k=>by have ht:= he t k; simpa only [dn,iteratedDeriv_succ] using ht) (convex_Ioi _) (show (1:ℝ)∈ Ioi 0 from Set.mem_Ioi.mpr (show 0<(1:ℝ) from zero_lt_one)) t
    obtain ⟨t,t0,e0,h0⟩:= ((ih.eventually (eventually_ge_atTop (|C|+‖V 1‖+1))).and ((show ∀ᶠ i in (𝓝[>] (0:ℝ)), 0 < i from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)))).exists
    have he:=hL e0
    have hy:=norm_sub_norm_le (V t) (V 1)
    have hD:‖t-1‖≤ (1:ℝ):=by rw [Real.norm_eq_abs,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr h0)]; exact sub_le_self _ (show 0 ≤ t from (e0:0<t).le)
    have hE:C*‖t-1‖ ≤ |C| *1:=mul_le_mul (le_abs_self _) hD (norm_nonneg _) (abs_nonneg _)
    change |C|+‖V 1‖+1 ≤ ‖V t‖ at t0; linarith only [he,hy,hE,t0]
-- norm self inner analytic
abbrev kernel(n:ℕ)(t:ℝ):ℝ:= ‖iteratedDeriv n f (t/2)‖^2
omit h u
lemma normalL(n:ℕ): AnalyticOnNhd ℝ (kernel f n) (Ioi 0):=by
 intro t v
 let V:=iteratedDeriv n f; let y:=fun t:ℝ=> V (t/2)
 have ht:AnalyticAt ℝ V (t/2):= aoe p n (half_pos v)
 have hp: AnalyticAt ℝ y t:= (show AnalyticAt ℝ V ((fun x:ℝ=>x/2) t) from ht).comp (f:=fun x:ℝ=>x/2) (analyticAt_id.div_const (c:=(2:ℝ)))
 let g:= innerSL ℝ (E:=(H).space)
 have hr:AnalyticAt ℝ (fun t:ℝ=> inner ℝ (y t) (y t)) t:= by
    exact (g.analyticAt_bilinear _).comp (hp.prod hp)
 have hx(t:ℝ): inner ℝ (y t) (y t)=‖y t‖^2:= real_inner_self_eq_norm_sq _
 rw [show kernel f n=(fun t:ℝ=> inner ℝ (y t) (y t)) from (funext fun t=> (hx t).symm)]; exact hr
include h u
lemma tollJ(n:ℕ): Tendsto (kernel f n) (𝓝[>] 0) atTop:=by
 let r(t:ℝ):=t/2
 have hx: Tendsto r (𝓝[>] 0) (𝓝[>] 0):=by
    apply tendsto_nhdsWithin_iff.mpr; constructor
    · have h':Continuous r:= continuous_id.div_const _
      have hx:Tendsto r (𝓝 (0:ℝ)) (𝓝 (r 0)):=h'.continuousAt; simpa only [show r 0=(0:ℝ) from zero_div _] using hx.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
    exact (show ∀ᶠ i in (𝓝[>] (0:ℝ)), 0 < i from self_mem_nhdsWithin).mono (fun x hx=> show (0:ℝ)<x/2 from half_pos hx)
 exact (tendsto_pow_atTop (α:=ℝ) (n:=2) (Nat.succ_ne_zero 1)).comp ((rises f p h u n).comp hx)
lemma not_analytic_bounded(n:ℕ)(g:ℝ→ℝ)(v:AnalyticOnNhd ℝ g (Ioi 0))(b:ℝ)(w:∀ t:ℝ,0<t→‖g t‖ ≤ b)(t₀:ℝ):∃ t:ℝ,t₀<t ∧ 0<t ∧ g t ≠ kernel f n t:=by
 by_contra! he
 let t:=max t₀ 0 + 1
 have ht:max t₀ 0 < t:=lt_add_one _
 have hz:0<t:=(le_max_right ..).trans_lt ht
 have h': g =ᶠ[𝓝 t] kernel f n:= (lt_mem_nhds ht).mono fun x p=>he x (lt_of_le_of_lt (le_max_left ..) p) (lt_of_le_of_lt (le_max_right ..) p)
 have hn : EqOn g (kernel f n) (Ioi 0):= v.eqOn_of_preconnected_of_eventuallyEq (normalL f p n) isPreconnected_Ioi hz h'
 obtain ⟨x,vx,u⟩:= ((show ∀ᶠ i in (𝓝[>] (0:ℝ)), 0 < i from self_mem_nhdsWithin).and ((tollJ f p h u n).eventually (eventually_gt_atTop b))).exists
 have he:= le_of_eq (hn vx).symm; exact not_le.mpr u (he.trans ((le_abs_self _).trans (w x vx)))
#print axioms rises
#check AnalyticAt.div_const
#check InnerProductSpace
#check @aoe
#print axioms not_analytic_bounded
end NeedleW
