import YM.SU5.Voyager.Embers
import Acacia.Crema
import Acacia.Hike
import HectorA.InShift
import Acacia.Rill
import Acacia.Smith
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace Acacia
open Filter Function Finset Set YM.OS YM Yoland
open scoped Topology NNReal BigOperators Classical InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal
-- station rotated heat at t₁>0 inside: small fixed radius d e.g. derivative cost bound norm.Qt continuous.Need only small d.
variable{H:Hilbert}{a:Axis}(S:OS.Semigroup H a){t:ℝ}
lemma disques (p:0<t):∃ d C:ℝ,0<d∧d<t∧0<C∧DifferentiableOn ℂ (fun z:ℂ=>S.F (t+z)) (Metric.closedBall 0 d)∧∀ z∈ Metric.closedBall (0:ℂ) d, ‖S.F (t+z)‖≤C:=by
 let G(z:ℂ):=S.F (t+z)
 have h : AnalyticAt ℂ G 0:= (show AnalyticAt ℂ S.F ((t:ℂ)+0) from (by rw [add_zero]; exact S.localHeat _ (show 0<(t:ℂ).re from p))).comp (f:=fun z:ℂ=>t+z) (analyticAt_const.add analyticAt_id)
 let c:=‖G 0‖+1; obtain ⟨ε,x,y⟩:=Metric.mem_nhds_iff.mp (h.continuousAt.norm.tendsto.eventually (ge_mem_nhds (lt_add_one ‖G 0‖)))
 let d:= min ε t/2; have hd:0<d:=half_pos (lt_min x p); have he:d<ε:=(half_lt_self (lt_min x p)).trans_le (min_le_left ..); have hg:d<t:=(half_lt_self (lt_min x p)).trans_le (min_le_right ..)
 refine ⟨d,c,hd,hg,add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun z u=>?_,fun z u=> y (Metric.closedBall_subset_ball he u)⟩
 have hv:0<(t+z:ℂ).re:=by rw [Complex.add_re,Complex.ofReal_re]; have hz:= Metric.mem_closedBall.mp u; have hr:=Complex.abs_re_le_norm z; rw [dist_zero_right] at hz; linarith [neg_le_of_abs_le hr]
 exact (((S.localHeat _ hv).comp (f:=fun z:ℂ=>t+z) (analyticAt_const.add analyticAt_id)).differentiableAt).differentiableWithinAt
-- 2 views at point. coord s sp along and t orthogonal. No structure on space motion except contract. function f(b,t). Use first-offset sphere independent of second-all incl forward hops. second offsets small (> -t).
variable{V:Hilbert}{v:Axis}(T:OS.Semigroup V v)
lemma hall (q:ℝ)(h₀:0<q)(f:ℝ→ℝ→ℂ)(X:ℝ→H.Op)(Y:ℝ→V.Op)(a₁ b₁:H)(a₂ b₂:V)(t u:ℝ)(ht:0<t)(hu:0<u)(hX:∀ r, ‖X r‖≤1)(hY:∀ r,‖Y r‖≤1)
 (h₁:∀ r s:ℝ,|r|≤q → -q<s→ f r s= inner ℂ a₁ (X s (dawn S (t+r) b₁)))
 (h₂:∀ r s:ℝ,|r|≤q → -q<s→ f r s= inner ℂ a₂ (Y r (dawn T (u+s) b₂))) (n:ℕ): AnalyticAt ℝ (fun r:ℝ=> iteratedDeriv n (f r) 0) 0:=by
 obtain ⟨d,C,h,g,h',c,c'⟩:=disques S ht
 let Φ(z:ℂ)(s:ℝ):ℂ:= inner ℂ a₁ (X s (S.F ((t:ℂ)+z) b₁))
 let A(i:ℕ)(z:ℂ):= delta (hop i) n (Φ z) 0; let k:= min d q; have hk:0<k:=lt_min h h₀; have hq:k≤q:=min_le_right ..; have hd:k≤d:=min_le_left ..
 let K:=Metric.closedBall (0:ℂ) d; let B:= Metric.closedBall (0:ℂ) k
 have he:B ⊆ K:=Metric.closedBall_subset_closedBall hd
 have hf (s:ℝ):DifferentiableOn ℂ (fun z:ℂ=>Φ z s) B:=by
    let L:= (innerSL ℂ a₁).comp ((X s).comp (ContinuousLinearMap.apply ℂ H.space b₁)); exact ((L.differentiable.comp_differentiableOn c).mono he)
 let r':=1+ (‖a₁‖*‖b₁‖)*C; have hr:0<r':=add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
 have hx(z:ℂ)(p:z∈B)(s:ℝ): ‖Φ z s‖≤r':= (contract_paid a₁ b₁ (X s) _ (hX _)).trans ((mul_le_mul_of_nonneg_left (c' _ (he p)) (by positivity)).trans (le_add_of_nonneg_left zero_le_one))
 obtain ⟨v,hv,l⟩:=signedE r' hr n
 apply Caino.golden_arc hk (by norm_num:0<(3/4:ℝ)) (by norm_num:(3/4:ℝ)<1) hv A
 · filter_upwards [eventually_gt_atTop 0] with i ht; exact ⟨growthU Φ n (hop i) (fun j _=>hf _),fun z p=>(delta_price (hop_pos _) n _ r' (fun j _=>hx z p _)).trans (l i ht)⟩
 obtain ⟨J,m,Hq⟩:=cuppa T n a₂ b₂ u hu hop hop_pos hop_tends
 filter_upwards [diffEra J m,Hq] with i e q₂; intro r h
 have hR:|r|≤k:=by simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] using h
 have hQ:|r| ≤ q:=hR.trans hq
 have hx(r':ℝ)(q':0 ≤ r'):Φ r r'=f r r':=by
    rw [h₁ r r' hQ (lt_of_lt_of_le (neg_lt_zero.mpr h₀) q')]; have u0:0<t+r:=by have v':= (abs_le.mp hR).1; linarith [hd]
    apply congrArg (fun x:H.Op=> inner ℂ a₁ (X r' (x b₁))); unfold dawn
    rw [← S.roots_heat (Real.toNNReal_pos.mpr u0)]
    apply congrArg S.F; unfold OS.Semigroup.duration; rw [Real.coe_toNNReal _ u0.le, Complex.ofReal_add]
 let f'(s:ℝ):=inner ℂ a₂ (Y r (dawn T (u+s) b₂))
 have hz(s:ℝ)(hs:0 ≤ s):Φ r s=f' s:=(hx s hs).trans (h₂ r s hQ ((neg_lt_zero.mpr h₀).trans_le hs))
 have hl:f r=ᶠ[𝓝 0] f':=(lt_mem_nhds (neg_lt_zero.mpr h₀)).mono fun s h=> h₂ r s hQ h -- eventually.mono
 unfold A; rw [delta_conf (g:=f') _ (fun j _=>hz _ (by rw [zero_add]; exact mul_nonneg (Nat.cast_nonneg _) (hop_pos i).le
    )), esteem T _ _ a₂ b₂ (Y r) u hu hl]
 exact (q₂ _ (hY _)).trans ((mul_comm J (hop i)) ▸ e)
#print axioms hall
end Acacia
