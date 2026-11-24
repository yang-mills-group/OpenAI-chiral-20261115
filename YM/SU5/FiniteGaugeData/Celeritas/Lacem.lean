import YM.SU5.FiniteGaugeData.Celeritas.Credenza
import YM.SU5.FiniteGaugeData.Mist.Leda
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
set_option quotPrecheck false
variable {H V:Hilbert}{a b:Axis}(S:OS.Semigroup H a)(T:OS.Semigroup V b)
-- complex semigroup continuity in SOT even at boundary; real axis all. clipping.
def Veil(z:ℂ):H.Op:= S.edge (-z.im)* S.E (Real.toNNReal z.re)
lemma voile (z:ℂ)(t:0< z.re): Veil S z=S.F z:=by
 let v:=z.re.toNNReal; unfold Veil; rw [← S.roots_heat (Real.toNNReal_pos.mpr t)]; apply Eq.trans (S.along (dur.mpr (Real.toNNReal_pos.mpr t)) _) ?_; refine congrArg _ (Complex.ext ?_ ?_)<;> simp [OS.Semigroup.duration,t.le,sideways]
lemma veil_analytic {z:ℂ}(p:z∈OS.Semigroup.inside) : AnalyticAt ℂ (Veil S) z := by
 refine (S.localHeat _ p).congr ?_; filter_upwards [(continuous_re.tendsto z).eventually (Ioi_mem_nhds (show 0<z.re from p))] with z t; exact (voile S z t).symm
lemma veil_real (t:ℝ): Veil S (t:ℂ)=S.E t.toNNReal := by unfold Veil; rw [ofReal_im,neg_zero,S.birth,ofReal_re]; rfl
lemma veil_repr (u:ℝ≥0)(t:ℝ): Veil S ((u:ℝ)+sideways t)=S.edge t*S.E u:=by unfold Veil; simp only [add_im, ofReal_im, add_re, ofReal_re, side, Real.toNNReal_coe, add_zero,zero_add]; unfold sideways; simp
lemma veil_C {X: Type*} [TopologicalSpace X] (f:X→ ℂ) (A:X→H)(p:Continuous f)(t: Continuous A): Continuous (fun x=> Veil S (f x) (A x)):=by
 apply cont_edge S _ _ _ (show Continuous (fun t=>-(f t).im) from (continuous_im.comp p).neg); exact Mist.Leda.steamV S _ _ (continuous_real_toNNReal.comp (continuous_re.comp p)) t -- import.Hike maybe?
-- domain sleeve
variable (d L:ℝ)
abbrev chamber : Set ℂ:= {z:ℂ| 0 < z.re ∧ z.re < d ∧ |z.im| < L}
private lemma chamber_pos (d0:0<d)(v:0<L): ∀ r:ℝ,0 < r → r <d→(r:ℂ)∈ chamber d L:=fun i x z=>by simp [chamber,x,z,v]
lemma chamber_conv : Convex ℝ (chamber d L):=(show Convex ℝ ({z:ℂ|0<z.re} ∩ ({z:ℂ|z.re<d} ∩ lanes L)) from Convex.inter (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0) (Convex.inter (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear d) (lane_v L)))
private lemma born (y:ℝ) (v:0<L)(p:0<d)(s:|y|<L): sideways y ∈ closure (chamber d L):=by
 let f(x:ℝ):= (x:ℂ)+sideways y
 have ht:Continuous f:=continuous_ofReal.add continuous_const; apply mem_closure_of_tendsto ((ht.tendsto' 0 (sideways y) (by simp [f])).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))); -- nebot interval
 filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (gt_mem_nhds p)] with z hz t; change f z∈ chamber d L; simp [f,sideways,chamber,s,show 0<z from hz,show z<d from t] -- hz.2 may ≤ not <. use Ioo
-- `Chart analyt` common contour
lemma veil_set {f g:ℂ→ℂ}(v:0<d)(t:0<L)(F:AnalyticOnNhd ℂ f (chamber d L))(H: AnalyticOnNhd ℂ g (chamber d L))(p:∀ x:ℝ,0<x→x<d→f x=g x): Set.EqOn f g (chamber d L):= by
 let z:= d/2; have he:0<z:=half_pos v; have hz:z<d:=half_lt_self v; refine F.eqOn_of_preconnected_of_frequently_eq H (chamber_conv d L |>.isPreconnected) (chamber_pos d L v t z he hz) ?_; intro hf
 have hv:Tendsto ((↑):ℝ→ℂ) (𝓝[>] z) (𝓝[≠] (z:ℂ)):=by apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ continuous_ofReal.continuousAt.continuousWithinAt; filter_upwards [self_mem_nhdsWithin] with r q; exact fun t=> (mem_Ioi.mp q).ne' (ofReal_injective (show (r:ℂ)=(z:ℂ) from t))
 obtain ⟨i,h,r,w⟩:= ((hv.eventually hf).and ((show ∀ᶠ y in 𝓝[>] z,z<y from self_mem_nhdsWithin).and (nhdsWithin_le_nhds (gt_mem_nhds hz)))).exists; exact h (p i (he.trans r) w)
lemma tariff_bridge {f g:ℂ→ℂ}{d L:ℝ}(v:0<d)(t:0<L)(F:AnalyticOnNhd ℂ f (chamber d L))(H:AnalyticOnNhd ℂ g (lanes L))(u: Continuous f)(p:∀ x:ℝ,0<x→x<d→ f x=g x)(y:ℝ)(q:|y|<L): f (sideways y)=g (sideways y):=by
 let z:=sideways y; have hp:z∈lanes L:=by unfold lanes z sideways; simpa
 have hc:ContinuousAt g z:=(H z hp).continuousAt; have he:EqOn f g (chamber d L):= veil_set d L v t F (fun x k=> H x k.2.2) p; haveI h:(𝓝[chamber d L] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (born d L y t v q); exact tendsto_nhds_unique_of_eventuallyEq (u.continuousAt.continuousWithinAt (x:=z) (s:=chamber d L)) (ContinuousAt.continuousWithinAt hc) ((show ∀ᶠ i in 𝓝[chamber d L] z,i∈ chamber d L from self_mem_nhdsWithin).mono fun u v=>he v)
#print axioms tariff_bridge
-- four point local commutation payment. d set fixed one, clearance L.B perspective. 
variable (A B:H.Op)(x y:H)(Z:V.Op)(w:V →L[ℂ] ℂ)(p:V)(s r:ℝ≥0)(v:OS.Cross b)
/- w captures all prefix L & A etc before b-gap from A into TAG_B; then GapB→Z (B mov)→next spacer →p(inner all). -/
abbrev sideB(t:ℝ) :ℂ:= w (T.E s (T.U (t • v) (Z (T.U (-t • v) (T.E r p)))))
abbrev heat_A (z:ℂ) :ℂ:= inner ℂ x (S.E 1 (A (Veil S z (B (Veil S (1-z) y)))))
abbrev heat_B (z:ℂ) :ℂ:= inner ℂ x (Veil S (1-z) (B (Veil S z (A (S.E 1 y))))) -- branch z positive applied y moves earlier z
variable (Q:Cinema T)(hv:‖v‖≤1)(hs:L ≤ s)(hp:L≤r)(ht:0<L)
local notation "G" u:max=> cup T u Q v hv
local notation "φ"=> sideB T Z w p s r v
local notation "Ψ"=> heat_A S A B x y
local notation "ν"=> heat_B S A B x y
variable (fP:∀ t:ℝ,0<t→t<1→ sideB T Z w p s r v t=heat_A S A B x y (↑t))(fM:∀ t:ℝ,0<t→t<1→ sideB T Z w p s r v (-t)=heat_B S A B x y (↑t))
local notation "I₁" => (ContinuousLinearMap.apply ℂ V.space p)
include Q hv hs hp ht fP fM
lemma torrent (t:ℝ)(u:|t|<L) : inner ℂ (S.E 1 x) (A (S.edge t (B (S.edge (-t) (S.E 1 y))))) = inner ℂ (S.E 1 x) (S.edge t (B (S.edge (-t) (A (S.E 1 y))))):=by
 let f(z:ℂ):= w (((G s) z * Z * (G r) (-z)) p); have hF(i:ℂ)(q:i∈lanes L): AnalyticAt ℂ f i:= by
    let X:= (cup_A T v s Q hv i (show |i.im|<s from lt_of_lt_of_le q hs)); have hx:= (cup_A T v r Q hv (-i) (by rw [lanes, Set.mem_setOf,neg_im,abs_neg]; exact lt_of_lt_of_le q hp)); exact w.analyticAt _ |>.comp ((I₁).analyticAt _ |>.comp ((X.mul analyticAt_const).mul (hx.comp analyticAt_id.neg))) -- signature
 have he(c:ℝ): f (↑c)=φ c:= by
    have hz:(G s) c= T.E s * T.U (c • v):= (credit_h T v s c Q hv (show 0<s from (show (0:ℝ)<s from ht.trans_le hs))).trans (T.independent ..).symm; have hs':(G r) (-(c:ℂ))=T.U (-c • v)* T.E r:= (ofReal_neg c) ▸ credit_h T v r (-c) Q hv (show 0<r from (show (0:ℝ)<r from ht.trans_le hp)); unfold f; rw [hz,hs']; rfl
 have hx(z)(h:z∈chamber 1 L): AnalyticAt ℂ (Veil S) z ∧ AnalyticAt ℂ (fun i=> Veil S (1-i)) z:=by
    refine ⟨veil_analytic S h.1,(veil_analytic S ?_).comp (analyticAt_const.sub analyticAt_id)⟩; change 0<(1-z).re; rw [sub_re,one_re]; exact sub_pos.mpr h.2.1
 have hO(z)(Z' : z∈ chamber 1 L): AnalyticAt ℂ Ψ z:= by
    let L:= (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H.space y)); let A'(z:ℂ):= S.E 1*A*Veil S z * B * Veil S (1-z); change AnalyticAt ℂ (L ∘ A') z; exact L.analyticAt _|>.comp (show AnalyticAt ℂ A' z from ((analyticAt_const.mul (hx z Z').1).mul analyticAt_const).mul (hx z Z').2)
 have hQ(z)(Z': z∈ chamber 1 L):AnalyticAt ℂ ν z:= by
    let L:= (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H.space (A (S.E 1 y)))); let A' (z:ℂ):= Veil S (1-z) * B * Veil S z; exact L.analyticAt _|>.comp (show AnalyticAt ℂ A' z from ((hx z Z').2.mul analyticAt_const).mul (hx z Z').1)
 have hf: Ψ (sideways t)= f (sideways t):= by
    apply tariff_bridge zero_lt_one ht hO hF ((innerSL ℂ x).continuous.comp ((S.E 1).continuous.comp (A.continuous.comp (veil_C S (fun z:ℂ=>z) (fun z=>B (Veil S (1-z) y)) continuous_id (B.continuous.comp (veil_C S (fun z:ℂ=>1-z) (fun _=>y) (continuous_const.sub continuous_id) continuous_const)))))) _ _ u -- `1-id` invalid.Vi.
    exact fun t v b=>(fP t v b).symm.trans (he t).symm
 have hk:ν (sideways (-t))=f (sideways t):=by
    let f'(z:ℂ):= f (-z); have ht' : ∀ z:ℂ, z∈lanes L→ -z∈ lanes L:= fun i p=>by rw [lanes, Set.mem_setOf,neg_im,abs_neg]; exact p
    have hm:=tariff_bridge zero_lt_one ht hQ (show AnalyticOnNhd ℂ f' _ from fun i z=> (hF (-i) (ht' i z)).comp analyticAt_id.neg) ((innerSL ℂ x).continuous.comp (veil_C S (fun z:ℂ=>1-z) (fun z=>B (Veil S z (A (S.E 1 y)))) (continuous_const.sub continuous_id) (B.continuous.comp (veil_C S (fun z:ℂ=>z) (fun _=> A (S.E 1 y)) continuous_id continuous_const)))) (fun x v z=>by unfold f'; rw [← ofReal_neg,he]; exact (fM x v z).symm) (-t) (by rwa [abs_neg]); exact hm.trans (congrArg f (show -sideways (-t)=sideways t from (by unfold sideways; push_cast; ring)))
 have Hx(t:ℝ): Veil S (sideways t)=S.edge t:=by have r:=veil_repr S 0 t; simp [S.eZero, show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl] at r; exact r
 have Hy(t:ℝ): Veil S (1-sideways t)=S.E 1*S.edge (-t):=by
    have he:Commute (S.edge (-t)) (S.E 1):=by rw [← S.roots_heat zero_lt_one]; exact (S.along (dur.mpr zero_lt_one) (-t)).trans (S.either (dur.mpr zero_lt_one) (-t)).symm
    rw [show 1-sideways t=(↑((↑(1:ℝ≥0)):ℝ):ℂ)+ sideways (-t) from (by unfold sideways; push_cast; ring), veil_repr,he.eq]
 have hy'(t:ℝ): Veil S (1-sideways t)= S.edge (-t)*S.E 1:=by rw [show 1-sideways t=(↑((↑(1:ℝ≥0)):ℝ):ℂ)+ sideways (-t) from (by unfold sideways; push_cast; ring), veil_repr]
 have hh:= hf.trans hk.symm; unfold heat_A heat_B at hh; rw [hy' t, Hy (-t),Hx,Hx,neg_neg] at hh; rw [←ContinuousLinearMap.adjoint_inner_right,S.sym,←ContinuousLinearMap.adjoint_inner_right,S.sym]; exact hh -- nested? explicit spectator.
#print axioms torrent
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
