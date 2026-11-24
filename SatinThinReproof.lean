import SatinFixedContrastNovember4
import YM.SU5.Macro.Edge
import SatinThinJetsForward
/-!
# Testing the analytic positive-H obstruction on the THIN limit

CP16, I: test against making these fields themselves local in a specific sense from
`YM.SU5.Macro.Edge`. Need NO *two-sided* further continuation license,
NO commutation bill in the input. Compare the earlier construction SatinExistence, the earlier construction Horizon tex: attempts at
real-time *gap* and other center-time-offset prices. Our test covers any candidate in
the indicated `OS.Semigroup` sense retaining even just ONE plus-order kernel on just a stripe of
centers at true separation (already nonzero there), with the indicated time shift,
for which one analytic-extension bill works. A **weaker class of no-go** than working
on arbitrary temperate spectral distributions. Measuring kernel as a bona fide
function at interior and requiring both orders as boundary **vectors** there. Not
requesting a test that would include e.g., reconstructing these markings by
smoothing OR recomposing some other field system; not about any particular spin
transformation. For our application to the same probes at all sufficiently late
stencil stages & the limit, read ReproofEnd.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SatinEdge
open Function Filter Set Metric Bornology Complex
open OS.Semigroup SatinJets
open SatinMacro
open scoped Topology InnerProductSpace NNReal ComplexOrder
/- recognition bookkeeping:
argument `2 r + t` is the center-time T. It's AFTER any intrinsic price of the pair.
We test WHATEVER positive time shift with that same interpretation.
-/
variable (u:OS.Cross timeAxis)(p:ℝ→ℂ){H:Hilbert}(S:OS.Semigroup H timeAxis) (A B:H)
def CenterPays (r:ℝ≥0) : Prop := ∀ᶠ t:ℝ in atTop, p (t+(r:ℝ)+(r:ℝ))= SatinMacro.kernel S A B u (t.toNNReal)

def Shows (a:ℝ) : Prop:= AnalyticOnNhd ℝ p (Ioi a) ∧ ∃ z∈ Ioi a, p z≠0

lemma late_receipt {p q:ℝ→ℂ}{a:ℝ}(f:AnalyticOnNhd ℝ p (Ioi a))(g:AnalyticOnNhd ℝ q (Ioi a))(t:p =ᶠ[atTop] q): EqOn p q (Ioi a):=by
 obtain ⟨b,hb⟩:= eventually_atTop.1 t
 obtain ⟨d,f',g'⟩:= exists_gt (max a b)|>.imp (fun d h=> (show a<d∧b<d from ⟨(le_max_left ..).trans_lt h,(le_max_right ..).trans_lt h⟩))
 exact f.eqOn_of_preconnected_of_eventuallyEq g isPreconnected_Ioi f' (by filter_upwards [lt_mem_nhds g'] with i v using (hb i v.le))
lemma traveler (p:ℝ→ℂ)(a:ℝ)(s:Shows p a): ∃ᶠ i:ℝ in atTop,p i≠0:= by
 intro h; obtain ⟨d,u,v⟩:=s.2
 exact v (late_receipt s.1 (analyticOnNhd_const (v:= (0:ℂ))) (h.mono (fun _ h=> not_not.mp h)) u)
lemma unique_accord {H':Hilbert}(S':OS.Semigroup H' timeAxis)(X Y:H'){r:ℝ≥0}
    (P: CenterPays u p S A B r)(Q: CenterPays u p S' X Y r): accord S A B u S' X Y := by
 have h(H:Hilbert)(S:OS.Semigroup H timeAxis)(x y:H): AnalyticOnNhd ℝ (fun t:ℝ=> kernel S x y u (Real.toNNReal t)) (Ioi 0):= by simpa only [add_zero,neg_zero] using real_analytic_shift S x y u 0
 have t:= late_receipt (h H' S' X Y) (h H S A B) ((show (fun t:ℝ=> kernel S' X Y u (t.toNNReal)) =ᶠ[atTop] _ from (Filter.EventuallyEq.symm Q)).trans (show _ =ᶠ[atTop] (fun t:ℝ=> kernel S A B u t.toNNReal) from P))
 refine ⟨1,zero_lt_one,Filter.Eventually.frequently ?_⟩; filter_upwards [(lt_mem_nhds (show (0:ℝ≥0)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds] with i w
 simpa only [Real.toNNReal_coe] using (show kernel S' X Y u (Real.toNNReal (i:ℝ))= _ from t (show (i:ℝ)∈Ioi 0 from w))
lemma kernel_paid_some (r:ℝ≥0)(P:CenterPays u p S A B r)(s:∃ᶠ i:ℝ in atTop,p i≠0): ∃ t:ℝ≥0,kernel S A B u t≠0:= by
 obtain ⟨b,h⟩:= eventually_atTop.1 P
 obtain ⟨z,v,q⟩:= (s.and_eventually (eventually_gt_atTop (b+↑r+↑r))).exists
 let t:ℝ:=z-(r+r:ℝ≥0)
 refine ⟨t.toNNReal,(h t (by unfold t; push_cast; linarith)).symm.trans_ne ?_⟩
 rwa [show t+↑r+↑r = z from (by unfold t; push_cast; ring)]
-- attenuation of PLUS-order high-time cost
lemma falls (g:S.orth B=0): Tendsto (fun t:ℝ=> kernel S A B u t.toNNReal) atTop (𝓝 0):= by
 have h:Tendsto (fun t=> kernel S A B u t) atTop (𝓝 0):= by
    change Tendsto (⇑((innerSL ℂ A).comp (S.U u)) ∘ (fun t=> S.E t B)) atTop _
    simpa only [g,map_zero] using
      (((innerSL ℂ A).comp (S.U u)).continuous.continuousAt.tendsto.comp (S.emerges B))
 exact h.comp Real.tendsto_toNNReal_atTop

/-- Even trying *other* vacuum vectors but wishing to keep **time smoothing**
once one claims a λ=0 continuation runs into this. -/
lemma kill (r:ℝ≥0) (P:CenterPays u p S A B r)(s:∃ᶠ i:ℝ in atTop,p i≠0)
    (t:Tendsto (fun i:ℝ=>p (i+↑r+↑r)) atTop (𝓝 0))(d:HasPadding S B) {x y:ℝ}(q:x<y) (A' B':H):
    ∃ v∈Ioo x y, ¬ swap S.unit (joinST u v) A A' B B' := by
 -- adaptation of Edge.refuses_lower without the ground projection assumption HERE
 by_contra! h
 let f (z:ℂ):= carried S B' A' (-u) (-z)
 obtain ⟨e,v,G,m,v',z⟩:= extends_kernel S A B u d
 have p' : IsBounded (f '' {z:ℂ| z.im < 0}) := by
    rw [isBounded_iff_forall_norm_le]; exact ⟨_,by rintro z ⟨w,_,rfl⟩; exact carried_cost S B' A' (-u) _⟩
 have H':= Glue.rigid_of_edge q v m (G:= (show AnalyticOnNhd ℂ f {z:ℂ| z.im<0} from carried_down S B' A' u)) (((carried_only_time S B' A' (-u)).comp continuous_neg).continuousOn) (v'.subset (image_subset_range ..)) p' (fun i hi=>?_)
 · obtain ⟨w,F,_⟩:=H'; obtain ⟨j,j'⟩:= kernel_paid_some u p S A B r P s
   have eq (a:ℝ≥0): kernel S A B u a=w:= by
      have he : 0 ≤ (SatinMacro.rise a).im := by rw [rise_im]; exact NNReal.zero_le_coe
      exact (carried_rise S A B u a).symm.trans ((z he).trans (F (lt_of_lt_of_le v he)))
   exact j' ((eq j).trans (tendsto_nhds_unique ((tendsto_const_nhds (x:=w) (f:=atTop)).congr (fun x:ℝ => (eq x.toNNReal).symm)) (t.congr' P)))
 unfold f; rw [← z (show 0 ≤ (i:ℂ).im by simp), ← ofReal_neg,carried_edge,carried_edge,← neg_joinST]; exact h i hi
lemma cost_both (t a:ℝ≥0): kernel S (S.E a A) (S.E a B) u t=kernel S A B u (t+a+a):=by
 unfold kernel; rw [S.swing]; have h(c d:ℝ≥0): S.E c (S.E d B)=S.E (c+d) B:=by rw [S.time]; rfl
 have he := S.independent a u; rw [show S.E a (S.U u (S.E t (S.E a B)))= S.U u (S.E a (S.E t (S.E a B))) from DFunLike.congr_fun he _,h,h,show a+(t+a)=t+a+a from (by abel)]
lemma paid_later (e a:ℝ≥0) (h:CenterPays u p S A B e): CenterPays u p S (S.E a A) (S.E a B) (e+a):= by
 obtain ⟨b,h⟩:= eventually_atTop.1 h
 unfold CenterPays; filter_upwards [eventually_ge_atTop b,eventually_ge_atTop (0:ℝ)] with s t v
 rw [cost_both, show s+ ↑(e+a) + ↑(e+a)=s+ ↑a+ ↑a+ ↑e+ ↑e from (by push_cast; ring), h (s+↑a+↑a) (by linarith [show (0:ℝ) ≤ ↑a from a.property]), show (s+↑a+↑a).toNNReal = s.toNNReal+a+a from (Real.toNNReal_add (r:=s+ ↑a) (by positivity) a.property).trans (congrArg₂ (·+·) ((Real.toNNReal_add v a.property).trans (congrArg (s.toNNReal+·) (Real.toNNReal_coe ..))) (Real.toNNReal_coe ..))]
lemma padded_later (a:ℝ≥0)(h:HasPadding S B): HasPadding S (S.E a B):= by
 obtain ⟨r,p,b,e⟩:=h; rw [e]; refine ⟨r,p,S.E a b,?_⟩; exact DFunLike.congr_fun ((S.time a r).symm.trans ((add_comm a r) ▸ S.time r a)) b
lemma dark_later (a:ℝ≥0)(h:S.orth B=0): S.orth (S.E a B)=0:=
 (Submodule.starProjection_apply_eq_zero_iff ..).2 ((S.ground.mem_orthogonal' _).2 fun v w=> by
    rw [S.swing,(S.fixed _).1 w a]; exact (S.ground.mem_orthogonal' _).1 ((Submodule.starProjection_apply_eq_zero_iff ..).1 h) v w)

variable (r:ℝ≥0)
/-- One translation u for the stamp; no need same A B labels, nor unit operator from the election. -/
def ThinRefusal : Prop := ∀ (H:Hilbert)(S:OS.Semigroup H timeAxis)(A A' B B':H), CenterPays u p S A B r →
    ∀ a b:ℝ,a<b→∃ t∈ Ioo a b, ¬ swap S.unit (joinST u t) A A' B B'
lemma padded_price_refuses (P:CenterPays u p S A B r)(f:∃ᶠ i:ℝ in atTop,p i≠0)(g:S.orth B=0)(v: HasPadding S B): ThinRefusal u p r:=
 let ⟨_,t⟩:= kernel_paid_some u p S A B r P f;
 fun _ S' X X' Y Y' h _ _ p'=> edge_any S A B u v g t p' S' X Y (unique_accord u p S A B S' X Y P h) X' Y'
end YM.SatinEdge
#print axioms YM.SatinEdge.falls
#print axioms YM.SatinEdge.kill
#print axioms YM.SatinEdge.padded_price_refuses
