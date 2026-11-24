import GaugeFieldConstruction.SlotCrownRP
/-! strong local cyclicity, Minkowski neighborhood. No local assumption on annihilator.
 Key: local product → propagate tack → remove single arbitrary slot by distribution. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex Metric Poincare
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
variable (v:Fin n→ Letter S)(U:Set E4)(o:IsOpen U)
-- ahead support lemmas duplicate; avoid heavy imports (ArcBefore in callers)
def shiftSetRP (b:E4): Set E4:= (fun v=>v-b)⁻¹' U
lemma open_shiftRP(h:IsOpen U)(b:E4): IsOpen (shiftSetRP U b):=h.preimage (continuous_id.sub continuous_const)
abbrev anchoredRP(L:Test4)(U:Set E4):Prop:=tsupport L⊆U ∧ HasCompactSupport ⇑L
def onSiteRP (L: Letter S)(U:Set E4):Prop:= anchoredRP L.2 U
def decideFullRP (T:Wightman S)(U:Set E4)(v:T.operators.H):Prop:=∀ (b:Sentence S), (∀ k∈b,onSiteRP k U)→inner ℂ v (T.operators.vector b)=0
variable (Ωv:d.system.operators.H)(t:decideFullRP d.system U Ωv)
variable (f:Test4)(w:E4)
lemma aheadSupportRP:tsupport (Probe.ahead w f)⊆shiftSetRP (tsupport f) w := tsupport_comp_subset_preimage ⇑f (show Continuous (fun x:E4=>x-w) from continuous_id.sub continuous_const)
lemma smolTackRP(h:HasCompactSupport ⇑f):HasCompactSupport (Probe.ahead w f :E4→ℂ):=by
 apply (h.image (show Continuous (fun x=> x+w) from continuous_id.add continuous_const)).of_isClosed_subset (isClosed_tsupport _); intro i p; exact ⟨i-w,aheadSupportRP f w p,by simp⟩
include o in
lemma tinySideRP (p:anchoredRP f U): ∀ᶠ z:E4 in 𝓝 0,anchoredRP (Probe.ahead z f) U:=by
 let F(x:E4×E4):= x.2+x.1
 have hp:∀ᶠ z:E4 in 𝓝 0,∀ k∈tsupport f,F (z,k)∈U:= p.2.eventually_forall_of_forall_eventually (fun x t=> (o.preimage (show Continuous F from continuous_snd.add continuous_fst)).mem_nhds (show (0,x)∈F⁻¹' U from by simp only[F,mem_preimage, add_zero]; exact p.1 t))
 filter_upwards [hp] with z u; refine ⟨fun k h=>?_,smolTackRP f z p.2⟩
 simpa only [F,sub_add_cancel] using u (k-z) (aheadSupportRP f z h)
include o t
lemma StartHullRP (h:∀ i,onSiteRP (v i) U): 0∈ loudRP d v Ωv:=by
 have hx:∀ᶠ z:Points n in 𝓝 0,∀ i,onSiteRP (forwardRP v z i) U:=by
    apply eventually_all.mpr; intro i
    have hy:Tendsto (fun x:Points n=> x i) (𝓝 0) (𝓝 0):=(show Continuous (fun x:Points n=> x i) from by fun_prop).tendsto 0
    exact hy.eventually (tinySideRP _ o _ (h i))
 exact hx.mono fun i p=> t (List.ofFn (forwardRP v i)) (fun k u=>by obtain ⟨j,rfl⟩:= List.mem_ofFn.mp u; exact p j)
include b H
lemma AnywherePadRP (h:∀ i:Fin n, ∃ x:E4,onSiteRP (v i) (shiftSetRP U x)):inner ℂ Ωv (d.system.operators.vector (List.ofFn v)) =0:=by
 choose x hx using h; let f:=forwardRP v (-(points x)); have he:forwardRP f (points x)=v:=by rw [speakTrodRP,neg_add_cancel]; exact forward_stillRP ..
 have hr:0∈ loudRP d f Ωv:= StartHullRP d f U o Ωv t (fun i=>by
    have ha(i:Fin n): -(points x) i= -x i:=by rw [points_apply]
    change anchoredRP (Probe.ahead _ _) _
    have hw:=hx i; unfold onSiteRP anchoredRP at hw; refine ⟨fun y r=>?_,smolTackRP _ _ hw.2⟩
    have hs:=hw.1 (show y- (-points x) i∈tsupport (v i).2 from aheadSupportRP _ _ r)
    change y- _ - _∈ U at hs; simpa using hs)
 have hp:=FullTackRP d H b f Ωv 0 hr (points x); rw [zero_add] at hp; have hb:= soundsAtRP d f Ωv (points x) hp; unfold dingRP at hb; rwa[he] at hb
lemma onListPadRP (a: Sentence S)(h: ∀ k∈a, ∃ x:E4, onSiteRP k (shiftSetRP U x)):inner ℂ Ωv (d.system.operators.vector a)=0:=by
 nth_rw 1 [show a= List.ofFn a.get from (List.ofFn_get ..).symm]; exact AnywherePadRP d H b _ U o Ωv t (fun i=>h (a.get i) (List.get_mem ..))
include U
variable (q:U.Nonempty)
include q
lemma anyWordRP (a c: Sentence S)(h:∀ k∈a, ∃ x:E4, onSiteRP k (shiftSetRP U x)):inner ℂ Ωv (d.system.operators.vector (a++c))=0:=by
 induction c generalizing a with
 | nil=> exact List.append_nil _ ▸ onListPadRP d H b U o Ωv t a h -- tune
 | cons k c ih=>
   let V:=d.system.operators; let T:Distn E4:= (innerSL ℂ Ωv).comp (Fields.singleLocalRP V k.1 a c d.course.meets d.course.adj); have hr(f:Test4): T f= inner ℂ Ωv (V.vector (a++((k.1,f)::c))):=by rw [← V.singleQuoteRP k.1 a c d.course.meets d.course.adj]; rfl
   have hx(x:E4): IsVanishingOn T (shiftSetRP U x):= (Distn.from_compact T).2 (by
      intro f t hU; rw[hr,show a++((k.1,f)::c)=(a++[(k.1,f)])++c from by simp]
      exact ih _ (fun l p=>by
         obtain p|p:=List.mem_append.mp p
         · exact h l p
         exact List.mem_singleton.mp p |>.symm ▸ (show ∃ y:E4, onSiteRP ((k.1,f):Letter S) (shiftSetRP U y) from ⟨x,⟨t,hU⟩⟩)))
   obtain ⟨x,p⟩:=q; have hy: dsupport T ⊆∅:=by
      intro i hi; have hz:i∈shiftSetRP U (i-x):=by simpa [shiftSetRP] using p
      exact absurd (hx (i-x)) ((mem_dsupport_iff_not_isVanishingOn i).1 hi _ hz (open_shiftRP _ o _)) -- o
   have ht:= (Distn.due T _ isClosed_empty).1 hy
   exact (hr k.2).symm.trans (ht k.2 (by simp)) -- eta
lemma FillΩRP : Ωv=0:=by
 have he: d.system.operators.domain ≤ LinearMap.ker (innerSL ℂ Ωv).toLinearMap:=by
    rw [d.course.total.cyclic]; apply Submodule.span_le.mpr; rintro _ ⟨p,rfl⟩; exact anyWordRP d H b U o Ωv t q [] p (by simp)
 have hz:=Submodule.topologicalClosure_minimal _ he (innerSL ℂ Ωv).isClosed_ker (show Ωv∈d.system.operators.domain.topologicalClosure from d.course.total.everywhere Ωv)
 exact (inner_self_eq_zero (𝕜:=ℂ)).1 hz
#print axioms FillΩRP
end YM.NSF.Boundary
end
