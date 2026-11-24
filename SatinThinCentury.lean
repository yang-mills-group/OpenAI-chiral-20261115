import SatinFixedContrastNovember4
import SatinThinPlane
import SatinThinCongress
/-! # Actual estimate: propagation preparedness. 
       With supply on the very same Course and Run. See the construction notes. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
namespace Spine
variable {P:Spine}{f r v:ℕ}{A b C:ℝ}
structure ScoutAnthem(P:Spine)(x:P.Spectrum0 3)(A C:ℝ)(f r:ℕ)(b:ℝ)(v:ℕ→ℕ)(a:ℕ→ (ℕ×ℕ)→ℝ):Prop where
 station: ∃ R:ℕ→Pedal P f, AtMile P A C f r x b v a R
 earns: ∀(j:Axis)(l:List Axis)(e:ℝ),0<e→∃ B:ℝ, ∀ᶠ i:ℕ in atTop,P.roomy * P.macroStep (v i) < e ∧ ‖(a i (f,r):ℂ) • P.beamWatch j x f (v i) l e‖≤ B
variable (P)
local notation "χ"=> P.pillars 3
variable (G₀:P.NightCop)(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)(F₀:f<r)(P0:∀ v:ℕ,r ≤ v→∃ c a w, Workforce A C f v P c a w)(Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(u:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ b/16)
include G₀ Book F₀ P0 Q0 u S D Z0
lemma second_winter (D₀: P.Spectrum0 3→Prop)(p0:∀ᵐ x∂χ,D₀ x)(p:Odd P.par.R.L.val) :
    ∃ x: P.Spectrum0 3,D₀ x ∧ ∃ v a, ScoutAnthem P x A C f r b v a:=by
 obtain ⟨g,t⟩:= exists_surjective_nat (Axis×List Axis ×ℕ); let H(v:ℕ):= P.macroStep v; have h(i): Nonempty (ForecastCard P f r (g i).1 (g i).2.1 (H (g i).2.2)):=P.forever_quote _ _ _ _ _ (P.macroStep_pos _); let F(i):= Classical.choice (h i); let Rv(i):= P.pedal_ξ _ (F i)
 obtain ⟨x,d,v,a,w⟩:= P.appearance G₀ Book F₀ P0 Q0 u S D Z0 Rv D₀ p0
 have he(j:Axis)(l:List Axis)(k:ℕ): ∃ B:ℝ, ∀ᶠ i:ℕ in atTop, ‖(a i (f,r):ℂ) • P.beamWatch j x f (v i) l (H k)‖ ≤ B:=by
    obtain ⟨n,p'⟩:= t (j,l,k)
    suffices h: ∃ B:ℝ,∀ᶠ i:ℕ in atTop, ‖(a i (f,r):ℂ) • P.beamWatch (g n).1 x f (v i) (g n).2.1 (H (g n).2.2)‖ ≤ B by rw [p'] at h; exact h
    refine ⟨P.cardPrice (g n).1 x (F n) A n,?_⟩; filter_upwards [w.extra n, w.fast.tendsto_atTop.eventually (P.account_due _ x (F n) F₀ p n A C)] with i t' u1; obtain ⟨c,l,Y⟩:= w.cruise i; exact u1 _ Y t'
 refine ⟨x,d,v,a,⟨Rv,w⟩,?_⟩; intro j l e h; obtain ⟨k,u⟩:= (P.macroStep_zero.eventually (gt_mem_nhds h)).exists; have hu: H k < e:=u
 obtain ⟨B,t'⟩:= he j l k; have ht:Tendsto (fun s=> (P.roomy:ℝ)*H s) atTop (𝓝 0):=by simpa only [mul_zero] using (P.macroStep_zero.const_mul (P.roomy:ℝ))
 refine ⟨B,?_⟩; filter_upwards [w.fast.tendsto_atTop.eventually (ht.eventually (gt_mem_nhds (P.macroStep_pos k))),t'] with i p q; have hp:(P.roomy:ℝ)*P.macroStep (v i)< H k:= p; refine ⟨hp.trans hu, le_trans ?_ q⟩; rw [norm_smul,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply P.beam_right_le j x _ (by rw [Apron.pivot_w,P.play_width]; exact hp.le) hu.le -- syntax _
omit G₀ Book F₀ P0 Q0 u S D Z0
variable {P}
lemma ScoutAnthem.cluster {a:ℕ→(ℕ×ℕ)→ℝ}{v:ℕ→ℕ}{x:P.Spectrum0 3}(T:ScoutAnthem P x A C f r b v a)(p:f < r): Clump P A C x f r b:=by
 obtain ⟨R,t,h,e,F,m,Q⟩:= T.station; refine ⟨F, Filter.frequently_atTop.mpr fun n=>?_⟩
 obtain ⟨i,hi⟩:= (t.tendsto_atTop.eventually (eventually_ge_atTop n)).exists; obtain ⟨w,g,x'⟩:= e i; exact ⟨v i,hi,a i (f,r),_,g,x'.plans _ (show chargeSpan f (v i) (f,r) from ⟨le_rfl,p,h i⟩),m i⟩
end Spine
private lemma htZ(P:Spine) (f:ℕ) : Spine.twiceT (P.baseRoot f) 3= Spine.twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]
-- important: can add any a.e. extra.
lemma elected_century (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,pat,C,ec,q,H,A,a,season,c,r,h,ρ⟩:= clock_consumption X Y L M p d w z
 obtain ⟨b,β,_,t₀⟩:= SatinJets.common_margin (max7+min7+1) min7 min_positive
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,?_⟩
 let A₀:=2*lensValue A; have h8:Tendsto (fun s:ℕ=>A₀ * P.repeatLoss s) atTop (𝓝 0):=by simpa only [mul_zero] using P.era_complete.const_mul A₀
 let νp:= P.pointEra; let δv:=P.future_payment
 filter_upwards [P.payment_late,δv.eventually (P.flight_soon.eventually (gt_mem_nhds w)), P.ready_granule (P.roomy), δv.eventually (P.offers_plans 3 1 zero_lt_one), δv.eventually (P.seat_many 3 1 zero_lt_one), δv.eventually (P.auditsCalendar H a), (P.lantern_go H).eventually (ge_mem_nhds (show 0< min7 /4 /4 from (by linarith only [min_positive]))), δv.eventually P.size_honors,P.reward_positive,h8.eventually (ge_mem_nhds (show 0<b/16 by positivity))] with s Hs w t δ n P0 G0 w0 W K0; let f:= νp s; have hp: f < s:= Hs.2.1
 refine ⟨w,fun F hf=>?_⟩
 let g(x: P.Spectrum0 3):Prop:= (∃ R:P.Ellis 3 x, Spine.Experiment P K c r x R) ∧ F x; have hz:∀ᵐ x∂ P.pillars 3,g x:= (ρ.mono (fun x p=> p.1)).and hf
 have he:P.reached f s:= t
 have ht:Spine.twiceT (P.baseRoot f) 3 ≤ Yoke.scout P.par 1 f:= by rw [htZ]; exact n
 have hx':= δ.1 (P.baseRoot f) ht
 have yK: Odd P.par.R.L.val:=⟨P.par.R.L.val/2,by omega⟩
 obtain ⟨x,⟨⟨R,h'⟩,κ'⟩, v,a,V⟩:= P.second_winter h0 hx' hp (fun v w=>P0 v (hp.le.trans w)) G0 he w0.1 (W.2 f) K0 g hz yK
 let Va:=V.cluster hp
 refine ⟨x,R,κ',⟨h',⟨he,hp,W.1,W.2 f⟩,Va,P.reliable_pp x he W.1 Va.price R t₀ β.le,?_⟩,v,a,V⟩
 intro U V o t'; let q:Fin 3 → Bool:= fun _=>false; obtain ⟨p, e, _he, _inside, hcost⟩ := authorize q; filter_upwards [packs_within_rectangles (trans6 h') (Metric.ball p e) q hcost U V o t'] with i hi; obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2; exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.elected_century
