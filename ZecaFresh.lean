import ZecaVow
import ZecaFount
import SatinThinHarmonica
import SatinThinReality
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
/-! # Keep CP18 prices, feast and launches; apply schedule, simultaneously on their SAME x. Adaptation from SatinThinHarmonica, -Reality, -Century. -/
namespace Spine
open Regis.Head.Brecht Regis.Circuit Regis.Head.Garland Papal
open scoped Classical
variable (P:Spine)(R:P.Register)(z:ℕ→ℕ) (d:ℝ)
variable {X:Supplier}{t B:ℝ}{C:ℝ}(u:uniform P R X t B)
-- all simultaneously. further market may choose from this **filter**, not deploy multiple phase picks.
include u in
lemma fresh_stage (night:P.NightCop) (p:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → Yoke.ShelterCost C P.run s i k)(w:0<d) : ∃ (c r:ℕ→ℕ), z≤r ∧ P.Snowy c r ∧ ∀ᵐ x∂P.pillars 3,
  (∃ J:P.Ellis 3 x,Spine.Experiment P R c r x J) ∧ ∀ᶠ i in atTop,P.haloCost d (c i) x < Yoke.canonWeight/32:=by
 obtain ⟨z0,hz,θ⟩:= P.schedule_ask u night z
 obtain ⟨r,g,b,p'⟩:= Prototype.outing u keyV keyV_positive z0
 obtain ⟨s,hb⟩:= θ r g
 obtain ⟨f,q⟩:= P.chooseFarther p d (Yoke.canonWeight/32) w (by have ht:=Yoke.focus_positive; positivity)
 obtain ⟨c,h,lt⟩:= choose_gradients fun i=> max (s i) (max (f i) (b i))
 have t:∀ i,max (f i) (b i)≤c i:=fun i=>(le_max_right ..).trans (lt i)
 obtain ⟨e,v,l⟩:= p' c h fun i=> (le_max_right ..).trans (t i)
 refine ⟨c,r,fun i=>(hz i).trans (g i), hb c (fun i=> (le_max_left ..).trans (lt i)),?_⟩; filter_upwards [P.many_stars 3 R,l, q c fun i=> (le_max_left ..).trans (t i)] with x j e' X'; obtain ⟨J⟩:=P.ellisP 3 x R; let hu:= P.parting 3 x R (P.homes_weather R 3 (P.all_phases 3 x j)); exact ⟨⟨J,e,e',hu, Spine.final_issues R J hu, P.footway _ J R hu⟩,X'⟩
end Spine
open QuadClock
lemma fresh_consumption (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧
     Yoke.Dispatchers P.par ∧
     (∀ e:ℝ,0<e→∀ᶠ s in atTop,(∀ j:Axis,∃ x:Cover, Plans j x s P ∧ P.repeatBill (Spine.twiceT x j) s)∧ P.repeatBill (Yoke.scout P.par e s) s)∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ P.Snowy c r ∧ ∀ᵐ x∂ P.pillars 3,
      (∃ J:P.Ellis 3 x, Spine.Experiment P K c r x J) ∧ P.Transmission x c r ∧
        (∀ᶠ i in atTop,Yoke.canonWeight/32 ≤ (Yoke.scout P.par d (c i):ℝ)^8 * (P.pulseQ 3 Yoke.witnessZ (c i) (Yoke.CheckPoint P.par d (c i)) 0 x).re) ∧
        ∀ (U V : Doorway) (order : Orders), U.Later V order 0 → ∀ᶠ i : ℕ in atTop,
          ∃ (a : ℝ) (F G : SampleDose), F.Normalized ∧ G.Normalized ∧
            tsupport F.val ⊆ U.invites ∧ tsupport G.val ⊆ V.invites ∧
            P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G := by
  obtain ⟨n,i,P,K,Q,r,v,t,g,pr,tq,U,G,⟨C,p',c,D⟩,⟨A,y,q⟩,_⟩:= partridge X Y L M p z
  obtain ⟨v',f,q1,snow,L'⟩:= P.fresh_stage K z d Q v D w
  refine ⟨n,P,K,Q,r,v,t,g,pr,tq,G,?_,C,p',c,D,A,y,?_, v',f,q1,snow,?_⟩
  · intro e u; filter_upwards [(eventually_all_finset univ).mpr (fun j _=> P.offers_plans j e u), P.weather_bill e u] with i p q
    exact ⟨fun j=> (p j (mem_univ _)).2,q⟩
  · filter_upwards [P.treasury_plot A C D y] with f p r e u z; obtain ⟨b,a,l,h⟩:=P.penny_p (p r e u z); exact ⟨b,a,l,h,fun j x y c=> ⟨P.vision j x h y c v,P.caucus j x h y z e.le c v⟩⟩
  filter_upwards [L'] with x p; obtain ⟨⟨J,Jh⟩,g⟩:=p; have β:= trans6 Jh
  refine ⟨⟨J,Jh⟩,β, g.mono fun i u=> P.bill_positive d _ u.le,?_⟩
  intro U V order sep
  let b : Fin 3 → Bool := fun _ => false
  obtain ⟨p, e, _he, _inside, hcost⟩ := authorize b
  filter_upwards [packs_within_rectangles β (Metric.ball p e) b hcost U V order sep] with i hi
  obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2
  exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
private lemma htZ(P:Spine) (f:ℕ) : Spine.twiceT (P.baseRoot f) 3= Spine.twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]
-- important: can add any a.e. extra.
lemma elected_fresh (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ P.Snowy c r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,pat,C,ec,q,H,A,a,season,c,r,h,snow,ρ⟩:= fresh_consumption X Y L M p d w z
 obtain ⟨b,β,_,t₀⟩:= SatinJets.common_margin (max7+min7+1) min7 min_positive
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,snow,b,β,?_⟩
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
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.elected_fresh
