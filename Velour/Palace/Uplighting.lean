import Velour.Crepe.Blanket
import Velour.Tassel.Plan
import YM.SU5.Same.TemperGalaxy
set_option autoImplicit false
set_option maxHeartbeats 800000
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

open SatinNucleus Six
/-!
# Uplight PoweredElection
Strengthen the original choice, don't re-elect independently for the probes.
-/
private lemma htZmirror(P:Spine) (f:ℕ) : Spine.twiceT (P.baseRoot f) 3= Spine.twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]
-- important: can add any a.e. extra.
lemma lit_century (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ P.SilkVelour c r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a∧ (∀ j l, AtGlassRate P x j (P.pointEra s) s l v a) :=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,pat,C,ec,q,H,A,a,season,c₀,r₀,_,ρ₀⟩:= clock_consumption X Y L M p d w z
 obtain ⟨c,r,h,I₀,ρ⟩:=P.relaunch e h0 z (ρ₀.mono fun i p=>p.1)
 obtain ⟨b,β,_,t₀⟩:= SatinJets.common_margin (max7+min7+1) min7 min_positive
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,I₀,b,β,?_⟩
 let A₀:=2*lensValue A; have h8:Tendsto (fun s:ℕ=>A₀ * P.repeatLoss s) atTop (𝓝 0):=by simpa only [mul_zero] using P.era_complete.const_mul A₀
 let νp:= P.pointEra; let δv:=P.future_payment
 filter_upwards [P.payment_late,δv.eventually (P.flight_soon.eventually (gt_mem_nhds w)), P.ready_granule (P.roomy), δv.eventually (P.offers_plans 3 1 zero_lt_one), δv.eventually (P.seat_many 3 1 zero_lt_one), δv.eventually (P.auditsCalendar H a), (P.lantern_go H).eventually (ge_mem_nhds (show 0< min7 /4 /4 from (by linarith only [min_positive]))), δv.eventually P.size_honors,P.reward_positive,h8.eventually (ge_mem_nhds (show 0<b/16 by positivity))] with s Hs w t δ n P0 G0 w0 W K0; let f:= νp s; have hp: f < s:= Hs.2.1
 refine ⟨w,fun F hf=>?_⟩
 let g(x: P.Spectrum0 3):Prop:= (∃ R:P.Ellis 3 x, Spine.Experiment P K c r x R) ∧ F x; have hz:∀ᵐ x∂ P.pillars 3,g x:= ρ.and hf
 have he:P.reached f s:= t
 have ht:Spine.twiceT (P.baseRoot f) 3 ≤ Yoke.scout P.par 1 f:= by rw [htZmirror]; exact n
 have hx':= δ.1 (P.baseRoot f) ht
 have yK: Odd P.par.R.L.val:=⟨P.par.R.L.val/2,by omega⟩
 obtain ⟨x,⟨⟨R,h'⟩,κ'⟩,_, v,a,V,Wⱼ⟩:= P.third_winter h0 hx' hp (fun v w=>P0 v (hp.le.trans w)) G0 he w0.1 (W.2 f) K0 H g hz yK
 let Va:=V.cluster hp
 refine ⟨x,R,κ',⟨h',⟨he,hp,W.1,W.2 f⟩,Va,P.reliable_pp x he W.1 Va.price R t₀ β.le,?_⟩,v,a,V,Wⱼ⟩
 intro U V o t'; let q:Fin 3 → Bool:= fun _=>false; obtain ⟨p, e, _he, _inside, hcost⟩ := authorize q; filter_upwards [packs_within_rectangles (trans6 h') (Metric.ball p e) q hcost U V o t'] with i hi; obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2; exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩
lemma lit_galaxy (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ P.SilkVelour c r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ ∃ (u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), GalaxyShow P x (P.pointEra s) s (P.cinema x (P.pointEra s) s v a q u) V ∧ P.VelvetCup x (P.cinema x (P.pointEra s) s v a q u) ∧ P.PoweredHeat x V:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,I₀,b,β,ρ⟩:= lit_century X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,I₀,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,d,t,v,a,V,Wⱼ⟩:= p.2 F h
 obtain ⟨x',u⟩:= V.station; let f:= P.pointEra i
 have O:Odd P.par.R.L.val:=⟨P.par.R.L.val/2,by omega⟩
 obtain ⟨s,Y,T,T'⟩:= P.velvet_radiated x v u.fast a f i K V h0 t.station.2.1 O
 let J₁:GalaxyShow P x (P.pointEra i) i (P.cinema x f i v a s u.fast) Y:= ⟨T,fun i=> P.pleading_b ..,fun i=> P.pleading_g ..,fun x z=> Spine.freemen P _ f i v u.fast a s Y V t.station.2.1.le t.station.1 β T t.opera x z,fun j l k u v a b t g p=>P.scenic_right x j R T T l k t g (sub_pos.mpr p),fun j l k u v a b t g p=>P.scenic_left x j R T T l k t g (sub_pos.mpr p)⟩
 exact ⟨x,R,d,t,v,a,V,u.fast,s,Y,J₁,T',P.cinema_powers x _ _ v a u.fast s Y Wⱼ J₁⟩
lemma lit_prism_labs (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ P.SilkVelour c r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ ∃ (u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x (P.pointEra s) s v a q u) n), P.VelvetCup x (P.cinema x (P.pointEra s) s v a q u) ∧ P.PoweredHeat x V ∧ P.VelvetHandle c r (P.cinema x (P.pointEra s) s v a q u) x n ∧ (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x (P.pointEra s) s v a q u) c r n p X V (P.pointEra s) s) ∧
          ∀ (U W: Doorway), U.Later W thinAlongOrder 0 → ∀ μ:ℝ,0<μ→ U.upper 3 ≤ -μ → μ ≤ W.lower 3 →
            ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x (P.pointEra s) s v a q u) c r n p V (P.pointEra s) s X μ F G U W (c i) (r i) K :=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,I₀,b,β,ρ⟩:= lit_galaxy X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,I₀,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,h,t,v,a,V,u,Q,X,T,T',hw⟩:= p.2 F h
 let Y₁:= P.cinema x (P.pointEra i) i v a Q u
 obtain ⟨N,d,I₁⟩:= P.velour_sales x c r Y₁ t.setup I₀
 let u'(p:Lead.Clan → SatinJets.Prism):= P.get_armada x Y₁ c r N p d X (P.pointEra i) i T (P.makeFleet x c r Y₁ N t.setup d T.heat (fun j=> P.cinema_pure x _ _ v a Q u j))
 refine ⟨x,R,h,t,v,a,V,u,Q,X,N,d,T',hw,I₁,u',fun F F' e m m' l i' =>?_⟩
 filter_upwards [P.ordersPrism x (P.pointEra i) i X m T R K F F' e l i' t.setup m'] with j h; obtain ⟨D₁,D₂,w',H⟩:= h; exact ⟨D₁,D₂,w',P.honorLab x _ _ _ _ _ _ _ _ _ (u' w') R _ _ _ _ _ _ _ _ e l i' H⟩

#print axioms lit_prism_labs
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

