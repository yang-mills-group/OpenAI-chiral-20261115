import SatinThinVisit
import SatinFixedContrastNovember4
import SatinPP.Silage
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
variable (P)
local notation "χ"=> P.pillars 3
variable (G₀:P.NightCop)(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)(F₀:f<r)(P0:∀ v:ℕ,r ≤ v→∃ c a w, Workforce A C f v P c a w)(Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(u:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ b/16)
include G₀ Book F₀ P0 Q0 u S D Z0
abbrev Rindle(x:P.Spectrum0 3)(f r:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ) :Prop:=
     ∃ l:ℕ→ℕ,StrictMono l ∧ P.Spots l x ∧ ∀ n,P.Offering x (P.pointEra (l n)) (l n) v a f r (turncost n)
lemma jubilee (adv:P.Care C)(Tt:∃ᶠ s:ℕ in atTop,P.Synchrony f (P.pointEra s)) (D₀: P.Spectrum0 3→Prop)(p0:∀ᵐ x∂χ,D₀ x)(p:Odd P.par.R.L.val) :
    ∃ x: P.Spectrum0 3,D₀ x ∧ ∃ v a, ScoutAnthem P x A C f r b v a ∧ P.Rindle x f r v a:=by
 obtain ⟨g,t⟩:= exists_surjective_nat (Axis×List Axis ×ℕ); let H(v:ℕ):= P.macroStep v; have h(i): Nonempty (ForecastCard P f r (g i).1 (g i).2.1 (H (g i).2.2)):=P.forever_quote _ _ _ _ _ (P.macroStep_pos _); let F(i):= Classical.choice (h i); let Qv(i):= P.pedal_ξ _ (F i)
 obtain ⟨u₀,u₂,t₀,k⟩:=P.sprint_route (r:=r) A adv Tt
 let Rv(i):= if i%2=0 then (k (i/2)).pedal else Qv (i/2)
 have M(i):Rv (2*i)=(k i).pedal := by
    have :2*i%2=0:=by omega
    unfold Rv;rw [if_pos this, Nat.mul_div_cancel_left _ (show 0<2 by decide)]
 have N(i):Rv (2*i+1)=Qv i := by
    have :¬ (2*i+1)%2=0:=by omega
    unfold Rv;rw [if_neg this, show (2*i+1)/2=i by omega]
 obtain ⟨x,⟨d,hp⟩,v,a,w⟩:= P.appearance G₀ Book F₀ P0 Q0 u S D Z0 Rv (fun x=>D₀ x ∧ P.Spots u₀ x) (p0.and t₀)
 have he(j:Axis)(l:List Axis)(k:ℕ): ∃ B:ℝ, ∀ᶠ i:ℕ in atTop, ‖(a i (f,r):ℂ) • P.beamWatch j x f (v i) l (H k)‖ ≤ B:=by
    obtain ⟨n,p'⟩:= t (j,l,k)
    suffices h: ∃ B:ℝ,∀ᶠ i:ℕ in atTop, ‖(a i (f,r):ℂ) • P.beamWatch (g n).1 x f (v i) (g n).2.1 (H (g n).2.2)‖ ≤ B by rw [p'] at h; exact h
    refine ⟨P.cardPrice (g n).1 x (F n) A (2*n+1),?_⟩; have hx:=w.extra (2*n+1);rw [N] at hx; filter_upwards [hx, w.fast.tendsto_atTop.eventually (P.account_due _ x (F n) F₀ p (2*n+1) A C)] with i t' u1; obtain ⟨c,l,Y⟩:= w.cruise i; exact u1 _ Y t'
 have Anthem: ScoutAnthem P x A C f r b v a:= by
    refine ⟨⟨Rv,w⟩,?_⟩; intro j l e h; obtain ⟨k,u⟩:= (P.macroStep_zero.eventually (gt_mem_nhds h)).exists; have hu: H k < e:=u
    obtain ⟨B,t'⟩:= he j l k; have ht:Tendsto (fun s=> (P.roomy:ℝ)*H s) atTop (𝓝 0):=by simpa only [mul_zero] using (P.macroStep_zero.const_mul (P.roomy:ℝ))
    refine ⟨B,?_⟩; filter_upwards [w.fast.tendsto_atTop.eventually (ht.eventually (gt_mem_nhds (P.macroStep_pos k))),t'] with i p q; have hp:(P.roomy:ℝ)*P.macroStep (v i)< H k:= p; refine ⟨hp.trans hu, le_trans ?_ q⟩; rw [norm_smul,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply P.beam_right_le j x _ (by rw [Apron.pivot_w,P.play_width]; exact hp.le) hu.le -- syntax _
   
 obtain ⟨u',a',H',w'⟩:= P.fineLine x F₀ k Anthem (fun n=> by
                                                                    have h:=w.extra (2*n)
                                                                    rw [M] at h; exact h)
 exact ⟨x,d,u',a',H',u₀,u₂,hp,w'⟩

end Spine
private lemma htZ(P:Spine) (f:ℕ) : Spine.twiceT (P.baseRoot f) 3= Spine.twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]
-- important: can add any a.e. extra.
lemma elected_jubilee (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ P.Rindle x (P.pointEra s) s v a:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,pat,C,ec,q,H,A,a,season,c,r,h,ρ⟩:= clock_consumption X Y L M p d w z
 obtain ⟨b,β,_,t₀⟩:= SatinJets.common_margin (max7+min7+1) min7 min_positive
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,?_⟩
 let A₀:=2*lensValue A; have h8:Tendsto (fun s:ℕ=>A₀ * P.repeatLoss s) atTop (𝓝 0):=by simpa only [mul_zero] using P.era_complete.const_mul A₀
 let νp:= P.pointEra; let δv:=P.future_payment
 filter_upwards [P.calendar_fringes,P.payment_late,δv.eventually (P.flight_soon.eventually (gt_mem_nhds w)), P.ready_granule (P.roomy), δv.eventually (P.offers_plans 3 1 zero_lt_one), δv.eventually (P.seat_many 3 1 zero_lt_one), δv.eventually (P.auditsCalendar H a), (P.lantern_go H).eventually (ge_mem_nhds (show 0< min7 /4 /4 from (by linarith only [min_positive]))), δv.eventually P.size_honors,P.reward_positive,h8.eventually (ge_mem_nhds (show 0<b/16 by positivity))] with s Ti Hs w t δ n P0 G0 w0 W K0; let f:= νp s; have hp: f < s:= Hs.2.1
 refine ⟨w,fun F hf=>?_⟩
 let g(x: P.Spectrum0 3):Prop:= (∃ R:P.Ellis 3 x, Spine.Experiment P K c r x R) ∧ F x; have hz:∀ᵐ x∂ P.pillars 3,g x:= (ρ.mono (fun x p=> p.1)).and hf
 have he:P.reached f s:= t
 have ht:Spine.twiceT (P.baseRoot f) 3 ≤ Yoke.scout P.par 1 f:= by rw [htZ]; exact n
 have hx':= δ.1 (P.baseRoot f) ht
 have yK: Odd P.par.R.L.val:=⟨P.par.R.L.val/2,by omega⟩
 obtain ⟨x,⟨⟨R,h'⟩,κ'⟩, v,a,V,Vi⟩:= P.jubilee h0 hx' hp (fun v w=>P0 v (hp.le.trans w)) G0 he w0.1 (W.2 f) K0 H Ti g hz yK
 let Va:=V.cluster hp
 refine ⟨x,R,κ',⟨h',⟨he,hp,W.1,W.2 f⟩,Va,P.reliable_pp x he W.1 Va.price R t₀ β.le,?_⟩,v,a,V,Vi⟩
 intro U V o t'; let q:Fin 3 → Bool:= fun _=>false; obtain ⟨p, e, _he, _inside, hcost⟩ := authorize q; filter_upwards [packs_within_rectangles (trans6 h') (Metric.ball p e) q hcost U V o t'] with i hi; obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2; exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩
open SatinNucleus Six 
lemma elected_silhouette (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ ∃ (u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), GalaxyShow P x (P.pointEra s) s (P.cinema x (P.pointEra s) s v a q u) V ∧ P.Silhouette x V:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_jubilee X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,d,t,v,a,V,k,u',p₁,p₂⟩:= p.2 F h
 obtain ⟨x',u⟩:= V.station; let f:= P.pointEra i; obtain ⟨s,Y,T⟩:= P.radiated x v u.fast a f i V
 exact ⟨x,R,d,t,v,a,V,u.fast,s,Y,⟨T,fun i=> P.pleading_b ..,fun i=> P.pleading_g ..,fun x z=> Spine.freemen P _ f i v u.fast a s Y V t.station.2.1.le t.station.1 β T t.opera x z,fun j l k u v a b t g p=>P.scenic_right x j R T T l k t g (sub_pos.mpr p),fun j l k u v a b t g p=>P.scenic_left x j R T T l k t g (sub_pos.mpr p)⟩, k,P.auditions x Y T R u' p₁ turn_soon (Eventually.of_forall fun v₀=> P.recoups x _ v u.fast a s Y _ _ (p₂ v₀) (turn_pos _) T (P.medal x Y (freemen P _ f i v u.fast a s Y V t.station.2.1.le t.station.1 β T t.opera)))⟩
#print axioms elected_silhouette
