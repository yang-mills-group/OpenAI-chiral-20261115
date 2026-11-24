import SatinFixedContrastNovember4
import SatinThinJetsPurchase
/-! # Milestone 13 actual order

On the elected lattice/gauge-matter run, full density estimate even at thin
width, IN THE HEAT PROFILE OF MANYF. Mixed approximation not yet claimed,
not yet claiming as the final sewn thin interaction theorem; isolates the
*selection and ordering* expenditure. See `the construction notes`.
-/
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

open SatinNucleus Six
-- arbitrary position Pair boxes as long as all axis positive and straddle our wall strictly by paid positive amount.
lemma elected_orderedPrism (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ ∃ (u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), GalaxyShow P x (P.pointEra s) s (P.cinema x (P.pointEra s) s v a q u) V ∧
          ∀ (U W: Doorway), U.Later W thinAlongOrder 0 → ∀ μ:ℝ,0<μ→ U.upper 3 ≤ -μ → μ ≤ W.lower 3 →
            ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.OnceHere x V p μ (c i) (r i) F G K U W :=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_galaxy X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,h,t,v,a,V,u,Q,X,g⟩:= p.2 F h
 exact ⟨x,R,h,t,v,a,V,u,Q,X,g,fun U W v μ p u w=>P.ordersPrism x (P.pointEra i) i X μ g R K U W v u w t.setup p⟩

-- in particular the concrete boxes. arbitrary supplier data in this theorem.
lemma orderedPrism_review (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ): ∃(P:Spine)(K:P.Register), uniform P K Y L M ∧ ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), z ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), GalaxyShow P x f s (P.cinema x f s v a q u) V ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.OnceHere x V p 1 (c i) (r i) F G K reviewEarlierBox reviewLaterBox:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_orderedPrism X Y L M p 1 zero_lt_one z
 obtain ⟨i,_,s⟩:= ρ.exists
 obtain ⟨x,R,_,t,v,a,V,u,Q,X,g,f⟩:= s (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 exact ⟨P,K,e,x,R,c,r,h,t.setup, P.pointEra i,i,v,a,u,Q,X,g, f reviewEarlierBox reviewLaterBox thinEarlier _ zero_lt_one (le_refl _) (le_refl _)⟩ -- uniform check
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.elected_orderedPrism
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.orderedPrism_review
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.elected_orderedPrism
