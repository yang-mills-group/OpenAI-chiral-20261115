import ZecaFresh
import SatinThinFieldInteraction
import ZecaAureole
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
lemma elected_thin_cloud (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ P.Snowy c r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ ∃ (u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x (P.pointEra s) s v a q u) n), Skyways P (P.pointEra s) s A C (P.rewardK (P.pointEra s) s) v a ∧ P.Aureole x (P.cinema x (P.pointEra s) s v a q u) c r n ∧ (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x (P.pointEra s) s v a q u) c r n p X V (P.pointEra s) s) ∧
          ∀ (U W: Doorway), U.Later W thinAlongOrder 0 → ∀ μ:ℝ,0<μ→ U.upper 3 ≤ -μ → μ ≤ W.lower 3 →
            ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x (P.pointEra s) s v a q u) c r n p V (P.pointEra s) s X μ F G U W (c i) (r i) K :=by

 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,snow,b,β,ρ⟩:= elected_fresh X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,snow,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,l,t,v',a',V'⟩:= p.2 F h
 obtain ⟨Z,X,⟨v,a₂,u,Q,V,m,rfl⟩,g,T⟩:= sky_voyage t V' β h0
 let Y':= P.cinema x (P.pointEra i) i v a₂ Q u
 obtain ⟨N,d',s⟩:= P.pollen_sale x c r Y' t.setup snow
 have g':=P.makeFleet x c r Y' N t.setup d' g.heat (fun j=>P.cinema_pure x (P.pointEra i) i v a₂ Q u j)
 let fleet:= fun p=>P.get_armada x Y' c r N p d' X _ _ g g'
 refine ⟨x,R,l,t,v,a₂,V,u,Q,X,N,d',m,P.aureole _ _ _ _ _ T snow s g',fleet, fun F F' l' μ p a b=>?_⟩
 filter_upwards [P.ordersPrism x (P.pointEra i) i X μ g R K F F' l' a b t.setup p] with j h
 obtain ⟨D₁,D₂,w',J⟩:= h
 exact ⟨D₁,D₂,w',P.honorLab x _ _ _ _ _ _ _ _ _ (fleet w') R _ _ _ _ _ _ _ _ l' a b J⟩
#print axioms elected_thin_cloud
