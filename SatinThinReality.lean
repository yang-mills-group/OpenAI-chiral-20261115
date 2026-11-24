import SatinFixedContrastNovember4
import SatinThinAngle
import SatinThinSpring
import SatinThinCivilization
import SatinThinHarmonica

/-! # Actual estimate: excited-account motion pricing. 
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
abbrev EarnedClockPlot (P:Spine)(C A:ℝ)(f r v:ℕ)(e:f<r)(u:r≤v): Prop:=
 ∃ (b:ℕ→ℝ)(a:ℝ)(l:ℕ→ℕ), Spine.lender A C f r v b a l P ∧ ∀ (j:Axis)(X:Cover)(p:Spine.Plans j X f P),P.repeatBill (Spine.twiceT X j) f→
   ‖P.vivid j f r v a (P.flume j X v p) (P.flume j X r p)‖^2≤3*Yoke.owedF P.par f A 2∧ (∫ x:P.Spectrum0 j, ‖P.stateVox j x v (P.cameo j X a e.le u p)‖^2 ∂(P.pillars j))≤3*Yoke.owedF P.par f A 2

lemma clock_consumption (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧
     Yoke.Dispatchers P.par ∧
     (∀ e:ℝ,0<e→∀ᶠ s in atTop,(∀ j:Axis,∃ x:Cover, Plans j x s P ∧ P.repeatBill (Spine.twiceT x j) s)∧ P.repeatBill (Yoke.scout P.par e s) s)∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∀ᵐ x∂ P.pillars 3,
      (∃ J:P.Ellis 3 x, Spine.Experiment P K c r x J) ∧ P.Transmission x c r ∧
        (∀ᶠ i in atTop,Yoke.canonWeight/32 ≤ (Yoke.scout P.par d (c i):ℝ)^8 * (P.pulseQ 3 Yoke.witnessZ (c i) (Yoke.CheckPoint P.par d (c i)) 0 x).re) ∧
        ∀ (U V : Doorway) (order : Orders), U.Later V order 0 → ∀ᶠ i : ℕ in atTop,
          ∃ (a : ℝ) (F G : SampleDose), F.Normalized ∧ G.Normalized ∧
            tsupport F.val ⊆ U.invites ∧ tsupport G.val ⊆ V.invites ∧
            P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G := by
  obtain ⟨n,i,P,K,Q,r,v,t,g,pr,tq,U,G,⟨C,p',c,D⟩,⟨A,y,q⟩,_⟩:= partridge X Y L M p z
  obtain ⟨v',f,q1,L'⟩:= P.further_stage K z d Q D w
  refine ⟨n,P,K,Q,r,v,t,g,pr,tq,G,?_,C,p',c,D,A,y,?_, v',f,q1,?_⟩
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
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.clock_consumption
