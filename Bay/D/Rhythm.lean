import Bay.D.Loop
import Bay.D.Laneway
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal
local notation "VΩ"=>VacuumSelection.Spine


-- D public offerings: strongest merged.
structure Islet (P:VΩ)(A:Armor)(i k:ℕ→ℕ):Prop where
 roads: Roadie P i k
 -- along those roads, eventually meters for all B-layouts including plug
 approach(M L:ℕ):∀ᶠs in atTop,∀ᶠr in atTop,
    let w:=port P s i k r
    A.doses w M L ∧ A.cape w ∧ Ferry P.run s (i r) (k r)
 living :∀ᶠ s:ℕ in atTop,
    Mile P s ∧
    Nonempty (Setpiece P A s i k) ∧
    ∃ d,Panel P.calibration (scale P s) d ∧ Even d

/-- universal transfer, independent of diaphragm calibration and queue election.
    d is the tick from the plane center in the units above. -/
def Pike(P:VΩ)(A:Armor)(ε:ℝ)(s:ℕ):Prop:=
  ∀ (d:ℕ), Panel P.calibration (scale P s) d →
    Cowl P.calibration (radiusB (scale P s)) d ∧
    ∀ (i k:ℕ→ℕ),Encore P s i k →∀u:Setpiece P A s i k,
       u.Cheered ε d

def Drums(P:VΩ)(A:Armor):Prop:=
 DryDock P.par ∧ Armor.Strong P A ∧
 (∃i k, Islet P A i k) ∧
 ∀ε:ℝ,0<ε→ε≤lbott A.δ/2→∀ᶠs:ℕ in atTop,Pike P A ε s

lemma drummer {P:VΩ}{A:Armor}(g:P.Register)
 (w:DryDock P.par)(a:Armor.Strong P A):Drums P A:=by
 have h:Tendsto (scale P) atTop atTop:=turnover P.par
 obtain ⟨i,k,l,y⟩:=gathers _ _ a
 refine ⟨w,a,⟨i,k,l,l.timely A a,(miles P w).and (y.and (h.eventually (panels P.calibration)))⟩,
   fun ε v e=>?_⟩
 obtain ⟨_,_,_,_,_,_,_,_,z,_,o,_⟩:=a
 obtain ⟨m,p⟩:=mists (P.par.K.top.clip) P.par.V.W.parcel _ _ A.r A.fee ε v P.par.K.width
      (zero_lt_one.trans_le P.par.V.up) z
 filter_upwards [h.eventually (styxed P.calibration m), h.eventually p] with s u t d x
 exact ⟨(u d x).right, fun _ _ b r=> r.fires_up g b (u d x) t e v o⟩

end D

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


open D
open Buffered.Afterglow.Tower
open Buffered.Afterglow.Tower.VacuumSelection.Spine
open Zephyr.Chern
universe u

/-- The actual Bay2 plus D contracts (Drums, on same Armor). -/
theorem Bay3 (Mc:ℕ)(X:TintDemand) :
 ∃ (P:VΩ)(K:P.Register)(A:Armor),
    Drums P A ∧ Hammer P Mc X ∧
    FirstLease P ∧ Post124 P.run ∧
    SprigFee P ∧ OfBay2 P ∧
    ∀(good:P.Spectrum0 3→Prop), (∀ᵐ y∂P.pillars 3,good y)→∃ y,
      good y ∧ JointTuple.{u} P K y :=by
 obtain ⟨P,K,w,l,j⟩:=flotilla.{u} Mc X
 have b:=l.two
 obtain ⟨A,M⟩:=Armor.punct b
 exact ⟨P,K,A,drummer K w M,l,l.leases,l.leases.post,SprigFee.paid P,b,j⟩

#print axioms Bay3
end YM.CF.Bay
