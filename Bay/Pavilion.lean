import Bay.D.Rhythm
import Bay.C.Race
import Bay.E.Attic
import SU5SatinMarkedCurrentNovember7
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


namespace C
/-- Merging the A-B, chiral plane (D), C upgrades and Silk, for public use. -/
def Extravaganza(P:VΩ)(A:Armor)(M:ℕ)(X:TintDemand):Prop:=
 ∃(b:Rib P), TicketF P b M X ∧ Edge P (SceneF P b M) ∧
 ∃ D r T e,let g:=Outfit.mk A.a A.c A.b A.F (tabW P) D r T e
 Helm P g ∧ Dry P (fun w=>w.Rig g.a g.c g.m)

theorem extra {P:VΩ}{A:Armor}{M:ℕ}{X:TintDemand}
   (d:Armor.Strong P A)(p:Hammer P M X):Extravaganza P A M X:=by
 obtain ⟨b,x,y⟩:= fRib p
 obtain ⟨l,_,_,_,_,f,q,j,_,_,_,z⟩:=d
 obtain ⟨D,r,T,e,w⟩:=pattern A.F f q j l
 refine ⟨b,x,y,D,r,T,e,w,?_⟩
 apply dryMono (z 1 1).2
 intro v a h
 have b':tabW v.P=tabW P:=congrArg tabW a
 change v.Rig A.a A.c (tabW P)
 rw[←b']
 exact h.1.old.cradle.1

lemma steam {P:VΩ}{i k:ℕ→ℕ}
 (d:Roadie P i k){f:ℕ→ℕ→ℕ→Prop}
 (h: Edge P f):
 ∀ᶠ s in atTop,∀ᶠ r in atTop,
    f s (i r) (k r) ∧ Buffered.Afterglow.Journey.Ferry P.run (s+1) (i r) (k r):=by

 filter_upwards [h] with s p
 filter_upwards [d.rowing.reaches (s+1),d.rowing.growing.eventually p,d.rowing.cooling.eventually
   (P.run.uv_grows.tendsto_atTop.eventually_gt_atTop (s+1))]
   with r y w v
 exact ⟨w _ v,y⟩

end C
universe u

/-- Public application. -/
theorem Bay4 (Mc:ℕ)(X:TintDemand) :
 ∃ (P:VΩ)(K:P.Register)(A:Armor),
    Silk.PortDual P A ∧ C.Extravaganza P A Mc X ∧
    Drums P A ∧ Hammer P Mc X ∧
    FirstLease P ∧ Post124 P.run ∧
    SprigFee P ∧ OfBay2 P ∧
    ∀(good:P.Spectrum0 3→Prop), (∀ᵐ y∂P.pillars 3,good y)→∃ y,
      good y ∧ JointTuple.{u} P K y :=by
 obtain ⟨P,K,A,d,h,f⟩:=Bay3.{u} Mc X
 exact ⟨P,K,A,Silk.dual d.2.1,C.extra d.2.1 h,d,h,f⟩

end YM.CF.Bay
