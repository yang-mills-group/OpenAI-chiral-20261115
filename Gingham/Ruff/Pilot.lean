import Gingham.Ruff.Boarding
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s


abbrev footing(P:Spine) (s n:ℕ):= momentm P.run (irr P n) s
lemma deckM(s n:ℕ): P.calibration.c (footing P s n)= Journey.side P.run (irr P n) s:=(terrain P.run P.large (P.run.ir (irr P n)) s)
-- notation ~p~ may refer to P
abbrev CheckIn(s n:ℕ):=boarding P a c μ d s n

/-- Matched on this reindex (with the reindexed grammar), also retaining the
    original *period* pressure, not a sew of a comparable case. -/
structure Lander
    (a c μ:ℝ)(d:ℕ)(ν:ℕ→ℕ)(F:ℕ→Fleece P.calibration):Prop extends Cosmos P a c μ d where
  grew : StrictMono ν
  loaded(s:ℕ): Pleiad P.calibration (P.run.meter.a s) (hpCost P a c) (F s)
  onDeck(s n:ℕ)(t:Leaf)(w:Scene P a c μ d s
      (irr P (ν n)) (uvv P (ν n))):
       exhibit P.run P.large s (irr P (ν n)) (F s t (some n))=w.printL t
variable {P a c μ d}
theorem touring(w:Cosmos P a c μ d):
  ∃ν F,Lander P a c μ d ν F:=by
  have hp:0≤hpCost P a c:=by
    obtain ⟨s,x,y⟩:=(clearance w 1 zero_le_one 2 le_rfl).exists
    obtain ⟨m,e⟩:= x.exists
    exact (Scene.reception e none).room.pos
  obtain ⟨v,f,p,x,t⟩:= Flora_picks (boarding P a c μ d)
     (fun _ _ h=>Scene.printL h) (deckM P)
     (fun _ _=>Scene.reception) (fun _ _=> Scene.room) hp
  exact ⟨v,f,w,p,x,fun s n l h=>t s n h l⟩

def YVoyage:Prop:=∃a c μ d ν F,Lander P a c μ d ν F
lemma navigator (v:Plumage P.run)(t:Chaplet P.run): YVoyage (P:=P):=by
 obtain ⟨a,c,m,d,e⟩:=cosmos P (Glendale_paid _ v t)
 exact ⟨a,c,m,d,touring e⟩

namespace Lander

variable {ν:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ d ν F)
include β
/-- finance along the strict reindex without changing Loom purchase. -/
lemma clearFor(E:ℝ)(t:0≤E)(l:ℕ)(r:2≤l):
  ∀ᶠ s in atTop,
   (∀ᶠ n in atTop, Scene P a c μ d s (irr P (ν n)) (uvv P (ν n))) ∧
   ∀i k,s<P.run.uv k→GlendaleInst P.run a c μ E d l s i k:=
 (clearance β.toCosmos E t l r).mono fun _ h=>⟨β.grew.tendsto_atTop.eventually h.1,h.2⟩
theorem promenade
   (s:ℕ)(word:List (Axis×ℤ))(z:ℝ):
  Bouquet (CF.Gingham.Ruff.stage word (frond P.calibration (P.run.meter.a s)))
      (‖(z:ℂ)‖ * (9*hpCost P a c)) false (Dancing word (wingtip z (F s))) ∧
    ∀n:ℕ, ∀h:Scene P a c μ d s (irr P (ν n)) (uvv P (ν n)),
    Tapestry.exhibit Y P.large s (irr P (ν n))
        (Dancing word (wingtip z (F s)) (some n)) =
      (z:ℂ) • maiden word (h.gb.brim h.bre):=by
   refine ⟨dance_pose (wing_price (β.loaded s).train _) _,?_⟩
   intro n h;rw [←h.meets]
   exact posed_receipt (F:=F s) (deckM P s _) (underlay_val P.par)
           (fun l=>β.onDeck s n l h) word z

#print axioms promenade

