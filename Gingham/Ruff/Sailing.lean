import Gingham.Ruff.AtSea
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

variable {P a c μ d s}
    {ν:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ d ν F)
set_option linter.unusedSectionVars false
open Footlight

abbrev Sailing (P:Spine)(a c μ:ℝ)(d:ℕ)(ν:ℕ→ℕ)(s n:ℕ):=
    Scene P a c μ d s (irr P (ν n)) (uvv P (ν n))
variable {n:ℕ}(α:Sailing P a c μ d ν s n)

local notation "iₙ"=>irr P (ν n)
local notation "kₙ"=>uvv P (ν n)
local notation "N"=>Journey.side P.run iₙ s
local notation "Rₙ"=>RootBook P.run iₙ kₙ s
local notation "Aₙ"=> (P.run.voyage iₙ).CapeT s
local notation "Δ"=>denZ Rₙ P.par.U Aₙ
local notation "𝒢"=>Scree.city N
local notation "χ"=>partitionZ Rₙ P.par.U Aₙ
local notation "𝒳"=>fun f:Family P.calibration=>exhibit Y P.large s iₙ f

namespace Letter
def takes(x:Orbit N): Letter P→ Footlight N
  | .summon z w=>scale (α.gb.signedActor α.bre α.gears.tag w x) z
  | .accessory S X p=> extra (Satin.region S N) ((𝒳) (X (some n)) (drawn Aₙ x))
    (((exhibited _ _ _ _ _ (p.whereTo n)).allV (drawn Aₙ x)).sector)

def anchorage (_α:Sailing P a c μ d ν s n) : Letter P→ Support (More N)
  | .summon _ w=> GarlandBook.Pall (Rₙ).p (maidS w) N
  | .accessory S _ _=>Satin.region S N

include β in
lemma peacocking (L:Letter P)(x:Orbit N):
    (takes α x L).plot=anchorage α L ∧
    (takes α x L).physical=(𝒳) (bill s F L (some n)) (drawn Aₙ x):=by
  cases L with
  | accessory=>exact ⟨rfl,rfl⟩
  | summon z w=>
     refine ⟨rfl,?_⟩
     change (z:ℂ) • (α.gb.signedActor α.bre α.gears.tag w x).physical =
       exhibit Y _ s _ (Dancing w (wingtip z (F s)) (some n)) _
     rw [(β.promenade s w z).2 n α, α.gb.crew_1 α.bre α.gears.tag w x (Aₙ x)]
     rfl

def Ocean (A B:Letter P): Prop:=
    Disjoint (anchorage α A) (anchorage α B)

include β in lemma troupe_S
 (l:List (Letter P))(x:Orbit N)(e:l.Pairwise (Ocean α)):
   List.Pairwise Space (l.map (takes α x)):=by
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ e
  intro A B h
  rw [Space,(peacocking β α A _).1,(peacocking β α B _).1]
  exact h

include β in lemma troupe_L (l:List (Letter P))(x:Orbit N):
    (𝒳) (cost s F l (some n)) (drawn Aₙ x) =
    libretto physical (l.map (takes α x)):=by
 induction l with
 | nil=>
      change exhibit Y _ s _ 1 _=1
      rw [Tapestry.actual_one];rfl
 | cons A l ih=>
      change exhibit Y _ s _ (bill s F A (some n)*cost s F l (some n)) _
         =(takes α x A).physical * libretto physical (l.map (takes α x))
      rw [actual_product,(peacocking β α A _).2,←ih];rfl

def stunt(l:List (Letter P))(x:Orbit N):FC (Single N):=
   libretto primed (l.map (takes α x))

def stuntPrice(l:List (Letter P))(x:Orbit N):ℂ:=
   beamZ N (acts (stunt α l x) (Δ x))

/-- Anytime assembled: one raw pricing integral, never drop division by partition. -/
def oceanPrice(l:List (Letter P)):ℂ:=(∫x, stuntPrice α l x ∂𝒢)/χ


include β in
theorem shoal(l:List (Letter P))
   (q:Ferry Y s iₙ kₙ)
   (e:l.Pairwise (Ocean α)):
 Integrable (stuntPrice α l) 𝒢 ∧ χ ≠ 0 ∧
 oceanPrice α l=Journey.sharp Y P.large s iₙ kₙ (cost s F l (some n)):=by
 have h:=Journey.paid Y P.large s (p:=q) (aux_test (accommodated β s l (some n)))
 let v:=cost s F l (some n)
 let V:=Journey.send Y P.large iₙ s (v (momentm Y iₙ s))
 have hp:(fun x=> beamZ N (acts (V (drawn Aₙ x)) (Δ x)))=stuntPrice α l :=by
   funext x
   unfold V v
   rw [←present_send]
   change beamZ N (acts ((𝒳) (cost s F l (some n)) (drawn Aₙ x)) (Δ x))=_
   rw [troupe_L β α l x]
   exact onstage _ (troupe_S β α l x e) (Δ x)
 -- rewrite through hp in paid type; i k width Rₙ defeq
 rw [oceanPrice,←hp]
 exact ⟨h.1,h.2.1,h.2.2.symm⟩

#print axioms shoal

