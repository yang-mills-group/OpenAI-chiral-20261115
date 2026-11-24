import Gingham.Ruff.Pilot
import Gingham.Ruff.Veronica
import Gingham.Ruff.Trellis
import Gingham.Eaves
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

variable {a c μ d s}
  {ν:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ d ν F)
  (s:ℕ)
variable {P}
set_option linter.unusedSectionVars false

/-- Finite or growing arrays allowed. Y128 charged pose inputs and even accessories. -/
inductive Letter(P:Spine)
| summon (z : ℝ) (word:List (Axis×ℤ))
| accessory (S:Finset Cover) (X:Cluster P.calibration)
   (deck: BQueue S (fun n=>X (some n)) (X none))
namespace Letter

def scope:Letter P→Finset Cover
| .summon _ w=>CF.Gingham.Ruff.stage w (frond P.calibration (P.run.meter.a s))
| .accessory t _ _ =>t

def bill (C:ℕ→Fleece P.calibration) : Letter P→Cluster P.calibration
| .summon z w=>Dancing w (wingtip z (C s))
| .accessory _ X _=>X
include β in
lemma admission (X:Letter P):
    BQueue (scope s X) (fun n=>bill s F X (some n)) (bill s F X none):=by
   cases X with
   | summon z w=>exact (β.promenade s w z).1.check
   | accessory S X p=>exact p

def width:List (Letter P) → Finset Cover
| []=>∅
| X::l=>scope s X ∪ width l


def cost (F:ℕ→Fleece P.calibration) (l:List (Letter P))
        (o:Option ℕ):Family P.calibration:=(l.map fun A=>bill s F A o).prod

include β
lemma admitts (l:List (Letter P)):
  BQueue (width s l) (fun n=>cost s F l (some n)) (cost s F l none):=by
   induction l with
   | nil=>
      exact BQueue.stay InTest.one zero_lt_one
        (show pay (1:Family P.calibration) 1 from fun _ _=> norm_one.le)
   | cons x l ih=>
      exact (admission β s x).multiply ih

lemma accommodated(l:List (Letter P))(o):
   InTest K true (width s l) false (cost s F l o):=by
   cases o
   · exact (admitts β s l).landing
   exact (admitts β s l).whereTo _

def guest(l:List (Letter P))(o:Option ℕ):P.Test:=⟨cost s F l o,
  (marque K).mpr (aux_test (accommodated β s l o))⟩

end Letter

-- no Sedge object file; redo sharp_coffee specializing here
lemma swell {f:ℕ→Family P.calibration}{g}{S}
   (h:BQueue S f g)(v: Tendsto ν atTop atTop):
   Tendsto (fun n=>Journey.sharp P.run P.large s (irr P (ν n))
      (uvv P (ν n)) (f n)) atTop (𝓝 (P.E s g)):=by
 obtain ⟨C₀,b₀,V'⟩:=P.history.implements s S
 let D:= toll Y P.large s S
 obtain ⟨D',h'⟩:= toll_pays Y P.large s S
 obtain ⟨C,c,hx,v'⟩:= h.bdd
 have hd:0 ≤ D:=D'


 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 let u:= ε/(D+C+1)
 have he:0 < u:= by unfold u; positivity
 filter_upwards [v.eventually (V' u he),v.eventually (P.history.finance s),h.saved u he,
  v.eventually ((rising_k P).tendsto_atTop.eventually h')] with n a b t h'
 rw [dist_eq_norm]
 let X:= Journey.sharp Y P.large s (irr P (ν n)) (uvv P (ν n))
 refine lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub (X (f n)) (X g) _)
     ((add_le_add (b:=D*u) (d:=u*C) ?_ (a g h.landing C hx).2.2.2.2.1).trans_lt ?_)
 · unfold X
   rw [←sharp_sub Y P.large _ (aux_test (h.whereTo _)) (aux_test h.landing)
      (show Ferry Y s (irr P (ν n)) (uvv P (ν n)) from b)]
   exact h' _ b.depth _ (InTest.subOp (h.whereTo _) h.landing) _ (t _)
 have hp:u*(D+C+1)=ε:=div_mul_cancel₀ _ (by positivity)
 nlinarith

include β
lemma ships (l:List (Letter P)):
 Tendsto (fun n=>rawE P s (ν n) (Letter.guest β s l (some n))) atTop
       (𝓝 (P.E s (Letter.cost s F l none))):=
    swell s (Letter.admitts β s l) β.grew.tendsto_atTop

#print axioms ships

