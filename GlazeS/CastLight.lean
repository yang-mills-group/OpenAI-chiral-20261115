import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
variable (P:Spine)(F:SampleDose)(s t:ℕ)
-- Dose transported for independent-placement sums. y is stencil's *own* position in the fixed v coordinates of chart requires c.
def dealt(p:Vantage):SampleDose where
 val:=fun x=>F.val (x+p)
 smooth:= F.smooth.comp (by fun_prop)
 budget:= F.budget.comp_homeomorph (Homeomorph.addRight p)
lemma pay_shift(p:Vantage){x:Vantage}(h:x∈ tsupport (dealt F p).val): x+p∈tsupport F.val:=by
 rw [show tsupport (dealt F p).val= (Homeomorph.addRight p) ⁻¹' tsupport F.val from ?_] at h; exact h
 exact ((Homeomorph.addRight p).preimage_closure (Function.support F.val)).symm
variable {g:P.Test}(x:P.Spectrum0 3)(w:P.birthF 3 s g)(p:s≤t)
local notation "T"=> P.physicalEnergy 3 x
local notation "E" t:max=> (T).E t
local notation "A"=> P.viewF 3 x s w
local notation "M"=>timeMesh P.par
def gibbert (P:Spine)(s t:ℕ)(g:P.Test)(z:Cover):P.Test:= P.luggage 3 (look 3) (fun i=>z (i:Axis)) (P.shifts 3 (z 3) (P.conveying s (t-s) g))
include w p
lemma fill_gossip (z:Cover)(v:0 ≤ z 3):∃ h:P.birthF 3 t (gibbert P s t g z), P.viewF 3 x t h=P.truck 3 x (P.vtile t z) ((E (Real.toNNReal (P.meshPose t z 3))) A):=by
 let n:ℕ:= (z 3).toNat; have hn:(n:ℤ)=z 3:=Int.toNat_of_nonneg v
 unfold gibbert; rw [←hn]
 let R:= P.rig 3 s t w p; let q:= P.passesLater 3 t n R
 refine ⟨P.certify 3 t (look 3) (fun i=> z i.val) q, ?_⟩
 rw [P.ship_ideal _ _ _ (look 3) _ q, P.releasedLater _ _ _ n R, P.view_rig _ _ _ t w]
 change _= (P.voyageF 3 x).raw (look 3) (fun i=> MeshClock.notch M t (z i.val)) ((E (Real.toNNReal (bell M t (z 3)))) A); rw [←hn,show (bell M t (n:ℤ)).toNNReal = whenly M t n from (congrArg Real.toNNReal (natural_time ..)).trans Real.toNNReal_coe]
 all_goals first |exact p|assumption
#print axioms fill_gossip
#check F
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
