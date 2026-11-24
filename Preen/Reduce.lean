import Preen.Trim
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
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
set_option maxHeartbeats 175000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Preen
variable (P:Spine) (x:P.Spectrum0 3)(s:ℕ)(o:Cover)
local notation "K"=>P.calibration
private def not_here(L:List (Trans (3:Axis)))(y:Cover)(o:Cover):Cover:=L.foldr (fun i a=>Calico.slid K i.val (y i.val) a) o
-- def P notation problem not_here inferred K.P
lemma post_accel(L:List (Trans (3:Axis)))(y:Cover)(o:Cover): P.luggage 3 L (fun i=>y i.val) (wp P s o)=wp P s (not_here P L y o):=by
 have hx(i:Axis)(q:ℤ)(o:Cover):P.shifts i q (wp P s o)=wp P s (slid K i q o):=Subtype.ext (coilT ..)
 induction L with
 | nil=>rfl
 | cons i L ih=> rw [P.ship_started,ih,hx]; rfl
/-- coordinates.P.Price -/
lemma postal_account(L:List (Trans (3:Axis)))(y:Cover)(o:Cover):
 nodeC (not_here P L y o) 3=nodeC o 3 ∧ ∀i:Trans (3:Axis), nodeC (not_here P L y o) i.val=nodeC o i.val + ruler P.par.block* Spine.massStep 3 i L (fun k=>y k.val):=by
 induction L with
 | nil=> refine ⟨rfl, fun i=>?_⟩; change nodeC o i.val=_+(ruler _)* 0; simp
 | cons i L ih=>
   let r:= not_here P L y o; have ht:not_here P (i::L) y o= Calico.slid K i.val (y i.val) r:=rfl
   refine ⟨?_,fun j=>?_⟩
   · rw [ht,bellV]; rw [if_neg (Ne.symm i.property),add_zero]; exact ih.1
   rw [ht,bellV,mass_cons,show nodeC r j.val=_ from ih.2 j]; by_cases h:i=j
   · subst j; rw [if_pos rfl,if_pos rfl]; change _+(ruler P.par.block)*_=_; ring
   rw [if_neg (Ne.symm (fun e=>h (Subtype.ext e))),if_neg h]; simp
-- reduce transverse cost to within one tick preserving price
variable (p: (P.calibration.ℓ:ℤ)+22 ≤ nodeC o (3:Axis))
abbrev driftCost(s:ℕ)(o:Cover)(p:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o (3:Axis)):ℝ := ‖paster (P.heaven 3 x) (P.wealth 3 x (P.viewF 3 x s (birthWP P o p)))‖
local notation "R"=>ruler P.par.block
lemma detross :∃ w:Cover, ∃ (h:nodeC w 3=nodeC o 3), let q:= show (P.calibration.ℓ:ℤ)+22 ≤ nodeC w (3:Axis) from p.trans_eq h.symm
 (∀i:Axis,i≠3→0 ≤nodeC w i ∧ nodeC w i ≤ (R)) ∧ driftCost P x s w q=driftCost P x s o p:=by
 let y(i:Axis):ℤ:= -(nodeC o i/(R))
 let w:= not_here P (look 3) y o
 obtain ⟨h,t⟩:=postal_account P (look 3) y o
 refine ⟨w,h,fun i g=>?_,?_⟩
 · unfold w; rw [show nodeC _ i=_ from t ⟨i,g⟩, mass_all]; unfold y; rw [mul_neg]
   have e:=Int.emod_lt_of_pos (nodeC o i) (ruler_gene P.par.block); have h0:=Int.emod_nonneg (nodeC o i) ((ruler_gene P.par.block).ne'); have he:=Int.emod_add_mul_ediv (nodeC o i) (R)
   change 0 ≤ nodeC o i + -((R)*(nodeC o i/(R))) ∧ _+ -((R)*(nodeC o i/(R))) ≤ _
   change _ ∧ nodeC o i+ -((R)*(nodeC o i/(R))) ≤ _; omega
 let Q:=P.certify 3 s (look 3) (fun i=>y i.val) (birthWP P o p)
 let ht:= P.identical_F 3 x s Q (birthWP P w (p.trans_eq h.symm)) (post_accel P s (look 3) y o)
 exact Eq.trans (congrArg (fun v:P.ColorHil 3 x=> ‖paster (P.heaven 3 x) (P.wealth 3 x v)‖) ht.symm) (conveyor P x y s _ (birthWP P o p))
#print axioms detross
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
