import MarchC.Admission
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
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
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico
-- all-axis T
variable (P:Spine)(a:Axis)(F:ℕ)
local notation "K"=>P.calibration
local notation "R"=>ruler P.par.block
local notation "Lx"=>P.par.R.L
/- implement concurrent slides without commute proofs using luggage plus one final. -/
private def tram (L:List (Trans a))(y:Cover)(o:Cover):Cover:=L.foldr (fun i u=>Calico.slid K i.val (y i.val) u) o
lemma post_axis(s:ℕ)(L:List (Trans a))(y:Cover)(o:Cover): P.luggage a L (fun i=>y i.val) (wp P s o)=wp P s (tram P a L y o):=by
 have hx(i:Axis)(q:ℤ)(o:Cover):P.shifts i q (wp P s o)=wp P s (slid K i q o):=Subtype.ext (coilT ..)
 induction L with
 | nil=>rfl
 | cons i L ih=> rw [P.ship_started,ih,hx]; rfl
/-- coordinates.P.Price -/
lemma postal_axis(L:List (Trans a))(y:Cover)(o:Cover):
 nodeC (tram P a L y o) a=nodeC o a ∧ ∀i:Trans a, nodeC (tram P a L y o) i.val=nodeC o i.val + ruler P.par.block* Spine.massStep a i L (fun k=>y k.val):=by
 induction L with
 | nil=> refine ⟨rfl, fun i=>?_⟩; change nodeC o i.val=_+(ruler _)* 0; simp
 | cons i L ih=>
   let r:= tram P a L y o; have ht:tram P a (i::L) y o= Calico.slid K i.val (y i.val) r:=rfl
   refine ⟨?_,fun j=>?_⟩
   · rw [ht,bellV]; rw [if_neg (Ne.symm i.property),add_zero]; exact ih.1
   rw [ht,bellV,mass_cons,show nodeC r j.val=_ from ih.2 j]; by_cases h:i=j
   · subst j; rw [if_pos rfl,if_pos rfl]; change _+(ruler P.par.block)*_=_; ring
   rw [if_neg (Ne.symm (fun e=>h (Subtype.ext e))),if_neg h]; simp
-- travelling as 3 by definition.A nonissue.
def metro (y:Cover)(o:Cover):Cover:=tram P 3 (look 3) y (slid K 3 (y 3) o)
private lemma metro_compute(y o:Cover): nodeC (tram P a (look a) y (slid K a (y a) o)) = fun i=>nodeC o i + R*y i :=by
 ext i; have hv:=postal_axis P a (look a) y (slid K a (y a) o); by_cases h:i=a; subst a; rw [hv.1,bellV, if_pos rfl]; rfl
 rw [show nodeC _ i =_ from hv.2 ⟨i,h⟩, mass_all,bellV,if_neg h,add_zero]
lemma metro_cal(y o:Cover)(i:Axis): nodeC (metro P y o) i=nodeC o i+R*y i:= congrFun (metro_compute P 3 y o) i
lemma metro_axis(y o:Cover): metro P y o=tram P a (look a) y (slid K a (y a) o):= Calico.node_dC (funext fun i=> (metro_cal P y o i).trans (congrFun (metro_compute P a y o) i).symm)
lemma cast_price(s:ℕ)(y o:Cover) : P.luggage a (look a) (fun i=>y i.val) (P.shifts a (y a) (wp P s o))=wp P s (metro P y o):=by
 rw [show P.shifts _ _ (wp P s o)=_ from (Subtype.ext (coilT ..) : _= wp P s (slid K a (y a) o)),post_axis,metro_axis P a]
private lemma dec_t (x:P.Spectrum0 a)(u:P.ColorHil a x)(v:P.ManyF a x): inner ℂ (P.wealth a x u) v=inner ℂ u (P.enter a x v):=by
 rw [←ContinuousLinearMap.adjoint_inner_right (P.wealth a x),P.bank_star]; rfl
lemma trek_axis (x:P.Spectrum0 a)(y:P.VMark)(v:P.ColorHil a x): P.wealth a x (P.truck a x y v)= P.cartage a x (P.laysM y) (P.wealth a x v):=by
 apply ext_inner_right ℂ
 intro b
 have hg:=P.cart_reverses a x (P.laysM y)
 rw [dec_t,P.truck_inner, P.cart_and,P.lays_neg, ← ContinuousLinearMap.adjoint_inner_right,hg,dec_t]
local notation "ξ" x:max s:max p:max=>P.wealth a x (P.viewF a x s p)
lemma casts (s:ℕ) (x:P.Spectrum0 a)(y:Cover){f:P.Test}(p:P.birthF a s f): ξ x s (P.certify a s (look a) (fun i=>y i.val) p)=P.cartage a x (P.gridSpot s y) (ξ x s p):= (congrArg (P.wealth a x) (show P.viewF a x s (P.certify a s (look a) (fun i=>y i.val) p)= P.truck a x (P.vtile s y) (P.viewF a x s p) from P.ship_ideal ..)).trans (trek_axis P a x (P.vtile s y) (P.viewF a x s p))
lemma travelS(s:ℕ)(o w:Cover)(y:Cover)(b:ℕ)(q:(b:ℤ)=y a)(h:metro P y o=w)(x:P.Spectrum0 a)(p:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o a)(g:(P.calibration.ℓ:ℤ)+22 ≤ nodeC w a):
 let d:=P.gridSpot s y
 ξ x s (bornP P a s w g)= P.cartage a x d ((P.seasons a x).E (d a).toNNReal (ξ x s (bornP P a s o p))):=by
 intro d; let D:=P.passesLater a s b (bornP P a s o p); let W:=P.certify a s (look a) (fun i=>y i.val) D
 have he:= P.identical_F a x s W (bornP P a s w g) ((show P.luggage a (look a) _ (P.shifts a (b:ℤ) (wp P s o))= _ from by rw [q,cast_price,h]):_= wp P s w)
 let t:=whenly (timeMesh P.par) s b
 have hk0:t=(d a).toNNReal:= NNReal.eq (by
    have hz:(t:ℝ)=d a:= (natural_time ..).symm.trans (show bell (timeMesh P.par) s (b:ℤ)=d a from by rw [q]; rfl)
    rw [←hz,Real.toNNReal_coe])
 have hz:= (congrArg (P.wealth a x) (P.releasedLater a x s b (bornP P a s o p))).trans ((P.bankHeat a x t _).trans (congrArg (fun j:ℝ≥0=> (P.seasons a x).E j (ξ x s (bornP P a s o p))) hk0))
 exact (congrArg (P.wealth a x) he.symm).trans ((casts P a s x y D).trans (congrArg (P.cartage a x (P.gridSpot s y)) hz))
#print axioms travelS
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
