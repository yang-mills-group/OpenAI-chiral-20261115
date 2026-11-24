import YM.SU5.Assay.TwoColor
import YM.SU5.Assay.BeamRide
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
/-!
# Actual pure marginal prices vanish termwise on charged assignments.
Both on output decompositions (Beam even after refinement), and finer
posing of native assignments to pure factors priced via separate advancement.
No assumption about factorization holding in the latter prices after
advancement, or purity preserved across heights. Costs before the grid and
width limits.
-/
lemma Beam.present (p:f∈P.Beam s D W):∃ l, Presented K W D f l:=by
  apply TwoColor.list
  exact Submodule.span_le.mpr (show _ from fun x h=>by
    obtain ⟨S,T,V,U,a,b,k,l,u,v,h,z,c,d,rfl⟩:=h
    exact TwoColor.dressed_visit K W S T D U V z c d k l u (P.pin_disjoint _ _ _ v) (P.pin_disjoint _ _ _ h)) p
variable (P) in
def GFlame (f:P.Test) : Prop:=∃ (q:ℂ)(r:GVertex),q≠1∧pennant K r f=q•f
lemma pure_flames (p:PureSplit K W S f g) : P.GFlame f ∧ P.GFlame g:=by
 obtain ⟨_,_,_,_,k,a,b⟩:=p
 exact ⟨⟨_,_,inv_ne_one.mpr (pname_ne W),a⟩,_,_,pname_ne W,b⟩

namespace GFlame
lemma value (p:P.GFlame f)(j:Axis)(s:ℕ)(x:P.Spectrum0 j): P.singleState j s x f=0:=by
 obtain ⟨q,r,h,w⟩:=p; let E:=P.singleState j s x
 have e : E (pennant K r f)=E f:=by unfold E;rw [P.single_state,P.single_state,P.reading_gauge]
 rw [w,map_smul,smul_eq_mul] at e
 by_contra u; exact h (mul_right_cancel₀ u (e.trans (one_mul ..).symm))
lemma beside (p:P.GFlame f)(u:f∈bay K S true)(q:g∈bay K T true)(d:Disjoint S T): P.GFlame (f*g):=by
 obtain ⟨c,r,h,w⟩:=p
 let l:GVertex:=fun i=> if i∈S then r i else 1
 have z:pennant K l f=pennant K r f:=appointed K S l _ _
   (fun m x w=> pennantTrace K S r u m x (fun i v=> (w i v).trans (if_pos v))) (pennantLocal K S r u)
 exact ⟨_,_,h,by rw [map_mul (pennant K l) f g,z,w,fixed_local K T l (fun i v=> if_neg fun a=>Finset.disjoint_left.mp d a v) q,smul_mul_assoc]⟩

lemma parent_onto (P:Spine): Surjective (parentGauge P.par):=by
 let L:=P.par.R.L.val; let k(x:Cover):= L•x
 have h:Function.Injective k:= nsmul_right_injective P.par.R.L.property.ne'
 intro g; exact ⟨Function.extend k g 1,funext fun i=> h.extend_apply g 1 i⟩
lemma promote (R:P.Register)(v:P.GFlame f)(s:ℕ): P.GFlame (P.promote s R f):=by
 obtain ⟨q,r,h,w⟩:=v
 obtain ⟨k,rfl⟩:=parent_onto P r
 exact ⟨_,_,h,by rw [←P.gauge_promotion s R k f,w,map_smul]⟩
lemma ascend (R:P.Register)(v:P.GFlame f)(s n:ℕ): P.GFlame (P.conveying s n f):=by
 induction n with
 | zero=> exact v
 | succ n h=>
    rw [show P.conveying s (n+1) f= P.promote (s+n) R (P.conveying s n f) from Subtype.ext (P.promotes_to (s+n) R (P.conveying s n f)).symm]
    exact promote R h _
lemma shift (v:P.GFlame f)(j:Axis)(n:ℤ): P.GFlame (P.shifts j n f):=by
 obtain ⟨q,r,h,w⟩:=v
 obtain ⟨k,u⟩:= P.spins_shift j n r f
 rw [w,map_smul] at u; exact ⟨_,_,h,u⟩
lemma jet (v:P.GFlame f)(l:List Axis)(o:Cover): P.GFlame (P.cruise l o f):=by
 induction l with
 | nil=> exact v
 | cons j l h=> rw [P.cruise_step,AlgHom.comp_apply]; exact h.shift _ _
lemma mirror (v:P.GFlame f)(j:Axis): P.GFlame (P.reflectTest j f):=by
 obtain ⟨q,r,h,w⟩:=v
 refine ⟨star q,reflectGauge j 0 r,fun u=> h (star_injective (u.trans (star_one ..).symm)),?_⟩
 unfold reflectTest;rw [pennantReflect,gauges_of_mirror,w]; exact P.scale_mirror ..
end GFlame

-- Posing a loose assignment with aperture prices from B
variable (P) in
def sParcel (t:ℕ)(B:P.Apron)(f:P.Test)(r:Cover): P.Test:=P.chartAll r (P.conveying B.s (t-B.s) f)
variable (B:P.Apron)
lemma sParcel.atPlot (t:ℕ)(h:f∈bay K B.S true)(r:Cover): P.sParcel t B f r∈bay K (P.plotSet t B r) true:=
 P.place_test _ Vacancy.ordinate r (woven_bay B.s h _)
lemma sParcel.flame (t:ℕ)(v:P.GFlame f)(r:Cover)(R:P.Register):P.GFlame (P.sParcel t B f r):=
 (v.ascend R B.s _).jet Vacancy.ordinate r
lemma sParcel.worth (t:ℕ)(v:P.GFlame f)(r:Cover)(R:P.Register)(j:Axis)(x:P.Spectrum0 j):
     P.singleState j t x (P.sParcel t B f r)=0:= (flame B t v r R).value j t x
lemma sParcel.together (C:P.Apron)(p:B.s≤t)(h:C.s≤t)(u:f∈bay K B.S true)(q:g∈bay K C.S true)(v:P.GFlame f)(r n:Cover)
   (w:Disjoint (P.Aperture B (P.meshPose t r)) (P.Aperture C (P.meshPose t n)))(R:P.Register)(j:Axis)(x:P.Spectrum0 j):
    P.singleState j t x (P.sParcel t B f r*P.sParcel t C g n)=0:=
  (GFlame.beside (flame B t v r R) (atPlot B t u r) (atPlot C t q n)
   (P.pin_disjoint _ _ _ (w.mono (P.inside_now t r B p) (P.inside_now t n C h)))).value j t x
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
