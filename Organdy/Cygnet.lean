import Organdy.Ballyhoo
import Organdy.Crown
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

variable {n:Side}(i:Axis)(z:ℤ)
abbrev ripple (n:Side)(i:Axis)(z:ℤ):Sweep n:= Levier.ray false (plane i z)
lemma rpt (x:Seat n): boxA (ripple n i z) x=(plane i z).anon n x:=
 stir_wrap x _ _ _ (wrap_lift _)
lemma rptField (U:Pane n):flashA (ripple n i z) U=fling i z n U:=
 stir_e (plane i z) false U
lemma rpt_inv: (ripple n i z)⁻¹ = ripple n i z:=by
  have h:ripple n i z * ripple n i z=1:=by unfold ripple; rw [Levier.ray_join,Buffered.gaugeSquare]; exact Levier.gish
  exact inv_eq_of_mul_eq_one_right h

open Hive
lemma ripples (a:FC (Single n))(p:Keys a): teen (ripple n i z) a=theta (carR i z n) a:=by
 have e:detX (plane i z).s=true:=det_t i
 refine (hono false _ _ p).trans ?_
 refine (stag_s false _ _ (pinLift i) a p (Levier.spinZ ..) ?_).trans ?_
 · rw [e];exact mirrorX i
 rw [e];rfl


variable (s t:Sweep n) (A:Support (More n)) (F:Mark n)
lemma chain (h:∀ x,Keys (F x)): voltaM t (voltaM s F)=voltaM (s*t) F:=by
 funext U
 have e:voltaF s⁻¹ (voltaF t⁻¹ U)=voltaF (s*t)⁻¹ U:=by
    unfold voltaF; dsimp only;rw [lights,lights,_root_.mul_inv_rev]
 change teen t (teen s (F _))=teen _ (F _);rw [e,yetL s t _ (h _)]
lemma rippleM (h:∀ x,Keys (F x)): voltaM (ripple n i z) F=reflMark i z F:=by
 funext U
 have e:voltaF (ripple n i z)⁻¹ U=reflFields i z U:=by
    unfold voltaF; rw [rpt_inv,rptField,rptField];rfl
 change teen _ (F _)=theta _ (F _);rw [e]; exact ripples i z _ (h _)
open Salt

lemma rippleBox : (boxA (ripple n i z)).symm = boxA (ripple n i z):=by rw [←sitU,rpt_inv]
lemma rippleY : actY (ripple n i z) A=hyphen i z A:=by
  rw [actY,map_eq_image,rippleBox]
  exact image_congr fun _ _=> rpt ..
lemma rippleYY :hyphen i z (actY s A) = actY (s*ripple n i z) A:=by
 rw [← rippleY,actY,actY,actY,Finset.map_map]
 rw [map_eq_image,map_eq_image]
 apply Finset.image_congr
 intro x _
 change (boxA (ripple n i z)).symm ((boxA s).symm x)=(boxA (s*ripple n i z)).symm x
 rw [←sitU,←sitU,←sitU,sitV,_root_.mul_inv_rev]
