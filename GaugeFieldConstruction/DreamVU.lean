import GaugeFieldConstruction.LensBarrierVU
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z B:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
local notation "S_A"=> SurfRimL A
local notation "S_Ζ"=> SurfRimL Z
variable (W:NSF.Boundary.Surface (SurfRimL A)) (F:NSF.Boundary.Waves (SurfRimL A))(N:W.Aurora drapeL)
local notation "M_ν" => H.TinCanL
local notation "J_ν" => H.AsterBackL
local notation "Τh" => TouchMΛ H (N:=N)
local notation "$ΐ"=> RespiteΛL H (N:=N)
local notation "δ_" a:max=> -(ΦshiftΛ (basis a))
local notation "Τ_Φ" => CoffΜΛ H p
open YM.Boundary (Joint.push Joint.materialize)
-- formal Ward on translation as analytic contour generating distribution δ.W products. Include determination meaning.
-- bundle Lighting & Terra pure attach
local notation "Ξ_A"=>SurfCheckL.HeightsKL p H
local notation "Ξ_G"=> SurfCheckL.VesselPL p H
variable (s:(SurfRimL A).RealSpin)
variable {B0:NSF.Boundary.LRoom (SurfRimL Z) timeAxis} {Bκ:Small (SurfRimL A) B0}
variable (d:PredictionL W F (SurfCheckL.HeightsKL p H) (H.AsterBackL) Bκ (SurfCheckL.VesselPL p H) s)
open Metric
include G d
-- starts Curry. point-value W on pair.Perturb x
-- Let V label. Pane chosen simultaneously proof. Logo.Mon.
variable (wX:N.FullBody F)
include wX
lemma ResolveVU (v:Fin 2→ΧiMars)(x:Points 2)(p':x∈conf 2)(u: x∈Gate2VU.gap)(e:readings x=0):∃ (U:Set (Points 2))(R: Points 2→ℂ), IsOpen U∧ x∈U ∧ ContinuousOn R U ∧ R x= Z 2 x v∧ ∀ f:Joint 2, HasCompactSupport ⇑f→ tsupport ⇑f⊆ U→ W.W 2 (M_ν ∘ v) f=∫ y,R y*f y:=by
 have hp':=d.labels ▸ d.course.letters -- tune
 obtain ⟨M'⟩:= StarsLampVU wX (M:=H.RiseFrameL) hp' H.PlannerL.toSymmetric (H.RiseKnownL _) d.inlet (M_ν ∘ v)
 obtain ⟨U,h,hx,q,g⟩:= clearVU wX M' d.inlet.habitat x u
 refine ⟨U,_,h,hx,q,akinVU e (M_ν ∘ v) M' u _ ((G.sm v).continuousOn.continuousAt ((conf_open _).mem_nhds p')) ?_,g⟩
 intro i t'; exact ΥLiveΛL H G d.inlet.heat wX _ t'
local notation "qVU"=> H.TinCanL
lemma BarrierOneVU (V: Fin 1 → ΧiMars)(f: Joint 1)(x:Points 1): W.W 1 (qVU ∘ V) f = Z 1 x V * (∫ i:Points 1,f i):=by
 let k:= Z 1 x V; let T:=qVU ∘ V
 have he (z:Full 1) (u:z∈ tube 1):N.emit T z=k:=by -- analytic Lane
    apply sub_eq_zero.mp
    refine ΛLaneL (X:=fun z=> N.emit T z-k) (fun y v=> ((wX.hol 1 _) y v).sub analyticAt_const) ?_ u
    intro i hi; change N.emit T (wickSlice _ i)-k=0; apply sub_eq_zero.mpr; rw [show N.emit T (wickSlice _ i)= Z 1 i V from ΥLiveΛL H G d.inlet.heat wX _ hi]; have hy:= G.even (x 0-i 0) V i (ΜConfΛL hi); rw [show NSF.Points.across (x 0-i 0) i=x from ?_] at hy; exact hy.symm; apply PiLp.ext; intro j; fin_cases j; first| exact add_sub_cancel ..| change i 0+(x 0-i 0)=_; abel
 haveI:= awaits (light 1)
 refine tendsto_nhds_unique_of_eventuallyEq (d.inlet.joints.corner _ _ f) tendsto_const_nhds ?_
 filter_upwards[self_mem_nhdsWithin] with t q
 change (∫ i,F.restricted T t i*f i)=k* _; simp_rw [← wX.pure 1 T _ t q, he _ (roseΛ (etched q) _), integral_const_mul]
#print axioms ResolveVU
#print axioms BarrierOneVU
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
