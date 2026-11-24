import Mussel.Scope
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Broker.FrameZ
variable {W:Bool}{s:ℕ}(D:FrameZ P W s)(t:ℕ)(p:s ≤ t)(F:SampleDose)
variable (X:P.Test →ₗ[ℂ] ℂ)(q:Factors P.calibration X)(u:MatterWard P.calibration X)
include q u p
lemma tell (i:Cover): X (pilot P s t i D.question)=0:= by
 rw [D.fullID t i,mul_comm]
 exact P.far_price W t _ _ q (.inl u) (Broker.commute W s t i D.tailSense p) (tram s t i D.mainPin) (D.pin_commission t i p).symm
lemma foresee : X (D.batch t F)=0:=by
 unfold batch; rw [map_sum]; refine sum_eq_zero (fun i h=>?_); rw [map_smul,D.tell t p X q u i,smul_zero]
section mirror
variable {x0:P.Spectrum0 3}
-- comparator dagger? not necessarily star compatible? derive via illumination only. saleearlier. Need sensor mirror at t right.Theorem from Sensor dummy apron. define.A
lemma tellShadow (i:Cover):X (P.reflectTest 3 (pilot P s t i D.question))=0:=by
 let a:=pilot P s t i D.mainStem
 let b:=pilot P s t i D.tailZ
 let Φ:=P.reflectTest 3
 rw [D.fullID t i]
 change X (Φ (a*b))=_
 have h:Φ (a*b)=(Φ a)*(Φ b):=aureoleProduct ..
 rw [h,mul_comm]
 let Q:=fence P s t i D.S0; let C0:=fence P s t i D.T0; let T0:=(P.sensing C0 t W)
 let E:=fun j:Finset Cover=> Tower.reflectedBox (3:Axis) (0:ℤ) j
 -- build dummy variation.by induction sensing
 have hv:b∈T0:=Broker.commute W s t i D.tailSense p
 have he:Φ b∈ P.sensing (E C0) t W:=by
    let R:=P.sensing (E C0) t W
    refine Submodule.span_induction (s:=_) (p:=fun a _=> Φ a ∈ R) (fun f l=>?_) ?_ ?_ ?_ hv
    · obtain ⟨S₁,T₁,U,p,h,u,v,e⟩:=l
      have hx:=P.pin_reflect t _ _ 3 u
      exact Submodule.subset_span (show _∈_ from ⟨_,_,_,union_subset (image_subset_image (subset_union_right.trans p)) (image_subset_image (subset_union_left.trans p)), image_subset_image h,hx.symm,mirror_dressed P.calibration W S₁ T₁ U 3 0 v,P.mirror_keeps 3 _ e⟩)
    · rw [show Φ 0=0 from by simpa using P.scale_mirror 0 0 3]; exact R.zero_mem
    · intro f g _ _ h k; unfold Φ at *; rw [P.sum_mirror]; exact R.add_mem h k
    intro r f _ h; unfold Φ at *; rw [P.scale_mirror]; exact R.smul_mem _ h
 exact P.far_price W t _ _ q (.inl u) he (P.canFlip Q 3 (tram s t i D.mainPin)) (P.pin_reflect t Q C0 3 (D.pin_commission t i p)).symm
lemma foresF : X (P.reflectTest 3 (D.batch t F))=0:=by
 unfold batch; rw [map_sum,map_sum]; refine sum_eq_zero (fun i h=>?_); rw [P.scale_mirror,map_smul,D.tellShadow t p X q u i,smul_zero]
end mirror
end Broker.FrameZ
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
