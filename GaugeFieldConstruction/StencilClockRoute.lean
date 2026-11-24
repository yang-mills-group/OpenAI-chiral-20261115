import GaugeFieldConstruction.StencilPanCore
import GaugeFieldConstruction.NereidΛL
import YM.Heat.Lift
/-!
# Translation and full PVM from WordLift. Coordinates paid by passing through
 the Carton in `Panorama`. Include retention even when Leb & unpad narration matters.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxRecDepth 4000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.PanSt
open Function Set Filter MeasureTheory Submodule
open NSF.Boundary
open YM.Boundary (Joint Test4)
open Spectral Mink
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ComplexConjugate Classical
variable {H: Hilbert}{S: OS.Semigroup H timeAxis}{D:Submodule ℂ H}
variable {G:NSF.Gauge} {L':NSF.Register G} {A':NSF.Table L'} {W:NSF.Boundary.Surface A'} {R:A'.Rotation}{j:A'.RealSpin}
variable {Row:Sentence A' → D}{T:Letter A' → Module.End ℂ D}
variable (X:Wightman A') (u:WordLiftSt X (H:=H) D Row T)(h:X.Realizes (W:=W) R j)
local notation "W#"=> X.operators
include h
private lemma shiftRowsSt (z:E4)(L:Sentence A') : X.action.V (Poincare.translation z) ((W#).vector L)=(W#).vector (L.map fun i=> (i.1,YM.Boundary.Probe.ahead z i.2)):=by -- check YM.Boundary.Probe.ahead name
 induction L with
 | nil=> exact h.covariance.vacuum (Poincare.translation z)
 | cons f L ih=>
    rw [List.map_cons]; let Y(f:Test4):=(YM.Boundary.Probe.ahead z f); let M:= LocalActΛL X h (Poincare.translation z); let v:=(W#).evaluates L; let k:L.length=L.length:=rfl
    have he(f:Test4): YM.Boundary.Joint.push (Poincare.translation z) f = Y f:=by ext1 x; simp [Y,Poincare.translation]
    let r:= (fun i:Letter A'=> (i.1,Y i.2)); have hx:M v=(W#).evaluates (L.map r):= Subtype.ext ih
    change X.action.V _ ((W#).field f.1 f.2 _).1=((W#).field f.1 (Y _) _).1; rw[h.covariance.covariance, show X.spin.rail (Poincare.translation z).Λ f.1= f.1 from h.letters.identity _,he]; change ((W#).field f.1 (Y _) (M v)).1= _; rw[hx]
variable (p:∀ (z:E4)(L:Sentence A'), S.unit.translation z (Row L).1=(Row (L.map fun i=> (i.1,YM.Boundary.Probe.ahead z i.2))).1)
include p u
lemma travelUnitSt (z:E4)(x: X.operators.H) : S.unit.translation z (u.rays x)= u.rays (X.action.orbit.translation z x):=by
 have H:(S.unit.translation z).comp (u.rays.toContinuousLinearMap)=(u.rays.toContinuousLinearMap).comp (X.action.orbit.translation z):=by
    apply ContinuousLinearMap.ext_on (R₁:=ℂ) (s:= Set.range (W#).vector); · rw [← h.total.cyclic]; exact h.total.everywhere
    rintro x ⟨L,rfl⟩; change S.unit.translation z (u.rays _) = u.rays (X.action.V (Poincare.translation z) _); rw [u.onWord, shiftRowsSt X h, u.onWord]; exact p z L
 exact DFunLike.congr_fun H _
lemma allowanceL3St (x: X.operators.H) : S.ℚmeasure.diagonal (u.rays x) = X.momentum.diagonal x:=by
 apply Measure.ext_of_charFun; funext z; rw [S.joint,h.spectral, travelUnitSt X u h p, u.rays.inner_map_map]
omit p u h
private lemma fullPathSt {H:Hilbert}{V:Type*}[MeasurableSpace V](X:PVM H V)(s:Set V)(w:MeasurableSet s)(z:H)(p:‖X.region s z‖^2=‖z‖^2) : X.region s z=z:= by
 let Z:= X.region s
 have hw: inner ℂ z (Z z)=inner ℂ z z:=by rw [← X.at_pair w,X.same w,p]; rw [inner_self_eq_norm_sq_to_K]; norm_cast
 have hz: inner ℂ (Z z) z=inner ℂ z z:= by
    calc _ = inner ℂ z (Z.adjoint z):= (ContinuousLinearMap.adjoint_inner_right ..).symm
         _= _:=by rw [show Z.adjoint=Z from X.real w,hw]
 have h₀:inner ℂ (Z z) (Z z)=inner ℂ z z:= by rw [←hw]; exact (by rw [inner_self_eq_norm_sq_to_K, ← X.at_pair w,X.same w]; norm_cast)
 apply sub_eq_zero.mp; apply inner_self_eq_zero (𝕜:=ℂ)|>.1; rw [inner_sub_left,inner_sub_right,inner_sub_right,h₀,hz,hw]; simp
include p u h
lemma travelRegionSt (s:Set E4)(w:MeasurableSet s)(x: X.operators.H) : S.ℚmeasure.region s (u.rays x)=u.rays (X.momentum.region s x):=by
 let T':= S.ℚmeasure; let P:= X.momentum; let Z:= P.region s x
 have hh(v:(W#).H): ‖T'.region s (u.rays v)‖^2= ‖u.rays (P.region s v)‖^2:=by unfold T' P; rw [← S.ℚmeasure.same w,allowanceL3St X u h p,u.rays.norm_map,← X.momentum.same w]
 have hv:T'.region s (u.rays Z)=u.rays Z:= fullPathSt _ _ w _ (by rw[hh, show P.region s Z=Z from P.idempotent w x])
 have he:T'.region s (u.rays (x-Z))=0:=by
    have hZ:= hh (x-Z); rw [show P.region s (x-Z)=0 from (by rw [map_sub]; rw [show P.region s Z=Z from P.idempotent w x]; exact sub_self _),map_zero,norm_zero,zero_pow (by norm_num)] at hZ; exact norm_eq_zero.mp (by nlinarith)
 rw [map_sub,map_sub,hv] at he; exact sub_eq_zero.mp he
#print axioms travelRegionSt
end YM.PanSt
end
