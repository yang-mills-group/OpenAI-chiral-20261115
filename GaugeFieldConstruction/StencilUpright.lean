import GaugeFieldConstruction.StencilSidecar
import GaugeFieldConstruction.StencilEuForecast
/-!
# Simple central parity (not reflection) for the rank estimate against even scalars
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Ember Ember.Volumetric Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset Mink RawBank Cell FirstPackMars
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff InnerProductSpace Classical
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable (A:Axis→ CogPV)
def bothSt:Signed:= Signed.mirror 0 * Signed.mirror 1 * Signed.mirror 2 * Signed.mirror 3
lemma allSignSt : signBit bothSt=false:=by rw [bothSt,signBit_mul,signBit_mul,signBit_mul]; simp
abbrev stillSO_st := signMot _ allSignSt
lemma price3_allSt (i:Axis)(t:looksVectorSt A): spinFrame three bothSt (A i)=- A i:=by
 rw [t bothSt i allSignSt]; have e:bothSt.perm i=i:=by unfold bothSt; rfl; --? Mirror perms = refl defeq
 rw [show bothSt.flip i=true from (by fin_cases i<;>rfl),pay_true,e]
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{φ:ℕ→Carat}(q:Ticket φ C)(F:FreeName three)
lemma axisVoid_st (i:Axis)(t:looksVectorSt A): compassPiMars q stillSO_st (LowIncPV (F.c (A i)))= - LowIncPV (F.c (A i)):=by
 rw [arcE_st, ← coin_E_st,←mirror,price3_allSt _ _ t,map_neg,map_neg]
-- keep one-point consequence even for all V in these columns
variable {H:CloudsL}(h:SurfCheckL H)(u:SurfCheckL.boisterL q H)
include h u
lemma quiet_allSt(x:Points 1)(i:Axis)(t:looksVectorSt A): H 1 x ![LowIncPV (F.c (A i))]=0:=by
 let P:=LowIncPV (F.c (A i)); let V:=![P]; have hx(x: Points 1):x∈ conf 1:= (fun _ _ _=> Subsingleton.elim ..)
 suffices ζ:H 1 0 V=0 by
   have he:= h.even (x 0) V 0 (hx 0); rw [show NSF.Points.across (x 0) 0=x from (by apply PiLp.ext; intro i; fin_cases i; exact zero_add ..), ζ] at he; exact he
 let F':=(H 1 (0: Points 1)).toLinearMap V 0; have hw:= u 1 V 0 (hx _) stillSO_st; rw [show motionMoonMars _ (0 : Points 1) = 0 from by apply PiLp.ext; intro t; exact map_zero (stillSO_st.val.motion), show compassPiMars q stillSO_st ∘ V= Function.update V 0 (-P) from funext fun j=> by fin_cases j; exact axisVoid_st A q F _ t] at hw
 have ha:H 1 0 V= F' P:= by unfold F'; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i; rfl
 change F' (-P)=_ at hw; rw [ha, map_neg] at hw; exact ha.trans (neg_eq_self.mp hw) -- tune
#print axioms axisVoid_st
end YM.GaugeFieldConstruction.Stage
end
