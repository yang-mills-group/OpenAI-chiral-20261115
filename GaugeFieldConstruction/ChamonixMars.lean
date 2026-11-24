import GaugeFieldConstruction.KeurMars
import GaugeFieldConstruction.PalmoraMars
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff FourierTransform InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
variable {n:ℕ} (k:Fin n) (a:Axis)
variable (F:Fin n→ΧiMars)
local notation "Q"=>TerraMars p Y
-- ∫ F test append identity
abbrev LookMars a j (K:Payroll n) b:= RyeMars (Q (Fathom.add (p.J a j) F)) K b a j
variable (x:Points n) (b:Bulb)(h:BreatherMars b k x)
lemma scanMars {ι:Type*}(s:Finset ι)(U:Set (Points n))(u:IsOpen U)(f:ι→Points n→ℂ)(v:∀ i∈s,ContinuousOn (f i) U) (t:Test n)(w:tsupport t ⊆ U):
    t.applyTo (fun x=>∑ i∈s,f i x)=∑ i∈s,t.applyTo (f i):=by
 unfold YM.Test.applyTo; simp_rw[Finset.mul_sum]; rw[integral_finsetSum _ (fun i h=>paleM U _ (f i) (v i h) t w u)]
include h
lemma EnrobeMars (i:Axis): D (direction k i) (Q F) x=∑ a:Axis,LookMars p Y F a i (Payroll.ticket i) b x:=by
 let U:= {x| BreatherMars b k x}; let K:Payroll n:=Payroll.ticket i
 have hp(a): ContinuousOn (LookMars p Y F a i K b) U:=SoilCanMars _ (TerraSm p Y _) K b a i k
 apply echelonsM U (fun _ (z:BreatherMars b k _) =>z.bounds) (BreathingMars b k) _ _
    (f:=fun y (z:BreatherMars b k _)=> (dSmooth (m:=∞) (TerraAt p Y F y z.bounds) _ (by simp)).continuousAt.continuousWithinAt)
    (g:=continuousOn_finsetSum _ (fun a _=>hp a)) _ h
 intro t hy; let V:=BreatherSupportMars b k U (fun _ he=>he) t hy
 rw [currentMars, translationMars p Y k F i b t V, scanMars _ U (BreathingMars b k) _ (fun a _=>hp a) _ hy]; apply Finset.sum_congr rfl; intro a _; change _=t.applyTo (RyeMars _ K _ a i); rw [SoilEarnMars _ (TerraSm p Y _) K b a i k t V]
 congr 1; ext1 x; rw[testcut_v]; change _= (D _ b.f _* YM.basis i i) • _; rw [show YM.basis i i=1 by simp,mul_one]; rfl -- tune
lemma EndorseMars (Ω:Ortho.Skew): Q (update F k (TrowMars p Ω (F k))) x=∑ a:Axis,∑ i:Axis,LookMars p Y F a i (Payroll.desk k Ω) b x:=by
 let U:= {x|BreatherMars b k x}; let K:= Payroll.desk k Ω
 let f(a i:Axis):= LookMars p Y F a i K b
 have he a i:ContinuousOn (f a i) U:=SoilCanMars _ (TerraSm p Y _) K b a i k
 have hv(a:Axis):ContinuousOn (fun x=>∑ i:Axis,f a i x) U:= continuousOn_finsetSum _ (fun i _=> he a i)
 apply echelonsM U (fun _ (z:BreatherMars b k _)=>z.bounds) (BreathingMars b k) _ _
    (f:= fun y (z:BreatherMars b k _)=> (TerraAt p Y (update F k (TrowMars p Ω (F k))) y z.bounds).continuousAt.continuousWithinAt)
    (g:=continuousOn_finsetSum _ (fun a _=>hv a)) _ h
 intro t hy; let V:=BreatherSupportMars b k U (fun _ he=>he) t hy
 change _=t.applyTo (fun x=>∑ a:Axis,∑ i:Axis,f a i x); rw [angularMars p Y k F Ω b t V,scanMars _ U (BreathingMars b k) _ (fun a _=> hv a) _ hy]; apply Finset.sum_congr rfl; intro a _; rw [scanMars _ U (BreathingMars b k) _ (fun i _=> he a i) _ hy]; exact Finset.sum_congr rfl fun i _=> (SoilEarnMars _ (TerraSm p Y _) K b a i k t V).symm
#print axioms EnrobeMars
#print axioms EndorseMars
end YM.GaugeFieldConstruction.Ember.Volumetric
