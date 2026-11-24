import Organdy.Confetti

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

open Hive Levier Urn

/-
 A target inequality, and how to use it (first step only —
 gives the mixed contrast with a current STENCIL). This part is
 CONDITIONAL.
-/
variable (P:Spine)(s r:ℕ)(u:P.Spectrum0 timeAxis)
local notation "π"=> turned P r
local notation "V"=>P.singleState timeAxis s u
local notation "H"=> P.calibration
local notation "A"=> timeAxis

def stain(f g:P.Test):ℂ:=
 V (π f * g) - V (π f)*V g
def severity(f:P.Test):ℝ:= (stain P s r u f f).re

lemma stain_add₁ (f g y:P.Test):
 stain P s r u f (g+y)=stain P s r u f g+stain P s r u f y:=by unfold stain; rw [mul_add,map_add,map_add,mul_add]; ring
lemma stain_add₂ (f g y:P.Test):
 stain P s r u (g+y) f=stain P s r u g f+stain P s r u y f:=by
 unfold stain turned;rw [map_add,add_mul,map_add,map_add,add_mul];ring

def affect(f:P.Test): P.Test →+ ℂ:=AddMonoidHom.mk' (stain P s r u f) (stain_add₁ P s r u f)

variable {w:ℤ}(e:Heat.gaugeShift P.par.block w= -(r:ℤ))
include e
lemma star₁(f:P.Test):star (V f)= V (π f):=by rw [turned,←e,single_star]

lemma stain_symm(f g:P.Test):
 stain P s r u f g=star (stain P s r u g f):=by
 unfold stain
 have v(y):π (π y)=y:=aureoleTwice ..
 rw [star_sub,star_mul, star₁ P s r u e, star₁ P s r u e, star₁ P s r u e,
    show π (π g*f)=π (π g)*π f from aureoleProduct .., v, mul_comm g (π f)]

lemma total(f:P.Test):
 severity P s r u f= (V (π f*f)).re - ‖V f‖^2:=by
 unfold severity stain
 rw [Complex.sub_re, ←star₁ P s r u e,Complex.sq_norm, mul_comm (star _) _]
 have g:V f*star (V f)=(↑(Complex.normSq (V f)):ℂ):=Complex.mul_conj _
 rw [g,Complex.ofReal_re]

lemma total_add (f g:P.Test):
 severity P s r u (f+g)=severity P s r u f + severity P s r u g+2*(stain P s r u f g).re:=by
 unfold severity
 rw [stain_add₁,stain_add₂,stain_add₂,stain_symm P s r u e g]
 simp only [Complex.add_re,Complex.star_def,Complex.conj_re]
 ring

variable {c:Cuts} {P s r u}
 {I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
 (p:Parade l P c d s i k X F x)
def rung(P:Spine)(c:Cuts)(s r:ℕ):=
 gleamδ c.γ * ((hue P s)/(guineas P s * distanceP r^4))^2
local notation "a" => (hue P s:ℂ)
abbrev strobe:= pauldron H (a • corset p)
def Rebate (r:ℕ)(u:P.Spectrum0 timeAxis):Prop:=
 severity P s r u (strobe p) < rung P c s r

-- RB needed for the following claim. Loss in ratio at ANY one eligible distance.
include e
variable (m:Grand P c s)(b:PrintRun p)
 (o:reach (guineas P s) r)

abbrev flood:=a • vivid p
abbrev currentP:= a • hatAxis (tenor p)
abbrev breach:= ventilate H c.m (currentP p)

include m b o in
lemma crackle(g:Rebate p r u):
 (stain P s r u (flood p) (breach p)).re < 0:=by
 let f:=flood p
 let j:=breach p
 let D:=severity P s r u
 have eq: strobe p=f+j:= b.net a

 have t: rung P c s r ≤ D f:=by
    change _ ≤ severity _ _ _ _ _
    rw [total P s r u e]
    apply b.centered r o
    exact half_le_self m.price.mood.plus.le
 have h:j∈ Place P s:=by
    rw [show j= strobe p - f from (add_sub_cancel_left ..).symm.trans
          (congrArg (· - f) eq.symm)]
    exact (Place P s).sub_mem (appealPopularity ((Place P s).smul_mem b.marked _))

       ((Place P s).smul_mem b.gauge _)
 have n:0 ≤ D j:=by
    change 0≤ severity _ _ _ _ _
    rw [total P s r u e]
    apply sub_nonneg.mpr
    rw [turned,←e]
    exact prestissimo P s _ _ _ _ _ h.1.1
      (e.symm ▸ inRegion r (m.path r o).2.2)
 have z: D (f+j)<D f:=by rw [←eq];exact lt_of_lt_of_le g t
 have y:D (f+j)=_:=total_add P s r u e f j
 change (stain P s r u f j).re<0
 linarith

include o b m in
/-- Mesh current component vs pure gauge stencil; CONDITIONAL. -/
theorem signboard(g:Rebate p r u):
 ∃ j:Axis,∃ v:Cover, (v=gstride c.m j ∨ v= -(gstride c.m j)) ∧
  stain P s r u (flood p) (stageMove H v (currentP p j)) ≠ 0:=by
 by_contra! h
 let C:=affect P s r u (flood p)
 have t:C (breach p)=0:=by
    change C (∑ j:Axis,twoSide H (gstride c.m j) (currentP p j))=0
    rw [map_sum]
    apply sum_eq_zero
    intro j _
    rw [twoSide,LinearMap.sub_apply,map_sub,
      show C (stageMove H (gstride c.m j) (currentP p j))=0 from h j _ (Or.inl rfl),
      show C (stageMove H (-(gstride c.m j)) (currentP p j))=0 from h j _ (Or.inr rfl),
      sub_self]
 have y:=crackle e p m b o g
 change stain P s r u (flood p) (breach p) =0 at t
 rw [t,Complex.zero_re] at y
 exact lt_irrefl _ y
#print axioms signboard
