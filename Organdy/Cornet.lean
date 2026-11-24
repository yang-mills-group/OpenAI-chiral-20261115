import Organdy.Tinsmith

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


variable {K:Calibration} (m:ℕ)
def twoSide(K:Calibration)(y:Cover):Dome K→ₗ[ℂ] Dome K:= stageMove K y - stageMove K (-y)

lemma veerAlong (w:Dome K)(s:Signed)(y:Cover):
 flounce K (incX s) (stageMove K y w)=stageMove K (s.act y) (flounce K (incX s) w):=by
 unfold stageMove; rw [turner,turner]
 rw [show joinX (incX s) (fastPose y)= joinX (fastPose (s.act y)) (incX s) from ?_]
 change Shape.mk (s*1) (s.act y +0)= Shape.mk (1*s) (Signed.act 1 0+s.act y)
 simp

def bandcall (s:Signed)(i:Axis):ℂ:= if s.flip i then -1 else 1

lemma whirlPulse (w:Dome K)(s:Signed)(i:Axis):
 flounce K (incX s) (twoSide K (gstride m i) w) =
 twoSide K (gstride m (s.perm i)) (bandcall s i • flounce K (incX s) w) :=by
 have t: s.act (gstride m i) = m • ((posDir i).rotate s).vec:=by
    unfold gstride; rw [Lattice.Step.vec_rotate];exact map_nsmul (s.actEquiv (R:=ℤ)) _ _
 rw [map_smul]
 unfold twoSide
 rw [LinearMap.sub_apply,map_sub,veerAlong,veerAlong,Signed.act_neg,t,LinearMap.sub_apply]

 unfold bandcall gstride Lattice.Step.rotate
 unfold posDir
 dsimp only
 cases s.flip i
 · change _=(1:ℂ) • _
   rw [one_smul]
   rfl
 change stageMove K (m • (-Lattice.step (s.perm i))) _-stageMove K (-(m • (-Lattice.step (s.perm i)))) _=(-1:ℂ) • _
 rw [smul_neg,neg_neg,neg_one_smul,neg_sub]


def plank (s:Signed)(g:Axis→ Dome K) (i:Axis):=
 let u:= s.perm.symm i
 bandcall s u • flounce K (incX s) (g u)

def hatAxis(g:Axis→ Dome K)(i:Axis):Dome K:=
 feeD • ∑ s:Signed, ebony s • plank s g i

def ventilate(K:Calibration)(m:ℕ): (Axis→ Dome K) →ₗ[ℂ] Dome K where
 toFun g:= ∑ i:Axis, twoSide K (gstride m i) (g i)
 map_add' f g:=by simp [Pi.add_apply,sum_add_distrib]
 map_smul' a f:=by simp only [Pi.smul_apply,map_smul,smul_sum,RingHom.id_apply]

lemma trainClamp (g:Axis→Dome K)(s:Signed):
 flounce K (incX s) (ventilate K m g)= ventilate K m (plank s g):=by
 change flounce _ _ (∑ i:Axis, twoSide K (gstride m i) (g i))=∑ i:Axis, twoSide K (gstride m i) (plank s g i)
 conv_rhs => rw [← Equiv.sum_comp s.perm]
 rw [map_sum]
 simp only [whirlPulse,plank,Equiv.symm_apply_apply]

lemma voiced (g:Axis→Dome K):
 pauldron K (ventilate K m g)=ventilate K m (hatAxis g):=by
 rw [show hatAxis g= feeD • ∑ s:Signed, ebony s • plank s g from by funext i; simp only [hatAxis,Pi.smul_apply,Finset.sum_apply]]
 rw [showtime,map_smul,map_sum];simp_rw [map_smul,trainClamp]

lemma keyBoard(s t:Signed)(u:Axis):bandcall (t*s) u=bandcall t (s.perm u)*bandcall s u:=by
 unfold bandcall;rw [Signed.mul_flip]; cases t.flip (s.perm u) <;>cases s.flip u<;>norm_num
lemma plankSeat(g:Axis→Dome K)(s:Signed)(u):
 plank s g (s.perm u)=bandcall s u • flounce K (incX s) (g u):=by simp [plank]
lemma clampAccess(g:Axis→Dome K)(t:Signed)(i:Axis):
 bandcall t i • flounce K (incX t) (hatAxis g i)=ebony t • hatAxis g (t.perm i):=by
 unfold hatAxis
 rw [map_smul,smul_comm (bandcall t i),smul_comm (ebony t),map_sum]
 refine congrArg (feeD • · : Dome K→Dome K) ?_
 conv =>
  rhs
  arg 2
  rw [← Equiv.sum_comp (Equiv.mulLeft t)]
 rw [smul_sum,smul_sum]
 refine sum_congr rfl fun s _=>?_
 change _=ebony t • ebony (t*s) • _
 obtain ⟨j,rfl⟩:=s.perm.surjective i
 rw [map_smul,← Signed.mul_perm_apply,plankSeat,show (Equiv.mulLeft t) s=t*s from rfl,plankSeat,keyBoard,map_smul,turner,joinInc,ebonyHue,smul_smul (ebony t), ←mul_assoc,ebony_sq,one_mul]
 simp only [smul_smul];congr 1;ring
