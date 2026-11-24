import YM.SU5.FiniteGaugeData.LapisQ.Musc
import YM.SU5.FiniteGaugeData.Lapis.Passport
import YM.CF.Thera.Jolt
set_option autoImplicit false
set_option maxHeartbeats 560000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LapisS
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.Lapis Lumi Eight
open Next.Rank Spindle Push.Local Rhythm LightK
namespace Fortuna
open YM.SU5.FiniteGaugeData.LapisQ Nosh Nectar Apoth Cordon Exterior Work.F03
open LapisS.Stadium
-- GLINT
variable (Q:Calibration)(p:Clip)(r:ℝ)(x y:Cover)(s s':Signed)(i j:RG.Slot)(a:Axis)(z:ℤ) (A B:PlaqAxes)
local notation "G"=>SU.group
noncomputable abbrev glint (Q:Calibration)(p:Clip)(r:ℝ)(x:Cover)(i:RG.Slot)(s:Signed): Charm.W Q:= Stadium.pole (zenY SU.group i) p r Q x s
noncomputable abbrev eyeball (Q:Calibration)(p:Clip)(r:ℝ)(x:Cover)(a:PlaqAxes) := glint Q p r x (sprinkle 0 a) 1
local notation "🌞" x:max a:max=> eyeball Q p r x a
local notation "F₀" x:max i:max s:max=> glint Q p r x i s
lemma glintV (m:Side) (U:Fields (Q.c m)) : (glint Q p r x i s).val m U= ((Lumi.live (zenY SU.group i) p r s (wrap _ x) U.1:ℝ):ℂ) • 1:= Stadium.rod_book ..
lemma eyeVal (m:Side)(U:Fields (Q.c m)) : (eyeball Q p r x A).val m U=((wardF p r U.1 (wrap _ x,A):ℝ):ℂ) • 1:=by
 rw [eyeball,glintV,zenZ,wet0,map_zero, zero_add] -- row shift sign.B
lemma combe: glint Q p r x i s= glint Q p r x (Lumi.pick («G»:=SU.group) s i).1 1:=by apply Subtype.ext; funext q A; rw [glintV,glintV,orientZ]
lemma sated : glint Q p r x i 1= eyeball Q p r (i.offset+x) i.plaq:= by
 apply Subtype.ext; funext b Y; rw [eyeVal,glintV,zenZ,map_add]; rfl
lemma duly: eyeball Q p r (x+y) B= glint Q p r y (sprinkle x B) 1:=by rw [sated,wet]; rfl
lemma dualeW : Stadium.pole (dualY SU.group i j) p r Q x 1= glint Q p r x i 1*glint Q p r x j 1:=by
 apply Subtype.ext; funext m T; change Stadium.rod (dualY G i j) p r Q x 1 _ T= (F₀ x i 1).val _ T * (F₀ x j 1).val _ T; rw [Stadium.rod_book,glintV,glintV,dualZ,Complex.ofReal_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,one_mul, smul_smul] -- tune
noncomputable abbrev jointEye (Q:Calibration)(p:Clip)(r:ℝ)(x y: Cover):W Q:= Stadium.pole (eyeS SU.group x) p r Q y 1
lemma fameR: jointEye Q p r x y= eyeball Q p r y leg0*eyeball Q p r (x+y) leg0:=by rw [jointEye,eyeS,dualeW,duly]
-- merge covers
noncomputable abbrev stitchE (a:Signed) (i:RG.Slot):= (Lumi.pick («G»:=SU.group) a i).1
noncomputable abbrev needler (a:Signed)(i:RG.Slot)(x y: Cover):= sprinkle ((stitchE a i).offset+x-y) (stitchE a i).plaq
lemma stuffed : glint Q p r x i s= glint Q p r y (needler s i x y) 1:=by
 rw [combe Q p r x s i,sated,sated, needler, wet, sub_add_cancel]; rfl -- tune arg order
noncomputable abbrev duoF(s s':Signed)(i j:RG.Slot)(x y:Cover): Lumi.Duct SU.group Bool:= dualY SU.group (stitchE s i) (needler s' j y x)
lemma stuffedP : glint Q p r x i s*glint Q p r y j s'=Stadium.pole (duoF s s' i j x y) p r Q x 1:=by rw [combe Q p r x s i,stuffed Q p r y x s' j]; exact (dualeW ..).symm
lemma pause (z':ℤ) : fire Q a z' (glint Q p r x i s)=glint Q p r ((plane a z').motion x) i (Signed.mirror a*s):=by
 apply Subtype.ext; funext m U; rw [ice_print, reflector, reflMark,glintV,theta_smul,theta_one,glintV]; -- tune
 rw [Complex.star_def, Complex.conj_ofReal]; apply congrArg (· • (1:FC _)); -- type class inference
 apply congrArg ((↑):ℝ→ℂ) 
 change Lumi.live (zenY G i) p r s _ (fling a z' _ U.1)=_
 rw [fling_eq]; refine (Lumi.probe_p (t:=0) ..).trans ?_; -- use `probe_p` takes `z` param too & multipl composition
 have he:= Shape.anno (plane a z') (N:=Q.c m) x; rw [←he]; rfl
lemma pause0 : fire Q a 0 (glint Q p r x i s)=glint Q p r ((plane a 0).motion x) i (Signed.mirror a*s):= pause ..
private lemma spiceH : (plane a (Heat.gaugeShift Q.B z)).motion ((plane a 0).motion x)=beat Q a z x:=by
 funext i; simp_rw [fling_move]; by_cases e:i=a; · subst i; rw [if_pos rfl,if_pos rfl, mul_zero,add_zero,neg_neg,tick_tock,beat_same]
 rw [if_neg (Ne.symm e),beat_slant Q i a z x (Ne.symm e), if_neg (Ne.symm e)] -- tune
lemma truss : clockW Q a z (glint Q p r x i s) = glint Q p r (beat Q a z x) i s:= by
 unfold clockW; simp_rw [pause]; have he:=spiceH Q x a z; rw [he, show Signed.mirror a*(Signed.mirror a*s)=s from ?_]; nth_rw 1 [← Signed.mirror_inv a]; exact inv_mul_cancel_left ..
lemma leapE (k:ℕ): clockW Q a k (eyeball Q p r x B) =eyeball Q p r (leapU x a (tic Q) k) B:=by
 unfold eyeball; rw [truss]; apply congrArg (fun i=> (F₀ i (sprinkle 0 B) 1)); unfold beat leapU; rw [←Nat.cast_mul, ←Nat.cast_smul_eq_nsmul ℤ (tic Q*k)]
-- operator & coordinates uniform. no phase hidden
lemma opGlint : SalonG.Width Q (glint Q p r x i s) 1:=by
 intro m v; rw [glintV,norm_smul,norm_one, Complex.norm_real,mul_one]; exact (zenY G i).enough _ -- defeq live
open Push.Local
abbrev rangeP (p:RG.Slot)(x:Cover): Finset Cover:=scape x (macroK Unit (zenY SU.group p)) -- check namespace
lemma shop : Locator Q (glint Q p r x i s) (rangeP i x):= Stadium.paneBolt ..
end Fortuna
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Fortuna.shop
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Fortuna.leapE
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Fortuna.fameR
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Fortuna.stuffedP
