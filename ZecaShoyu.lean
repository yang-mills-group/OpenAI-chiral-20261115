import ZecaSpray
import ZecaUnagi
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
local notation "R" => saucer S

open Poin

open Boundary Probe

variable (Ω:Bench S) (D:Moment H)
local notation "O"=>Ω.val
variable (h:saucer S Ω.val=Ω.val) (e:∀p,M S p Ω.val=Ω.val)

local notation "P" => parabola S D.n
variable (f:Test4)
include h e


open Six
omit h e
lemma soy_int(f:Test4) (v:H):
 Integrable (fun y:E4=> f y • M S y v):=by
 have H':Integrable (fun y:E4=>‖f y‖*‖v‖):= f.integrable.norm.mul_const _
 refine H'.mono (f.continuous.smul
      ((step_c S).comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable (ae_of_all _ fun y=>?_ )
 change ‖f y • M S y v‖ ≤ ‖‖f y‖*‖v‖‖
 rw [norm_smul,M,S.unit.unitary]
 exact Real.le_norm_self _
include h e
/-- Exact heat of Mink vector. -/
lemma cinnabar_ext (u:ℝ≥0) (p:0<u):
 S.E u (D.field S f Ω).val=
    ∫ y:E4, f y • M S y (P (duration u) (D.op O)):=by
 let J:=P (duration u)
 let v:=J (D.op O)
 have k:Integrable (fun y:E4=> f y • M S y v)  := soy_int S f v

 apply ext_inner_left ℂ
 intro x
 let X:Bench S:=⟨S.E u x,ray S x u p⟩
 rw [←ContinuousLinearMap.adjoint_inner_left, S.sym]
 change inner ℂ X.val (D.field S f Ω).val= inner ℂ x (∫ y:E4, f y • M S y v)
 rw [(realStamp S).scalar,←integral_inner k]
 have t:hall S D.n X=J x:= by
    apply cache_I S D.n
    rw [releases]
    exact (DFunLike.congr_fun (K_E S D.n u p) x).symm
 refine integral_congr_ae (Eventually.of_forall fun y=>?_ )
 unfold Moment.form lucent
 rw [t,hallO S Ω h]
 change f y * inner ℂ (J x) (M S y (D.op (M S (-y) O))) = inner ℂ x (f y • M S y v)
 rw [e,inner_smul_right,←ContinuousLinearMap.adjoint_inner_right,show J.adjoint=J from para_adj S D.n u p]
 exact congrArg (fun z=> f y * inner ℂ x z)
   (DFunLike.congr_fun (mslot S y _ (dur.mpr p) D.n).eq (D.op O))


/-- Looser unpadding estimate through any given region -/
local notation "YPROJ" => S.ℚmeasure.region
lemma shoyu (L:Set E4)(b:MeasurableSet L) (q:ℂ) (s:ℝ≥0) (p:0< s):
 ‖YPROJ L (S.E s (q•awake S Ω D f))‖ ≤
   (∫ y:E4,‖f y‖) * ‖YPROJ L (q•P (duration s) (D.op O))‖:=by
 rw [map_smul,awake,cinnabar_ext S Ω D h e f s p]
 let v:= P (duration s) (D.op O)
 let d:= (YPROJ L)*((q•1):H.Op)
 have hd(z:H):d z = YPROJ L (q•z):=rfl
 rw [←hd,←ContinuousLinearMap.integral_comp_comm d (soy_int S f v), ←hd,←integral_mul_const]
 -- norm integral dominated
 refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (ae_of_all _ (fun y=>?_))
 have a:= (DFunLike.congr_fun ((Six.rep_unit S y).comm_region b) (q•v)).symm
 change YPROJ L (M S y (q•v))=M S y (YPROJ L (q•v)) at a
 beta_reduce
 rw [map_smul,norm_smul,hd,hd, ← map_smul (M S y),a,M,S.unit.unitary]
#print axioms shoyu
