import ZecaBubble
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin

open Boundary Probe

variable (Ω:Bench S) (D:Moment H)
local notation "O"=>Ω.val
variable (h:saucer S Ω.val=Ω.val) (e:∀p,M S p Ω.val=Ω.val)

local notation "P" => parabola S D.n
variable (f:Test4)
include h e

/-- Exact heat of Mink vector. -/
lemma cinnabar (u:ℝ≥0) (p:0<u)
 (c:HasCompactSupport (⇑f)):
 S.E u (D.field S f Ω).val=
    ∫ y:E4, f y • M S y (P (duration u) (D.op O)):=by
 let J:=P (duration u)
 let v:=J (D.op O)
 have k:Integrable (fun y:E4=> f y • M S y v) :=
   (f.continuous.smul ((step_c S).comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport c.smul_right
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

omit h e
abbrev awake (f:Test4):=(D.field S f Ω).val
include e in
lemma awake_move (p:E4)(f:Test4):awake S Ω D (ahead p f)= M S p (awake S Ω D f):=by
 have t:usher S p Ω=Ω:=Subtype.ext (e p)
 exact (congrArg Subtype.val ((realStamp S).travel D p f Ω |>Eq.trans <| congrArg (D.field S (ahead p f)) t)).symm
open Probe
lemma awake_m (Z: Moment H)(g:Test4):
  inner ℂ (awake S Ω D f) (awake S Ω Z g)=
    inner ℂ O (D.dagger.field S (bar f) (Z.field S g Ω)).val:=
 (realStamp S).adj D f Ω _

#print axioms cinnabar
#check Probe.bar
