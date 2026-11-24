import Lucent.LatticeFieldEstimates
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

set_option maxHeartbeats 380000
set_option linter.unusedSimpArgs false
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

open Maxwell Cache Glaze
abbrev xy : PlaqAxes:=⟨(0,1),by decide⟩
variable (x:Gaia)
structure Duo (x:Gaia):Prop where
 x0:x 0=0
 x1:x 1=0
 x2:x 2≠0
lemma Duo.non (p:Duo x):x≠0:=by intro h; apply p.x2; rw [h]; rfl
variable (p:Duo x)
include p
lemma monoP : 0<bareCurl 0 1 0 1 x := by
 unfold bareCurl; rw [Pi.sub_apply,Bare.opp_grad p.non, Bare.opp_grad p.non]; simp [Axis,second_Green p.non,p.x0,p.x1]; have v:=norm_pos_iff.mpr p.non
 unfold Maxwell.normal; positivity

lemma tone : gleamV x (dnSpin 1) (upSpin 1)= (x 3:ℂ)-(x 2:ℂ)*Complex.I:=by
 rw [gleamV,Matrix.mul_sum, Matrix.sum_apply]; simp_rw [Matrix.mul_smul,Matrix.smul_apply]
 have he(i:Axis) : (minA*gammaOp i) (dnSpin 1) (upSpin 1)= (if i=(3:Axis) then (1:ℂ) else if i=(2:Axis) then -Complex.I else 0):=by
    rw [minA, show Aop = cutM plusHalf from Adef.trans raising.symm, sub_mul,one_mul,Matrix.sub_apply, cutM,Matrix.diagonal_mul,if_neg (dn_half _),zero_mul,sub_zero]
    change gammaOp i 3 1 = _
    fin_cases i <;> norm_num [gammaOp,Fin.ext_iff,SpinIdx] <;> rfl
 simp_rw [he,smul_eq_mul]
 simp only [mul_ite,mul_one,mul_zero]
 norm_num [Fin.sum_univ_succ,Axis,Fin.ext_iff]

 rw [show (Fin.succ (2:Fin 3)) = (3:Axis) from rfl]; ring
lemma butt : Onyx.pencil x (dnSpin 1) (upSpin 0)=0:=by
 unfold Onyx.pencil; rw [Matrix.smul_apply]
 suffices gleamV x (dnSpin 1) (upSpin 0)=0 by rw [this,smul_zero]
 rw [gleamV,Matrix.mul_sum, Matrix.sum_apply]
 refine sum_eq_zero fun i _=> ?_
 rw [Matrix.mul_smul,Matrix.smul_apply, minA, show Aop = cutM plusHalf from Adef.trans raising.symm, sub_mul,one_mul,Matrix.sub_apply, cutM,Matrix.diagonal_mul, if_neg (dn_half _),zero_mul,sub_zero]
 change (x i:ℂ) * gammaOp i 3 0=_
 fin_cases i
 · change (x (0:Axis):ℂ)*_=0; rw [p.x0,Complex.ofReal_zero,zero_mul]
 · change (x (1:Axis):ℂ)*_=0; rw [p.x1,Complex.ofReal_zero,zero_mul]
 · have ht:gammaOp 2 3 0=0:=rfl; exact mul_zero _
 exact mul_zero _
lemma bull (i:Fin 2): Onyx.pencil x (dnSpin i) (upSpin i)≠0:=by
 unfold Onyx.pencil; rw [Matrix.smul_apply]
 have v:=norm_pos_iff.mpr p.non
 refine smul_ne_zero (by positivity) ?_
 fin_cases i
 · change gleamV x (dnSpin 0) (upSpin 0)≠0; rw [quaternion x]; intro h; have u:=congrArg Complex.im h; simp at u; exact p.x2 u
 change gleamV x (dnSpin 1) (upSpin 1)≠0; rw [tone x p]; intro h; have u:=congrArg Complex.im h; simp at u; exact p.x2 u

omit p
variable (d:FieldPlan I)(u v i j k:I)
-- Conditions on d at the intended placements
structure Money(d:FieldPlan I)(u v i j k:I):Prop where
 shades:∀ i,(d.hands i).shade=xy
 apart:{p q:I}→p≠q→ Duo ((d.hands p).p - (d.hands q).p) -- actually v uses same staff hinge, fine
 tied : ∀ a∈[i,j,k],(d.hands a).p=(d.roles a).pt
 left:(d.roles i).voice=(0,1)
 right:(d.roles j).voice=(1,0)
 axial:(d.roles k).voice=(0,0)
 guests:[u,v,i,j,k].Nodup
variable (h:Money d u v i j k)

lemma group_pos : (Fintype.card Pig:ℂ) ≠ 0:=by
 haveI: Nontrivial SU.group.Color:= Thera.yet_one.nontrivial_color
 have hf:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
 change (Fintype.card (Fin SU.group.lieDim):ℂ)≠0; rw [Fintype.card_fin]; exact_mod_cast hf.ne'
include h
lemma precious : twoc d i j≠0 ∧ tria d i j k≠0 ∧ moneyC d.roles i k=0:=by
 obtain ⟨_,_,t,s⟩:True∧ True∧ i≠j∧i≠k∧j≠k:=by have :=h.guests; simp at this; tauto
 have ti:= h.tied i (by simp)
 have tj:= h.tied j (by simp)
 have tk:= h.tied k (by simp)
 simp only [twoc,tria,moneyC, billX,outside,upstairs,Function.comp_apply,h.left,h.right,h.axial,←ti,←tj,←tk]
 exact ⟨mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (bull _ (h.apart t) 1) (bull _ (h.apart t.symm) 0))) (by norm_num),
   mul_ne_zero (mul_ne_zero (mul_ne_zero (bull _ (h.apart t) 1) (bull _ (h.apart s.2) 0)) (bull _ (h.apart s.1.symm) 0)) (by norm_num), butt _ (h.apart s.1)⟩

theorem priceless [Fintype I] (z:Window.Family) :
   faq d (V i*V j* D z k)- faq d (V i*V j)*faq d (D z k) ≠ 0 ∧ faq d (G u v*(V i*V j)) - faq d (G u v)*faq d (V i*V j) ≠0:=by
 obtain ⟨r,l⟩:=precious d u v i j k h
 obtain ⟨e1,e2,e3,e4,e5⟩:u≠i∧ u≠j∧v≠i∧v≠j∧i≠j:=by have :=h.guests; simp at this; tauto
 let p(a b:I):=bareCurl 0 1 0 1 ((d.hands a).p-(d.hands b).p)
 have w(a b:I):uFee d a b=(p a b:ℂ):=by unfold uFee; rw [h.shades,h.shades]
 have vpos(a b:I)(s:a≠b):0<p a b:=monoP _ (h.apart s)
 rw [price_D,mul_zero,sub_zero,price_allZ _ _ _ _ _ l.2,price_both,price_G,price_V,add_sub_cancel_left,hem]
 simp_rw [w]
 constructor
 · exact mul_ne_zero (mul_ne_zero (mul_ne_zero group_pos (by unfold tally;split <;> norm_num)) l.1) (Complex.ofReal_ne_zero.mpr (vpos _ _ e5).ne')
 apply mul_ne_zero (mul_ne_zero (mul_ne_zero group_pos (by norm_num)) r)
 exact_mod_cast (add_pos (mul_pos (vpos _ _ e1) (vpos _ _ e4)) (mul_pos (vpos _ _ e2) (vpos _ _ e3))).ne'
