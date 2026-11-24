import Lucent.Clara
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

open Stencil

def beaded (F:List (Tint I)) (i:I)(X:Op Slot): Stencil I:=
 pack Finset.univ fun a=> pack Finset.univ fun b=> X a b • mono F [(i,a,b)]

lemma beaded_g (F:List (Tint I))(i:I)(X:Op Slot) : degree (beaded F i X) F.length 1:= by
  unfold beaded
  apply degree.pack; intro a h; apply degree.pack; intro b h; exact degree.scale (mono_grade F [(i,a,b)]) _

variable (X X' X'':Op Slot)(d:FieldPlan I) [Fintype I] (F E H L:List (Tint I))(i j k:I)
def fdiv (d:FieldPlan I)(L:List (Tint I))(S:Stencil I):ℂ:=S.quote (fun t=>vell (fair d.hands) (L++t.flash)*aria d.roles t.loom)
lemma fdiv_nil (S:Stencil I): faq d S=fdiv d [] S:=rfl
lemma solo : fdiv d L (beaded F i X)=0:=by
 unfold fdiv beaded; simp only [pack_q,scale_q,mono_q, aria,oneW, mul_zero,smul_zero,sum_const_zero]
private lemma traced₂ : (∑ a:Slot,∑ b, X a b*(∑ c,∑ e, X' c e*(ep b c* ep e a)))=Matrix.trace (X*X'):= by
   unfold ep; simp only [mul_ite, ite_mul,mul_zero,zero_mul, mul_one,one_mul, sum_ite_eq,sum_ite_eq', mem_univ,ite_true, Matrix.trace,Matrix.diag_apply,Matrix.mul_apply] -- tune!

private lemma trace₃ : (∑ a:Slot,∑ b, X a b * (∑ c,∑ e, X' c e*(∑ f,∑ g, X'' f g * (ep b c*ep e f*ep g a))))=Matrix.trace ((X*X')*X''):= by
  simp only [mul_ite, ite_mul,mul_zero, zero_mul,mul_one,one_mul,ep,sum_ite_eq',sum_ite_eq, mem_univ,ite_true]
  rw [mul_assoc]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=> congrArg (X a b * ·) ?_
  rw [sum_eq_single b]
  · simp
  · intro c _ h; simp [h.symm]
  simp
def twoc (d:FieldPlan I)(i j:I):ℂ:= -(moneyC d.roles i j * moneyC d.roles j i) * (1/2:ℂ)^2
def tria (d:FieldPlan I)(i j k:I):ℂ:= moneyC d.roles i j * moneyC d.roles j k * moneyC d.roles k i * (1/2:ℂ)^3
lemma duoc :
 fdiv d L (beaded F i X * beaded E j X')=Matrix.trace (X*X')* (twoc d i j* vell (fair d.hands) (L++(F++E))):=by
 rw [←traced₂]; simp only [sum_mul]
 simp only [beaded,fdiv,mul_q,pack_q,scale_q,mono_q,Join.glue,aria,List.singleton_append,twoW,smul_eq_mul]
 simp only [mul_sum,sum_mul,List.length_cons,List.length_nil]
 refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>sum_congr rfl fun c _=> sum_congr rfl fun g _=>by simp only [sum_mul,twoc]; ring -- sum_mul and mul_sum

lemma viac (s:moneyC d.roles i k=0):
 fdiv d L (beaded F i X * beaded E j X' * beaded H k X'') = Matrix.trace (X*X'*X'') * (tria d i j k * vell (fair d.hands) (L++((F++E)++H))) :=by
 rw [← trace₃]
 simp only [beaded,fdiv,mul_q,pack_q,scale_q,mono_q,Join.glue,aria,List.singleton_append,List.cons_append,List.nil_append,threeW,smul_eq_mul,sum_mul,mul_sum,s]
 refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>sum_congr rfl fun c _=> sum_congr rfl fun e _=> sum_congr rfl fun f _=> sum_congr rfl fun g _=>by simp only [tria,List.length_cons,List.length_nil]; ring
