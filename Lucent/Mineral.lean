import Lucent.Tessa
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

open Hiro
open scoped Kronecker
abbrev chip (b:Pig): SU.group.Color := mug b
abbrev crest (b:Pig) :Op Slot:= walkC (chip b)
def tally (z:Window.Family):ℂ:= if z.2 then 15 else 5
abbrev metals (z:Window.Family) := cutM (Window.colors z)

variable (z:Window.Family)
lemma chip_norm (b:Pig): ‖chip b‖=1 := (EuclideanSpace.basisFun Pig ℝ).orthonormal.1 b
lemma crestTrace (b:Pig): Matrix.trace (crest b * crest b)=60:=by unfold crest; rw [walk_square,chip_norm]; norm_num

private lemma traces_cut (A:Op F): Matrix.trace (dMatter A^2*metals z)= (if z.2 then Matrix.trace (ExTwo.gen A ^ 2) else Matrix.trace (cc A ^2)):=by
  rw [sq,dMatter,op_kron_mul,sheetD,mul_one,Join.both_mul]
  rcases z with ⟨w,k⟩; let V:=∑ j:Sheet, if Sum.isLeft j=k then Join.both (ExTwo.gen A ^ 2) (cc A^2) j j else (0:ℂ)
  have p : (if k then Matrix.trace (ExTwo.gen A^2) else Matrix.trace (cc A^2))=V:= by cases k <;> simp [V,Fintype.sum_sum_type,Sheet,Matrix.trace,Join.both]
  have g : (w,k).snd=k:=rfl; rw [g,p]; simp only [Matrix.trace,Matrix.diag_apply,Slot,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single w]
  · refine sum_congr rfl fun j _=>?_; simp [metals,cutM,Window.family,Window.colors,sq, Matrix.kronecker_apply,Eq.comm (a:=k)]
  · intro i t h; simp [metals,cutM,Window.family,Window.colors,h,sq,Matrix.kronecker_apply]
  simp

lemma iod (b:Pig): Matrix.trace (crest b * crest b * metals z)=tally z:=by
 let x: Op SU.F:=group.colorMat (chip b)
 obtain ⟨h,f⟩:=Thera.league.mp (group.colorMat_mem (chip b))
 change star x = -x at h; change Matrix.trace x=0 at f
 have k:Matrix.trace (x^2)= -5:=by
   have e:=crestTrace b; unfold crest at e; rw [walk_price] at e; change Matrix.trace ((-Complex.I•dMatter x)*(-Complex.I • dMatter x))=_ at e
   rw [Matrix.smul_mul,Matrix.mul_smul, Matrix.trace_smul,Matrix.trace_smul,←sq,(local_polynomial x ⟨h,f⟩).2.1] at e
   simp only [smul_eq_mul,←mul_assoc,neg_mul_neg,Complex.I_mul_I] at e; linear_combination -e/12
 unfold crest; rw [walk_price]; change Matrix.trace ((-Complex.I • dMatter x)*(-Complex.I •dMatter x)*_)=_
 rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul, Matrix.smul_mul, Matrix.trace_smul,←sq (dMatter x),traces_cut,ExTwo.quad_gen,f,k,cc,h,← Matrix.transpose_pow,Matrix.trace_transpose,neg_sq,k]
 simp only [smul_eq_mul, neg_mul_neg,Complex.I_mul_I]; norm_num [SU.F,tally] <;> split <;> norm_num
