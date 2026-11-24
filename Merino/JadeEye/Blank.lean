import Merino.Hem.Rose

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}

open Hem Window Buffered StressExchange Dial Peaks
variable (s:Sweep n)
open Py Rate LocalLimit Preparation

variable (j:ℕ)(M:Male)(e:ℝ)
variable (H:∀ x:Bkg (More n),Guard x e→ Safe (dome n (profile x))∧∀ M:Male,Safe (art n j M.val (profile x)))
variable (p:0<e)(u:1≤j)
include H p u
local notation "T"=> spar j M (1:Pane n)-tickA n
lemma reach (w:s.charge=false)(W:Op (Single n)):
    (T*W).trace=(slash s.s:ℂ)*(T*ech s⁻¹ W).trace:=by
   have h:=congrArg Matrix.trace (full_slide s W (1:Pane n) j M u e H (guard0 p.le))


   rw [jul_rep,vblank,Matrix.trace_smul] at h
   have h₁:=calc
     (T*W).trace=(ech s⁻¹ (T*W)).trace:=by
       unfold ech; rw [singT,trace_twist,win_trace, show s⁻¹.charge=false from w];rfl
     _=(slash s.s:ℂ)*(T*ech s⁻¹ W).trace:= h
   exact h₁

lemma rides (o y:Site n):
 (T*millQ o).trace=(T*millQ y).trace:=by
 let t:=y-o
 have hy:o+t=y:=by unfold t;abel
 have w:=millMotion t o
 rw [hy] at w
 rw [reach (taxiPlus t) j M e H p u rfl]
 rw [← w,ech_rev]
 have h:slash (taxiPlus t).s=1:=by
    have v:=slash_abs 1
    have d:=slash_mul 1 1; rw [one_mul] at d
    change slash 1=1
    rcases abs_eq (show (0:ℝ)≤1 by simp)|>.mp v with g | g; exact g; rw [g] at d; norm_num at d
 rw [h,Complex.ofReal_one,one_mul]


lemma blank_atom(o:Site n):
    (T*millQ o).trace=0:=by
 let k:=Signed.mirror 0
 let t:Sweep n:=⟨k,0,false⟩
 let v:=(castX t).mills n o
 have h0:boxA t (node o)=node v:= (castX t).nodex o |>.symm -- check
 have h:=Tye.proM (boxA t) (boxA t).injective t.charge (γS t)
   (fun i j=>Tye.birth_l i j (castX t) _ t.charge) (node o)
 rw [h0,←millstock,←millstock] at h
 change ech t _=_ at h
 have hv:ech t⁻¹ (millQ o)=millQ v:=by rw [←h,ech_rev]
 have he:=reach t j M e H p u rfl (millQ o)
 have ht:slash t.s= -1:=by unfold slash; change (if detX k then _ else _) = _; unfold k;rw [det_t];rfl
 rw [hv, ht,← rides j M e H p u o v] at he
 rw [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] at he
 linear_combination he/2

lemma blank_total (m:ℕ)(L:List Axis)(o:Site n):
  (T*squareSum millQ m L o).trace=0:=by
 induction L generalizing o with
 | nil => exact blank_atom j M e H p u o
 | cons i L ih=>
    rw [squareSum,stripSum,mul_sum,Matrix.trace_sum]
    exact sum_eq_zero fun _ _=>ih _


omit H p u
open Afterglow.Tower.VacuumSelection

abbrev cap0 (F:SOp n) := ‖(F (profile 1)).trace‖
lemma move0(s:Sweep n)(F:SOp n) : cap0 (julStep s F)=cap0 F:=by
 unfold cap0
 rw [jul_rep,vblank,ech,singT,trace_twist,win_trace]
 cases s⁻¹.charge
 · rfl
 change ‖star ((F (profile 1)).trace)‖=_
 rw [norm_star]

variable (P:Spine)(z:Bolts)
lemma epoint (m s i k:ℕ)
 (q:P.par.U.roundZ ≤ (RegNum P s i).val)
 {o:Site (RegNum P s i)}(D:Dress P s i k z m o):
 cap0 D.y.color ≤loseM P z.a s*z.c:=by
 let e:=P.par.V.note.fields_one _ (P.par.U.needed.trans q)
 let f :Openc (More (RegNum P s i)) P.par.d:=
   ⟨profile (1:Pane _),1,guard0 P.par.dpos.le,by simpa using P.par.dpos⟩
 have g:=congrArg Matrix.trace (D.glaze_funds f)
 rw [Matrix.trace_add] at g
 let N:=RegNum P s i
 let Z:=(LedgerM P s i k).J.M
 change ((spar P.par.K.j Z (1:Pane _)-tickA _)*windmill o m).trace=_ at g


 rw [show ((spar P.par.K.j Z (1:Pane N)-tickA N)*windmill o m).trace=0 from blank_total P.par.K.j Z _ e (by exact P.par.dpos.trans_le P.par.U.gem) (by rw [P.par.kJ]; decide) m _ o] at g
 change ‖(D.y.color f.val).trace‖ ≤ _
 rw [eq_neg_of_add_eq_zero_left g.symm,norm_neg]
 exact soak_trace D.wane f z.decay.le

