import Merino.Mitre.Velvet
import Merino.Hem.Agate
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Branch Sault Dial Vow BProof Reed Brooch Thera Kennel Hest

variable {N:Side}

open Hive Swell Hem
open Merino.Mitre

variable {F:Evaluation N}
abbrev prance (s:Sweep N):=Bide.move s⁻¹
lemma prA (s t:Sweep N)(h:Bide.plainP F):
 prance s (prance t F)=prance (s*t) F:=by unfold prance; rw [Bide.dance _ _ h,_root_.mul_inv_rev]
lemma prB (s:Sweep N)(A:ℝ) : prance s ((A:ℂ) • F)=(A:ℂ) • prance s F:=by
 funext U
 change tourP _ _ _ ((A:ℂ) • F (flashA s⁻¹⁻¹ U))=_
 rw [sew_scale]
 -- cSignX
 have e(b:Bool):cSignX b (A:ℂ)=(A:ℂ):=by cases b <;>simp [cSignX]
 rw [e];rfl

lemma light_foot {G:Evaluation N}
 {v:Site N}(h:Bide.plainP F)(f:Spool.perches F G v):
    prance (taxiPlus v) F=G:=by
 funext V
 have j:=Mitre.sail v h V
 have e := j.trans (f V).symm
 rw [← sub_eq_zero] at e ⊢
 rw [←map_sub] at e
 exact norm_eq_zero.mp ((twist_norm _ _).symm.trans (congrArg norm e) |>.trans norm_zero)
-- Orientation signed shifts, in matter units
abbrev slide (N:Side)(a:Axis)(m:ℤ):Site N:=wrap N (m • step a)
def bend (σ:Signed)(a:Axis)(m:ℤ):= if σ.flip a then -m else m
lemma rProduct (σ:Signed)(v:Site N) :
 rim N σ * taxiPlus v=taxiPlus (σ.act v) * rim N σ:=by
 change Sweep.mk (σ*1) (0+σ.act v) ((detX σ).xor false)=
     Sweep.mk (1*σ) (σ.act v+(1:Signed).act 0) (false.xor _)
 simp [rim]
lemma stride (σ:Signed)(a:Axis)(m:ℤ):σ.act (slide N a m)=slide N (σ.perm a) (bend σ a m):=by
 unfold slide bend
 simp only [map_zsmul,wrap_step]
 have e:σ.act (step a:Site N)= if σ.flip a then -step (σ.perm a) else step (σ.perm a):=by
   rw [←Lattice.Step.vec_pos, ←Lattice.Step.vec_rotate]; simp only [Lattice.Step.rotate, Lattice.posDir,Lattice.Step.vec, Bool.false_xor]
 rw [show σ.act (m • (step a:Site N))=m • σ.act (step a) from map_zsmul σ.actEquiv m (step a),e]
 split <;> simp

variable {p:RG.BudgetPoint}{x:ℝ}{K:Scree.Loom N}{a b d:ℝ}{y:Spool N}
 (σ:Signed)(h:y.Hem K p a b d)

def trinc (f:Pane N→ℂ) : Evaluation N:=fun x=> f x • 1
lemma pr_scalar (f:Pane N→ℂ) :
  prance (rim N σ) (trinc f)=trinc (f∘flashA (rim N σ)):=by
 funext U
 change Spire.tourP _ _ _ (f (flashA (rim N σ)⁻¹⁻¹ U) • (1:FC (Single N))) =_
 rw [sew_scale,coin_one,inv_inv,
     show ((rim N σ)⁻¹).charge.xor (detX (castX (rim N σ)⁻¹).s)=false from ?_]
 · rfl
 change (detX σ).xor (detX σ⁻¹)=false
 rw [←det_p,mul_inv_cancel,det_i]

include h
lemma plainJ (i:Axis):Bide.plainP (prance (rim N σ) (y.jPole K p i)) :=
 Bide.keys _ (Bide.plain (allowedX (h.jPole i)))
lemma shiftJ (i:Axis){x:Site N}{m:ℤ} (v:x-y.origin=slide N i m) :
 prance (taxiPlus (slide N (σ.perm i) (bend σ i m))) (prance (rim N σ) (y.jPole K p i))
  = prance (rim N σ) (y.jShift K p i x):=by
 have e:=Bide.plain (allowedX (h.jPole i))
 rw [prA _ _ e,←stride,←rProduct,←v,←prA _ _ e, light_foot e (h.poses i x)]
omit h
lemma right_offset(i:Axis):y.rightY i-y.origin = slide N i y.stepY:=by
 simp only [slide,map_zsmul,wrap_step]; simp [Spool.rightY,gapPlus]
lemma left_offset(i:Axis):y.leftY i-y.origin = slide N i (-y.stepY:ℤ):=by
 simp only [slide,map_zsmul,wrap_step]; simp [Spool.leftY,gapPlus]

end YM.CF.Merino.Tiara
