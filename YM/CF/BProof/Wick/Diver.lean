import YM.CF.BProof.Wick.Melt
import YM.CF.BProof.Align.Ins

/-! Limit of offerP shear. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Thera Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] {A: Op I} {c:ℝ}{p q:Finset I}{x: Wave I}
variable (b:Board A (cutM p) (cutM q) c)
include b
lemma pedal {u:ℝ}(g:u≠0): house A (cutM p) (cutM q) u=offerP p q u*(u • wedgeP A (cutM p) + wedgeQ A (cutM p)):=by
 let T:=offerP p q (u:ℂ); let V:=wedgeP A (cutM p); let L:=space (cutM p) (cutM q); have he : (u:ℂ) • T=(cutM p)+u • L+ u^2 • (cutM q):=by unfold T offerP; simp only [smul_add,smul_smul, mul_inv_cancel₀ (show (u:ℂ)≠0 by exact_mod_cast g),one_smul]; rw [pow_two,Complex.coe_smul, ← Complex.ofReal_mul,Complex.coe_smul]; abel
 let W:=wedgeQ A (cutM p); have hv:T*W=(L+u • (cutM q))*W:=by unfold T offerP; unfold L W; simp only [add_mul,Algebra.smul_mul_assoc, b.rimLeft,smul_zero,zero_add, Complex.coe_smul]; abel -- tune
 unfold house; rw [mul_add (offerP p q u)]; rw [←Complex.coe_smul u (wedgeP A (cutM p))] -- tune
 change _ + (L+u • (cutM q))*W = T*((u:ℂ) • V)+T*W; rw [hv,Algebra.mul_smul_comm,←Algebra.smul_mul_assoc,he]
lemma shed (u:ℝ)(h:Task A x): acts (quant (u • wedgeP A (cutM p)+wedgeQ A (cutM p))) x=(u:ℂ)^p.card • x:=by
 let T:=wedgeP A (cutM p); let U:=u • T+wedgeQ A (cutM p); have he:U=A+((u:ℂ)-1) • T:=by unfold U; rw [sub_smul,one_smul,Complex.coe_smul]; change u • T+(A-T)=_; abel
 have hl:U*A=U:=by rw [he,add_mul,Algebra.smul_mul_assoc,b.sailP,b.a.isIdempotentElem] -- tune
 have ht:A*U=U:=by rw [he,mul_add,Algebra.mul_smul_comm,b.spanP,b.a.isIdempotentElem]
 rw [h.sitting U (by show A*U=_; rw [hl,ht])]; rw [hutch,ht,hl,he,show A+((u:ℂ)-1) • T+(1-A)=1+((u:ℂ)-1) • T from by abel,det_rank (P:=T) (p:=b.drawn) p.card (b.tE.trans (trace_cut _)),add_sub_cancel _ _] -- check T match
lemma beetle (d:Disjoint p q)(s:Task A x){u:ℝ}(e:u≠0): acts (quant (house A (cutM p) (cutM q) u)) x=acts (grab p q u) x:=by rw [pedal b e,quant_mul,act_mul,shed b u s,map_smul, ←act_smul, contracts (by exact_mod_cast e) d]
theorem migrate (d:Disjoint p q)(s:Task A x) : acts (quant (house A (cutM p) (cutM q) 0)) x=acts (cabin p q) x:=by
 let f(u:ℝ):=acts (quant (house A (cutM p) (cutM q) u)) x; let g(u:ℝ):= acts (grab p q u) x; have ht:Continuous f:=by unfold f house; fun_prop
 have hp:Continuous g:= acts_cont.comp ((coals ..).comp Complex.continuous_ofReal)|>.clm_apply continuous_const
 have he:f 0=g 0:= tendsto_nhds_unique_of_eventuallyEq (ht.continuousWithinAt (x:=0) (s:={0}ᶜ)) (hp.continuousWithinAt (x:=0)) (by filter_upwards [self_mem_nhdsWithin] with u hu; exact beetle b d s hu)
 unfold f g at he; simpa only [Complex.ofReal_zero, permit_spec] using he
end YM.CF.BProof.Wick
