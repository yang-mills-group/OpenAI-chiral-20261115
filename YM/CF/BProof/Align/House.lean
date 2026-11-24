import YM.CF.BProof.Align.Speech
/-! prop:B-Pproj stretch case. Use Sᵤ exactly, never inverse of operator on arbitrary field. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I] {A P Q:Op I}{c:ℝ}{x:Ket I}
def house (A P Q:Op I)(u:ℝ):= (P+u • space P Q+u^2 • Q)*wedgeP A P+(space P Q+u • Q)*wedgeQ A P
def floorH (A P Q:Op I)(u:ℝ):= land A (house A P Q u)
def slopeH (c:ℝ) := c^2 / (2*c+1)
def Paid (c:ℝ):= min ((slopeH c)^2) 1
lemma slopeH_p (h:0<c):0<slopeH c:= by unfold slopeH; positivity
lemma paid_pos (h:0<c) : 0<Paid c := lt_min (pow_pos (slopeH_p h) _) one_pos
namespace Board
variable (b:Board A P Q c)
include b
lemma house_hit (u:ℝ): house A P Q u * A=house A P Q u:= by rw [house,add_mul,mul_assoc,mul_assoc _ (wedgeQ A P),b.sailP,b.sailQ]
lemma hitOne : house A P Q 1=A:=by
 rw [house,one_smul,one_smul,one_pow,one_smul]; let L:=space P Q; rw [show P+space P Q+Q=1 from by unfold space; abel,show space P Q+Q=1-P from by unfold space; abel,one_mul,sub_mul,b.rimLeft,one_mul,sub_zero,b.bins]
lemma on_front (u:ℝ): P*house A P Q u=P*wedgeP A P:=by
 rw [house,mul_add P,← mul_assoc P,←mul_assoc P]; simp only [mul_add, Algebra.mul_smul_comm, b.p.isIdempotentElem.eq,b.pw,b.pq,smul_zero,zero_mul,add_zero]
lemma on_rim (u:ℝ): space P Q*house A P Q u= u •(space P Q*wedgeP A P)+space P Q*wedgeQ A P:=by
 let L:=space P Q; have hp:L*P=0:=swapOrth b.p b.wall b.pw; have hq:L*Q=0:= swapOrth b.q b.wall b.qw; unfold house; change L*((P+u • L+u^2 • Q)*wedgeP A P + (L+u • Q)* _) = _; rw [mul_add L, ←mul_assoc L,←mul_assoc L]; simp only [mul_add, Algebra.mul_smul_comm,show L*L=L from b.wall.isIdempotentElem,hp,hq,smul_zero,zero_add,add_zero,Algebra.smul_mul_assoc]; rfl -- tune
variable [Nonempty I]
lemma lower (s:ℝ)(ht:‖s‖≤1)(x: Ket I): slopeH c*‖acts A x‖≤ ‖acts (house A P Q s) x‖:=by
 let L:=space P Q; let V:=wedgeP A P; let W:=wedgeQ A P; let u:=acts V x; let v:=acts W x; let y:= acts (house A P Q s) x
 have hh:c*‖u‖ ≤ ‖y‖:= ((b.avail (selfApply b.drawn x)).trans_eq (congrArg (‖·‖) (show acts P (acts V x)=acts P y from by rw [←act_mul, ←b.on_front s]; exact act_mul ..))).trans (funded b.p _)
 have ht:c*‖v‖ ≤ ‖y‖+‖u‖:=by
    have he: acts L v=acts L y-s • (acts L u):=by
      have he:= b.on_rim s; suffices h:acts L y=s • (acts L u)+acts L v by rw [h]; abel
      unfold L y; rw [← act_mul,he,act_add,act_dilate,act_mul, act_mul]
    apply (b.gramMil (x:=v) (selfApply b.leaves x)).trans; change ‖acts L v‖≤ _; rw [he]; apply (norm_sub_le ..).trans (add_le_add (funded b.wall _) ?_); rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (funded b.wall _)
 have hx: ‖acts A x‖≤‖u‖+‖v‖:=by apply (norm_add_le u v).trans'; nth_rw 1 [←b.bins]; rw [act_add]
 have hp:=b.nice; change slopeH c*‖acts A x‖≤‖y‖; rw [slopeH,div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<2*c+1)]
 nlinarith only [mul_le_mul_of_nonneg_left hh hp.le, hh, mul_le_mul_of_nonneg_left ht hp.le, mul_le_mul_of_nonneg_left hx (sq_nonneg c)]
theorem house_gear (s:ℝ)(h:‖s‖≤1): Paid c • (1:Op I) ≤ entered A (house A P Q s):=by
 let T:=house A P Q s; have hp:= paid_pos b.nice; apply by_hil (IsSelfAdjoint.of_nonneg (smul_nonneg hp.le zero_le_one)) (IsSelfAdjoint.of_nonneg (add_nonneg (star_mul_self_nonneg T) b.a.one_sub.nonneg)); intro x; rw [hil_linear,hil_one,hil_sum,hil_gram,hil_idem x b.a.one_sub,← splitOrth x b.a,mul_add]
 apply add_le_add ?_ (mul_le_of_le_one_left (sq_nonneg _) (min_le_right ..)); apply le_trans (mul_le_mul_of_nonneg_right (show Paid c≤_ from min_le_left ..) (sq_nonneg _)); rw [←mul_pow]; apply pow_le_pow_left₀ (mul_nonneg (slopeH_p b.nice).le (norm_nonneg _)) (b.lower s h x)
lemma houseFit (s:ℝ)(h:‖s‖≤1): Fit A (house A P Q s):= ⟨b.a,b.house_hit s,active (paid_pos b.nice) (b.house_gear s h)⟩
end Board
end YM.CF.BProof.Align
