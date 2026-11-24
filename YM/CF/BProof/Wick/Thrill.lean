import YM.CF.BProof.Wick.Grad
/-! Bra derivative path. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Thera Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I]
lemma woven (A B:Op I): Commute (coupl A) (coupl B):=by
 have he(a b:I): Commute (put a*put b) (coupl B):= Commute.mul_left (show Commute _ _ from put_coupl ..) (show Commute _ _ from put_coupl ..)
 unfold Commute SemiconjBy
 conv_lhs=> arg 1; unfold coupl squareP
 conv_rhs=> arg 2; unfold coupl squareP
 simp_rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,sum_mul,mul_sum,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; simp_rw [(he _ _).eq]

lemma curvJ (A B: Op I): coupl (A+B)=coupl A+coupl B:= by unfold coupl; rw [show squareP (A+B)=squareP A+squareP B from dyad_plus A B put put,smul_add]
def hedge(I:Type)[Fintype I][LinearOrder I]: Op I →L[ℝ] FC I :=
 (({ toFun:=coupl, map_add':= curvJ, map_smul':=fun c x=>by unfold coupl squareP; simp [smul_sum,smul_smul,mul_left_comm,mul_comm,mul_assoc] } : Op I →ₗ[ℂ] FC I).toContinuousLinearMap.restrictScalars ℝ)
variable {A:ℝ→Op I}{B:Op I}{r:ℝ}(h:HasDerivAt A B r)
include h
-- use power derivative and terminating series
private theorem powered (i:ℕ): HasDerivAt (fun x=>coupl (A x)^(i+1)) ((i+1:ℂ) • (coupl B*coupl (A r)^i)) r:=by
 have he:HasDerivAt (fun x=>coupl (A x)) (coupl B) r:= (hedge I).hasFDerivAt.comp_hasDerivAt r h
 induction i with
 | zero=> simpa using he
 | succ i ih=>
   rw [show (fun x=>coupl (A x)^(i+1+1))=(fun x=>coupl (A x)^(i+1)* coupl (A x)) from funext fun x=>pow_succ ..]
   apply (ih.fun_mul he).congr_deriv
   rw [Algebra.smul_mul_assoc, (woven _ _|>.pow_left (i+1)).eq, mul_assoc,←pow_succ]; push_cast; module
private theorem yieldT (i:ℕ) : HasDerivAt (fun x=>pairTerm (A x) (i+1)) (acts (coupl B) (pairTerm (A r) i)) r:=by
 unfold pairTerm; refine ((act_der_const (powered h i) (vacuum I)).const_smul ((↑((i+1).factorial):ℂ)⁻¹)).congr_deriv ?_ -- tune
 rw [act_smul,act_mul,map_smul,smul_smul]; congr 1; rw [Nat.factorial_succ]; push_cast; field_simp
lemma turn : HasDerivAt (fun x=> pairWave (A x)) (acts (coupl B) (pairWave (A r))) r:=by
 unfold pairWave
 let N:= Fintype.card I
 have hv:acts (coupl B) (pairTerm (A r) N)=0:= ((term_degree (A r) N).couplD B).too_big (by unfold N; omega)
 rw [map_sum,sum_range_succ (fun i=>acts (coupl B) (pairTerm (A r) i)), show acts (coupl B) (pairTerm _ (Fintype.card I))=_ from hv]; simp_rw [sum_range_succ' (fun i=>pairTerm (A _) i),pairTerm_zero]
 exact (HasDerivAt.fun_sum (fun i (_:i∈ Finset.range (Fintype.card I))=> yieldT h i)).fun_add (hasDerivAt_const r _)
end YM.CF.BProof.Wick
