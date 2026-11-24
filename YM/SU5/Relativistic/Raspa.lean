import YM.SU5.Relativistic.Canini
import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-! # determinant cost for opposing the sum of mask moves, on real occupied sea. Uses basis-free trace of leakage. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Thera Finset
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
namespace Pea
variable (A B:Pea I) {P:Op I}
abbrev candy:= (2:ℝ)^(A.nodes)
/-- incorrect marked occupations counting P. -/
def frost(P: Op I):= Matrix.trace (A.fill*(1-P)+A.pour*P)
def leak (P:Op I):ℝ:= (A.frost P).re
lemma added {A B:Pea I}(p:Zones A B)(P:Op I): p.fuse.leak P=A.leak P+B.leak P:=by
 unfold leak frost Zones.fuse; simp only [add_mul, Matrix.trace_add,Complex.add_re]; abel
lemma divin {A B:Pea I}(p:Zones A B): p.fuse.candy=A.candy*B.candy:=by unfold candy; rw [nodF p, pow_add]
private lemma sat (V:Op I) (p:0≤V): ‖V.det‖ ≤ Real.exp ((V-1).trace.re):=by
 obtain ⟨U,d,e⟩:= spectral_exists V (IsSelfAdjoint.of_nonneg p); subst V; rw [←spectral_zero U,spectral_le] at p
 rw [← spectral_one U,spectral_sub,spectral,spectral,det_twist,trace_twist,Matrix.trace_diagonal, Matrix.det_diagonal,norm_prod]; push_cast -- tune
 have he(i:I): ‖(↑(d i):ℂ)‖ ≤ Real.exp (d i-1):=by have hx:= Real.add_one_le_exp (d i-1); rw [Complex.norm_real, Real.norm_of_nonneg (p i)]; linarith
 rw [show ( (∑ i:I, (↑((d-1) i):ℂ):ℂ)).re= (∑ i:I, (d i-1)) from (?_), Real.exp_sum]
 · exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>he i)
 rw [←Complex.ofReal_sum,Complex.ofReal_re]; rfl
private lemma flo (X:Op I): ‖X.det‖^2≤ Real.exp ((star X*X-1).trace.re):=by
 apply (sat _ (star_mul_self_nonneg X)).trans'; apply le_of_eq; rw [pow_two,Matrix.det_mul,norm_mul,show ‖(star X).det‖ = ‖X.det‖ from (?_)]
 rw [show star X=X.conjTranspose from rfl, Matrix.det_conjTranspose,norm_star] -- tune
local notation "F" => A.fill
local notation "D" => A.pour
local notation "S" => A.mint.sell
lemma duty : 0<A.candy:= by unfold candy; positivity
private lemma nations (p:IsStarProjection P): let C:=F*(1-P)+D*P; Matrix.trace (star C*C)= A.frost P ∧ Matrix.trace (star C)=A.frost P:=by
 intro C; let V:= 1-P
 have he:star C*C=V*F*V+P*D*P:=by
    unfold C; simp only [star_add,star_mul,A.home.isSelfAdjoint.star_eq,A.water.isSelfAdjoint.star_eq,p.isSelfAdjoint.star_eq,p.one_sub.isSelfAdjoint.star_eq]
    change (V*F+P*D)*(F*V+D*P)=_
    rw [add_mul,mul_add,mul_add,←mul_assoc (V*F),←mul_assoc (P*D),←mul_assoc (V*F),←mul_assoc (P*D)] -- fragile
    rw [mul_assoc V F F,A.home.isIdempotentElem.eq,mul_assoc P D D,A.water.isIdempotentElem.eq,mul_assoc V F D,mul_assoc P D F,A.leg,A.lic]; simp
 constructor
 · unfold frost; rw [he,Matrix.trace_add,Matrix.trace_add,mul_assoc V F V, Matrix.trace_mul_comm V, mul_assoc F V V, show V*V=V from p.one_sub.isIdempotentElem, mul_assoc P D P, Matrix.trace_mul_comm P,mul_assoc D P P,p.isIdempotentElem.eq]
 unfold C frost; rw [star_add,star_mul,star_mul,p.one_sub.isSelfAdjoint,p.isSelfAdjoint,A.home.isSelfAdjoint,A.water.isSelfAdjoint,Matrix.trace_add,Matrix.trace_add,Matrix.trace_mul_comm _ F,Matrix.trace_mul_comm _ D]
private lemma sucker (p:IsStarProjection P):
    (↑(A.candy):ℂ)^2 * (P*(S*S)*P+(1-P)).det=
       (1+(3:ℂ) • (F*(1-P)+D*P)).det:=by
 let V:=(-3/4:ℂ) • F+(3:ℂ) • D; let U:=(3:ℂ) • F
 have he:S*S=1+V:=by
    change A.Φ _ _*A.Φ _ _=_; rw [A.philosophy]; unfold Φ V
    ext i j; simp [Complex.real_smul]; ring -- tune
 have hh:(P*(S*S)*P+(1-P)).det=(1+V*P).det:=by
    rw [he]; rw [show P*(1+V)*P+(1-P)=1+P*V*P from (by rw [mul_add P,add_mul,mul_one,p.isIdempotentElem.eq]; abel)]
    rw [mul_assoc, Matrix.det_one_add_mul_comm, mul_assoc V,p.isIdempotentElem.eq]
 have hv: (↑A.candy:ℂ)^2=(1+U).det:=by
    obtain ⟨T,s,d⟩:= spot_projection F A.home
    unfold candy; rw [A.nodes_spec _ _ d]; unfold U; rw [d, ←twist_scalar,←map_one (twist T),←map_add,det_twist]
    let f(i:I):ℂ:= if i∈s then 4 else 1
    rw [show (1:Op I)+ (3:ℂ) • cutM s=Matrix.diagonal f from (by ext i j; by_cases h:i=j; subst j; by_cases g:i∈s <;> simp [cutM,f,g]<;> norm_num; simp [cutM,h]),Matrix.det_diagonal]; unfold f; rw [prod_ite,prod_const,prod_const_one,mul_one,filter_mem_eq_inter,univ_inter]; push_cast; rw [←pow_mul,pow_mul']; norm_num -- tune
 rw [hv,hh,←Matrix.det_mul]; congr 1
 unfold U V; simp only [mul_add,add_mul,one_mul,mul_one, Algebra.mul_smul_comm,Algebra.smul_mul_assoc, mul_sub]; rw [←mul_assoc F F,A.home.isIdempotentElem.eq, ←mul_assoc F D,A.leg]; simp only [zero_mul, smul_zero]; module
lemma frosty (p:IsStarProjection P) (f:Wave I)(x:Sea P f): ‖(↑A.candy:ℂ) • acts (quant S) f‖ ≤ Real.exp (4*A.leak P):=by
 let C:=F*(1-P)+D*P
 let X:=1+(3:ℂ) • C
 let D':=(A.frost P)
 let V:= (↑A.candy:ℂ) • acts (quant S) f
 have ht: inner ℂ V V=X.det:=by
    rw [show X.det = (↑A.candy:ℂ)^2*(P*(S*S)*P+(1-P)).det from (A.sucker p).symm, ← meadow p f x]; unfold V skyGlow; rw [quant_mul,act_mul,inner_smul_left,inner_smul_right]; rw [show (starRingEnd ℂ) (↑A.candy:ℂ)= _ from (show (starRingEnd ℂ) (↑A.candy:ℂ)=(↑A.candy:ℂ) from (by exact Complex.conj_ofReal A.candy))]
    have he:star S=S:= (A.tale _ _).star_eq
    nth_rw 1 [←star_star (quant S)]; rw [act_inner,← quant_star,he]; ring
 have hv : ‖V‖^4 ≤ Real.exp (16*A.leak P):=by
    have hh: ‖X.det‖=‖V‖^2:=by rw [←ht,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    obtain ⟨ha,hb⟩:= A.nations p
    have hx:0≤ (star C*C).trace:=(Matrix.nonneg_iff_posSemidef.mp (star_mul_self_nonneg _)).trace_nonneg
    have hp:0≤ A.leak P:= (ha ▸ hx).1
    have hg:(star X*X-1).trace=15*D':=by
       have he:star X*X-1=((3:ℂ) • C+(3:ℂ) • star C)+(9:ℂ) • (star C*C):=by
          unfold X; rw [star_add,star_one,star_smul,show star (3:ℂ)=3 by simp, add_mul,mul_add,mul_add,mul_one,one_mul,mul_one,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; module -- tune
       rw [he,Matrix.trace_add,Matrix.trace_add, Matrix.trace_smul,Matrix.trace_smul, Matrix.trace_smul, ha, hb]; change ((3:ℂ)*D'+3*D')+9*D'=_; ring
    apply le_trans _ ((flo X).trans (Real.exp_monotone _))
    · rw [hh]; exact le_of_eq (by ring)
    rw [hg]; change (15 *D').re ≤ 16*(D').re; norm_num [Complex.mul_re]; change 0≤ D'.re at hp; linarith only [hp]
 apply le_of_pow_le_pow_left₀ (n:=4) (by norm_num) (Real.exp_pos _).le; rw [←Real.exp_nat_mul]; exact hv.trans_eq (by push_cast; congr 1; ring)
end Pea
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.Pea.frosty
