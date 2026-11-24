import YM.CF.Aroma.Chive
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N M:Side}{J:InJ n N}
private lemma yump {U X Y: Cab n N} : U*X*U*X+U*Y*U*Y=(1/2:ℂ) • (U*(X+Complex.I • Y)*U*(X-Complex.I • Y)+U*(X-Complex.I • Y)*U*(X+Complex.I • Y)):=by simp only [mul_add,mul_sub,add_mul,sub_mul,Matrix.smul_mul,Matrix.mul_smul,smul_add,smul_sub]; simp_rw [smul_smul,Complex.I_mul_I]; module
namespace Foot
variable {T:Op n}{j:ℕ}(P:Foot T j M J){η C:ℝ}(U:Tween T j M N η C)(p:U.stem=oak J)(q:U.halo=float (Met J))
include P p
lemma wis (x:Momentum)(F:Tide N x)(h:∀ i:Site N,spoon (mel i) x∈realCube zone): let V:= Met J; let H:=subHub (fun i:Site N=> edgeH n j M (mel i))
 (H*firstH V x*H*star (firstH V x)).trace=∑ i:Site N,U.wheels (mel i) x:=by
 intro V H; let L:= fun i :Site N => U.rail (mel i) x; let f:=F.σ
 rw [show firstH V x=hub f L from P.railH _ _ F h p]; change (subHub _*hub f L * subHub _*star _).trace= _; rw [heart, lung, hub_star,hearts,trace_hub,←Equiv.sum_comp f]
 refine sum_congr rfl ?_; intro i _; change Matrix.trace _= Matrix.trace _; simp only [Equiv.symm_apply_apply]; rw [(slid_f _ F i (h i) j M).2,show star (mel i)=mel i from (mel_h i).1,show star x=x from F.phys] -- tune
include q
lemma ant (x:Momentum)(F:Tide N x): (subHub (fun i=> edgeH n j M (mel i))*secondH (Met J) x).trace=∑ i:Site N,U.sear (mel i) x:=by
 rw [P.paidU U x F q,show subHub _ *subHub _=_ from (heart (Equiv.refl (Site N)) (fun i=>edgeH n j M (mel i)) (fun i=> U.halo (x,mel i)))]; exact trace_hub _
lemma reel(x:Momentum)(F:Tide N x)(h:∀ i:Site N,spoon (mel i) x∈realCube zone)(k:∀ i: Site N,spoon (mel i) (-x)∈realCube zone):room J x= (∑ i:Site N, (U.wheels (mel i) x+U.wheels (mel i) (-x) - (U.sear (mel i) x+U.sear (mel i) (-x)) ).re)/4:=by
 let V:=Met J; let A:Cab n N:=flatV n N; let L:= subHub (fun i:Site N=> edgeH n j M (mel i)); let m:=(V 0)⁻¹
 have he:m=L+(1-A):=P.census.2
 let S(z:Air N):=JD V z; let Q(z:Air N):=JG V z z
 have heK(z): palmH J z=(1/2:ℝ)*((L*S z*L*S z - L* Q z).trace).re:=by
    have hx:=P.issue z; change palmH J z=(1/2:ℝ)*((m*S z*m*S z - m* Q z).trace).re at hx; have hS:m*S z=L*S z:=by rw [he,add_mul,sub_mul,one_mul,show A*S z=S z from (P.shadeM z).1,sub_self,add_zero]
    rw [mul_assoc _ m,hS,he,add_mul,sub_mul,show A*Q z=Q z from P.coinsY z,one_mul, sub_self,add_zero, ← mul_assoc _ L] at hx; exact hx
 let a:Air N:=amber x; let b:Air N:=zinnia x; let f:=firstH V x; let g:= firstH V (-x); let H:=L*S a*L*S a+L*S b*L*S b
 have hh: H= (1/2:ℂ) • (L*f*L*star f+L*g*L*star g):=by
    have he: g=S a-Complex.I • S b:=by unfold g firstH; rw [(aside F).1,(aside F).2,map_neg, smul_neg]; abel -- tune
    rw [show star f=g from by rw [← show star g=f from P.star_cost _ F,star_star],show star g=f from P.star_cost x F,he]; exact yump
 let T':=secondH V x; let W:=L* T'
 have hx: H-W=L*S a*L*S a-L*Q a+(L*S b*L*S b-L*Q b):=by
   have hz:T'= Q a+Q b:=rfl; unfold W H; rw [hz,mul_add]; abel
 have hk: secondH V (-x)=T':=by simp only [secondH,(aside F).1,(aside F).2,map_neg,ContinuousLinearMap.neg_apply,neg_neg]; rfl
 have hl := P.wis U p x F h; have hv:= P.wis U p (-x) (opp F) k
 change Matrix.trace _= _ at hl hv
 have hc : room J x=(1/2:ℝ)* ((H-W).trace).re:=by rw [room,heK,heK,hx, Matrix.trace_add, Complex.add_re, mul_add]
 have hp:= P.ant U p q x F; have hu:= P.ant U p q (-x) (opp F); change W.trace=_ at hp; rw [show secondH _ (-x)=_ from hk] at hu; change W.trace=_ at hu
 rw [hc,hh, Matrix.trace_sub, Matrix.trace_smul,Matrix.trace_add,show Matrix.trace _=_ from (hl : (L*f*L*star f).trace=_),show Matrix.trace _=_ from (hv :(L*g*L*star g).trace=_)]
 rw [← Complex.re_sum]; simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]; rw [← hp,←hu]; -- tune
 simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.add_re]; norm_num; ring
end Foot
end YM.CF.Aroma
