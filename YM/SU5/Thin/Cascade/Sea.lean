import YM.SU5.Relativistic.Raspa
import YM.CF.Gall.Geld
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Rapids
open Function Filter NormedSpace Fock Thera Finset
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
lemma settled (V:Op I) (p:0≤V): ‖V.det‖ ≤ Real.exp ((V-1).trace.re):=by
 obtain ⟨U,d,e⟩:= spectral_exists V (IsSelfAdjoint.of_nonneg p); subst V; rw [←spectral_zero U,spectral_le] at p
 rw [← spectral_one U,spectral_sub,spectral,spectral,det_twist,trace_twist,Matrix.trace_diagonal, Matrix.det_diagonal,norm_prod]; push_cast -- tune
 have he(i:I): ‖(↑(d i):ℂ)‖ ≤ Real.exp (d i-1):=by have hx:= Real.add_one_le_exp (d i-1); rw [Complex.norm_real, Real.norm_of_nonneg (p i)]; linarith
 rw [show ( (∑ i:I, (↑((d-1) i):ℂ):ℂ)).re= (∑ i:I, (d i-1)) from (?_), Real.exp_sum]
 · exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>he i)
 rw [←Complex.ofReal_sum,Complex.ofReal_re]; rfl

-- In the BASIS norm, not Maximal. Matrix is l2 operator in lean; DriveL1 entry ports here.
abbrev DriveL1 (A:Op I) : ℝ:= ∑ i:I,∑ j:I, ‖A i j‖
structure SnowCone (A:Op I)(C:ℝ):Prop where
  right (i:I) : ‖acts A (basisKet i)‖≤ C
  left (i:I) : ‖acts (star A) (basisKet i)‖ ≤ C
namespace SnowCone
variable {A B:Op I}{t u:ℝ}
lemma pilot [Nonempty I] (e:‖A‖≤t): SnowCone A t:=by
 constructor
 · intro i; have he:=Flare.opy A (basisKet i); rw [show ‖basisKet i‖=1 from by simp,mul_one] at he; exact he.trans e
 intro i; have he:=Flare.opy (star A) (basisKet i); rw [show ‖basisKet i‖=1 from by simp,norm_star,mul_one] at he; exact he.trans e
lemma solo : SnowCone (1:Op I) 1:=by constructor<;> intro i <;> simp [act_one]
lemma pose (p:SnowCone A t): SnowCone (star A) t:=by constructor; exact p.left; rw [star_star]; exact p.right
lemma add (p: SnowCone A t)(q:SnowCone B u): SnowCone (A+B) (t+u):= by
 constructor
 · intro i; rw [act_add]; exact (norm_add_le ..).trans (add_le_add (p.right i) (q.right i))
 intro i; rw [star_add,act_add]; exact (norm_add_le ..).trans (add_le_add (p.left i) (q.left i))
lemma neg (p:SnowCone A t): SnowCone (-A) t:=by constructor; intro i; rw [act_neg,norm_neg]; exact p.right i; intro i; rw [star_neg,act_neg,norm_neg]; exact p.left i
lemma mono (p:SnowCone A t)(q:t≤u):SnowCone A u:= ⟨fun i=>(p.right i).trans q,fun i=>(p.left i).trans q⟩
lemma entry [Nonempty I](p:SnowCone A t)(i j:I) : ‖(star A*A-1) i j‖ ≤ t^2+1:=by
 have hg:(star A*A) i j= inner ℂ (acts A (basisKet i)) (acts A (basisKet j)):=by rw [←basis_act (star A*A) i j,←basis_inner,act_mul,←act_inner,star_star]
 rw [Matrix.sub_apply,hg]; apply (norm_sub_le ..).trans; apply add_le_add
 · rw [sq]; exact (norm_inner_le_norm (𝕜:=ℂ) (acts A _) (acts A _)).trans (mul_le_mul (p.right i) (p.right j) (norm_nonneg _) ((norm_nonneg _).trans (p.right i)))
 exact (norm_entry (1:Op I) _ _).trans_eq norm_one
end SnowCone
lemma flowEntry (P Q:Op I) (t:ℝ)(h:∀ i j, ‖P i j‖ ≤ t): ‖(P*Q).trace‖ ≤ t* DriveL1 Q:=by
 let F(i j:I):ℝ:=‖Q j i‖; have he: ‖(P*Q).trace‖ ≤ ∑ i:I,∑ j:I, t* F i j:=by
    apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=> (norm_sum_le ..).trans ?_; exact Finset.sum_le_sum fun j _=> (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _))
 simp_rw [←mul_sum] at he; rw [sum_comm] at he; exact he -- trace simp may need change
lemma ship_le (A S T:Op I)(p:IsStarProjection S)(t:IsStarProjection T)(ht:A*T=T)(U:Wave I)(u:Sea S U)(w:ℝ)
  (hv: ((star A*A-1)*(S-T)).trace.re ≤ w): ‖acts (quant A) U‖ ≤ Real.exp (w/2):=by
 let L:=star A*A-1; let Q:=S*L*S; have ht':T*(star A*A)*T=T:=by
    have hz:T*star A=T:=by nth_rw 1 [←t.2]; rw [←star_mul,ht,t.2]; -- tune
    rw [←mul_assoc T,hz]; -- equals `T*A*T`. assoc to A*T
    rw [mul_assoc,ht,t.isIdempotentElem.eq]
 let x:=S*(star A*A)*S+(1-S); have hx:0≤ x:=by
    have hs:(star (A*S))*(A*S)= S*(star A*A)*S:=by rw [star_mul,p.2]; noncomm_ring
    rw [show x=_ from (show x=star (A*S)*(A*S)+(1-S) by rw [hs]), add_comm]; exact add_nonneg p.one_sub.nonneg (star_mul_self_nonneg _)
 have hh:(x-1).trace= Matrix.trace (L*(S-T)):=by
    have he:x-1=S*L*S:=by unfold L x; rw [mul_sub,sub_mul,mul_one,p.isIdempotentElem.eq]; abel
    have hₜ:T*L*T=0:=by unfold L; rw [mul_sub,sub_mul,mul_one,t.isIdempotentElem.eq,ht',sub_self]
    have hp (V:Op I)(e:IsStarProjection V): (V*L*V).trace=(L*V).trace:=by rw [mul_assoc,Matrix.trace_mul_comm V, mul_assoc L, e.isIdempotentElem.eq]

    rw [he,hp S p,mul_sub,Matrix.trace_sub,←hp T t,hₜ,Matrix.trace_zero,sub_zero]; -- note rw [mul_sub] on wrong?
 have he: ‖x.det‖= ‖acts (quant A) U‖^2:=by
    unfold x; rw [←meadow p U u (star A * A),skyGlow,quant_mul, quant_star,act_mul,←act_inner,star_star, inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
 apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp; rw [←he,←Real.exp_nat_mul]; refine (settled x hx).trans (Real.exp_monotone ?_); rw [hh]; push_cast; exact hv.trans_eq (by ring)
end YM.CF.Rapids
