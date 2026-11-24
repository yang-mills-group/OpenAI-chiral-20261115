import GaugeFieldConstruction.Ridgelet
set_option autoImplicit false
set_option maxHeartbeats 25000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock.Flux
open Finset Function Filter Lattice NormedSpace Set TopologicalSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P:Op I}
variable {J:Type*}[DecidableEq J]{L W:FC I}{a b z B:ℝ}
local notation "O"=> Set.Icc (0:ℝ) 1
 
lemma trail (x:ℝ)(u:x∈O)(i: Wave I)(p:‖L‖ ≤ b)(v:b≤1/2): let j:=i+x • acts L i
    (inner ℂ j (acts L i)).re ≤ (quotation j L).re+2*b^2*‖j‖^2:=by
 intro j; have h:=Graph.spentS _ L i; have hk:=norm_nonneg i; have hb:0≤b:=(norm_nonneg L).trans p; have ht': ‖acts L i‖≤ b*‖i‖:= h.trans (mul_le_mul_of_nonneg_right p hk)
 have hs:0≤x:=u.1; have he: ‖i-j‖≤ b*‖i‖:=by unfold j; rw [show i-(i+x • acts L i)= -(x • acts L i) by abel,norm_neg,norm_smul,Real.norm_of_nonneg hs]; exact (mul_le_of_le_one_left (norm_nonneg _) u.2).trans ht'
 have hy: ‖i‖≤ 2*‖j‖:=by linarith only [(norm_sub_norm_le i j).trans he,mul_le_mul_of_nonneg_right v hk]
 let D:= inner ℂ j (acts L i); let E:= quotation j L
 have hw : D.re-E.re ≤ 2*b^2*‖j‖^2 :=by
    have h:D.re-E.re≤ ‖D-E‖:= ((Complex.sub_re ..).symm).le.trans ( (le_abs_self _).trans (Complex.abs_re_le_norm _))
    apply h.trans; unfold D E quotation; rw [←inner_sub_right,←map_sub];
    apply (norm_inner_le_norm ..).trans; apply (mul_le_mul_of_nonneg_left ((Graph.spentS _ L (i-j)).trans (mul_le_mul p (he.trans (mul_le_mul_of_nonneg_left hy hb)) (norm_nonneg _) hb)) (norm_nonneg _)).trans_eq; ring
 change D.re≤ E.re+_; linarith only [hw]
lemma quoteScaleV (P:FC I)(u:Wave I)(a:ℝ): quotation (a • u) P=a^2 • quotation u P:=by unfold quotation; rw [← Complex.coe_smul, map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal, ← Complex.coe_smul (a^2),Complex.ofReal_pow,smul_eq_mul]; ring
lemma unit_sales (q: Finset J)(T:J→FC I)(t:∀ v:Wave I,‖v‖=1→ ∑ i∈q,(quotation v (T i)).re ≤ febrile P v + B) (v:Wave I) :
 ∑ i∈q,(quotation v (T i)).re ≤ febrile P v + ‖v‖^2 * B:=by
 let a:=‖v‖; by_cases p:v=0; · simp [p,quotation,febrile]
 let V:= a⁻¹ • v; have hp:0<a:=norm_pos_iff.mpr p; have he:a • V=v:= smul_inv_smul₀ hp.ne' _
 have hq:‖V‖=1:=by unfold V; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le]; exact inv_mul_cancel₀ hp.ne'
 have hh(T:FC I): (quotation v T).re=a^2*(quotation V T).re:=by nth_rw 1 [←he]; rw [quoteScaleV,←Complex.coe_smul (a^2),smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] -- names
 have ht:febrile P v=a^2*febrile P V:= hh (excite P); simp_rw [hh]; rw [← Finset.mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left (t V hq) (sq_nonneg a)); rw [ht,mul_add]
lemma shrink_F (p:IsStarProjection P)(T:J→FC I)(q:List J)(h:q.Nodup)(t:∀ i∈q,∀ j∈q,Commute (T i) (T j))(u:Wave I)
  (y:ℝ)(v:y ∈ O)(l:b≤1/2)(dP:∀ i∈q,‖tradeKm P T y i‖ ≤ b)(ht:∀ v:Wave I,‖v‖=1 → ∑ i∈q.toFinset,(quotation v (tradeKm P T y i)).re ≤ febrile P v + a) :
 let F (x:ℝ):=acts (knight P (1-x)* flowing T q x) u
 (inner ℂ (F y) (deriv F y)).re ≤ (a+2*b^2*q.length)* ‖F y‖^2:=by
 intro F; let I:=q.toFinset; let Q:=F y; let W:= knight P (1-y)
 let L(i:J):=acts (W*T i*flowing T (q.erase i) y) u; let H:=tradeKm P T y
 have he: ∑ i∈I,(inner ℂ Q (L i)).re≤ febrile P Q+(a+2*b^2*q.length)*‖Q‖^2:=by
    refine le_trans (sum_le_sum (g:=fun j:J=> (quotation Q (H j)).re +2*b^2*‖Q‖^2) ?_) ?_
    · intro i p'; have hu:i∈q:= List.mem_toFinset.mp p'; obtain ⟨e,d⟩:= sliding q h u p T t y i hu; let X:=acts (W*flowing T (q.erase i) y) u; rw [show Q=_ from e, show L i=_ from d]; exact trail _ v X (dP i hu) l
    have hL:I.card=q.length:= List.toFinset_card_of_nodup h
    rw [sum_add_distrib, sum_const,nsmul_eq_mul,hL]; linarith only [unit_sales I H ht Q]
 have hz: deriv F y= -(acts (excite P) Q)+ ∑ i∈I,L i:= (tide_k T p q h t y u).deriv
 rw [hz,inner_add_right,inner_neg_right,inner_sum,Complex.add_re, Complex.re_sum, Complex.neg_re];
 change -febrile P Q + (∑ i∈I,(inner ℂ Q (L i)).re) ≤ _*‖Q‖^2; linarith only [he]
lemma evolve (F:ℝ→ Wave I)(C:ℝ)(h:Differentiable ℝ F)(t:∀ x, x∈O → (inner ℂ (F x) (deriv F x)).re ≤ C* ‖F x‖^2) : ‖F 1‖ ≤ Real.exp C * ‖F 0‖:=by
 let q(t:ℝ):= Real.exp (-2*t*C)*‖F t‖^2; let r(x:ℝ):= (inner ℂ (F x) (deriv F x)).re
 have hg:∀ x:ℝ, HasDerivAt q (Real.exp (-2*x*C)*(2*r x- 2*C*‖F x‖^2)) x:=by
    intro x; have hz:= (h x).hasDerivAt; have hv:= Complex.reCLM.hasFDerivAt (x:=inner ℂ (F x) (F x));
    have he : HasDerivAt (fun y:ℝ=> (inner ℂ (F y) (F y)).re) (((inner ℂ (F x) (deriv F x))+(inner ℂ (deriv F x) (F x))).re) x:=by exact hv.comp_hasDerivAt x (hz.inner (𝕜:=ℂ) hz)
    have ht: HasDerivAt (fun y=> ‖F y‖^2) (2*r x) x:=by
       unfold r; have hE: (inner ℂ (deriv F x) (F x)).re=(inner ℂ (F x) (deriv F x)).re:= by nth_rw 1 [←inner_conj_symm]; exact Complex.conj_re _
       rw [show (fun y=> ‖F y‖^2)=(fun y=>(inner ℂ (F y) (F y)).re) from funext (fun i=> (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm)]; apply he.congr_deriv; rw [Complex.add_re,hE,two_mul] -- careful simp recursion!
    have hh : HasDerivAt (fun x:ℝ=> -2*x*C) (-2*C) x:=by simpa using! (((hasDerivAt_id' (𝕜:=ℝ) x).const_mul (-2:ℝ)).mul_const C)
    apply (hh.exp.mul ht).congr_deriv; ring
 have hv:q 1≤q 0:= (antitoneOn_of_deriv_nonpos (convex_Icc _ _) ((show Continuous q from continuous_iff_continuousAt.mpr fun i=> (hg i).continuousAt).continuousOn) (fun x _=>(hg x).differentiableAt.differentiableWithinAt) (fun x hx=>by rw [(hg _).deriv]; apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr ?_); unfold r; linarith only [t x (interior_subset hx)])) ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one
 unfold q at hv; rw [mul_one,mul_zero,zero_mul,Real.exp_zero,one_mul,neg_mul,Real.exp_neg,inv_mul_le_iff₀ (by positivity)] at hv
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp; rw [mul_pow,← Real.exp_nat_mul]; exact hv -- casts?
lemma flow_v (T:J→FC I)(q:List J): flowing T q 0=1:=by induction q with| nil=>rfl| cons j l ih=>change (1+(0:ℝ) • T j)* flowing T l 0=1; rw [zero_smul,ih,add_zero,mul_one]
lemma sealed_flow (p:IsStarProjection P)(T:J→FC I)(q:List J)(h:q.Nodup)(t:∀ i∈q,∀ j∈q,Commute (T i) (T j))(u:Wave I) (l:b≤1/2)(dP:∀ y∈O,∀ i∈q,‖tradeKm P T y i‖ ≤ b)(ht:∀ y∈O,∀ v:Wave I,‖v‖=1 → ∑ i∈q.toFinset,(quotation v (tradeKm P T y i)).re ≤ febrile P v + a): ‖acts (flowing T q 1) u‖ ≤ Real.exp (a+2*b^2*q.length)* ‖acts (knight P 1) u‖:=by
 let F (x:ℝ):= acts (knight P (1-x)*flowing T q x) u; have hx: ∀ i,DifferentiableAt ℝ F i:= fun i=> (tide_k T p q h t i u).differentiableAt
 have he:= evolve F (a+2*b^2*q.length) hx (fun i v=>shrink_F p T q h t u i v l (dP i v) (ht i v)); unfold F at he; rw [sub_self,sub_zero,knight_start,one_mul,flow_v,mul_one] at he; exact he
end YM.CF.Fock.Flux
end
