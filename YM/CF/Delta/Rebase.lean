import YM.CF.Ave.Home

/-! Log comparisons without branch winding. Uses overlapping positive bands. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock NormedSpace Branch Phase Function Finset Pastry Petal MeasureTheory Filter Ave
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma trace_near {P Q : Op n} (h : IsStarProjection P) (g : IsStarProjection Q) (e : ‖P-Q‖<1) : P.trace=Q.trace := by
  let R := 1-P; let S := 1-Q; let A:= P*Q + R*S; let M:= Q*P+S*R
  have hr : R*P=0 := by unfold R; rw [sub_mul,one_mul,h.isIdempotentElem,sub_self]
  have hs : S*Q=0 := by unfold S; rw [sub_mul,one_mul,g.isIdempotentElem,sub_self]
  have ht : A*M=1-(P-Q)*(P-Q) := by
    unfold A M; rw [add_mul,mul_add,mul_add,mul_assoc P Q, ←mul_assoc Q, g.isIdempotentElem,
      mul_assoc P Q (S*R), ←mul_assoc Q S, Porth g, zero_mul,mul_zero, mul_assoc R S (Q*P),←mul_assoc S Q,hs,zero_mul,mul_zero,
      add_zero,zero_add,mul_assoc R S (S*R),←mul_assoc S S R,show S*S=S from g.one_sub.isIdempotentElem]; unfold R S; rw [mul_sub (P-Q), sub_mul,sub_mul]; simp only [mul_sub,sub_mul,show P*P=P from h.isIdempotentElem,show Q*Q=Q from g.isIdempotentElem,one_mul,mul_one]; abel -- tune
  have he : IsUnit A := by
    have hz : IsUnit (1-(P-Q)*(P-Q)) := Units.isUnit (Units.oneSub ((P-Q)*(P-Q)) (show ‖(P-Q)*(P-Q)‖<1 from (norm_mul_le ..).trans_lt (by nlinarith [norm_nonneg (P-Q)]))) -- tune name
    have hx := live (show IsUnit (A*M) from ht.symm ▸ hz)
    apply live_of (S:=M*(A*M)⁻¹); rw [←mul_assoc,hx.1] -- tune T
  have hp : P*A=A*Q := by unfold A; rw [mul_add,add_mul,←mul_assoc P P,h.isIdempotentElem,←mul_assoc P R,Porth h,zero_mul,mul_assoc P Q Q, g.isIdempotentElem, mul_assoc R S Q,hs,mul_zero]
  calc
    P.trace=(P*A*A⁻¹).trace := by rw [mul_assoc,(live he).1,mul_one]
    _ = Q.trace := by rw [hp,Matrix.trace_mul_cycle,(live he).2,one_mul] -- tune
lemma area_line {P Q : Op n} (h : IsStarProjection P) (g : IsStarProjection Q) (p : ‖P-Q‖<1) : lineOp P*quant Q=lineOp P*lineOp Q := by
  obtain ⟨V,t,H⟩:= spot_projection Q g
  have he : Q.trace=(t.card:ℂ) := by rw [H, trace_twist,trace_cut]
  have hx : P.trace=(t.card:ℂ) := (trace_near h g p).trans he
  let A := selector n t.card
  have ht (W : Op n) (l : W.trace=t.card):lineOp W=quant W*A := by
    unfold lineOp; rw [l]; simp_rw [choose_nat _ _ _ (card_le_univ _),ite_smul,one_smul,zero_smul]; rw [sum_ite_eq,if_pos (mem_range.mpr (lt_of_le_of_lt (card_le_univ _) (by omega)))]
  rw [ht P hx, ht Q he, mul_assoc, mul_assoc (quant P) A, show A*(quant Q*A)= quant Q*A by rw [←mul_assoc,show A*quant Q=quant Q*A from (selector_quant _ _).symm,mul_assoc,show A*A=A from (cutM_idp _).isIdempotentElem],show A*quant Q=quant Q*A from (selector_quant _ _).symm]
lemma area {P Q : Op n} (C : Op n) (h : IsStarProjection P) (g : IsStarProjection Q) (p : ‖P-Q‖<1) : acts (lineOp P) (filled Q C) = filled P (body Q C) := by
  unfold filled; rw [←act_mul,←area_line h g p,act_mul,pair_cov]; unfold body; rw [cc,g.isSelfAdjoint]
lemma same_spark {P A : Op n} (p : IsStarProjection P) (k : IsUnit (stage P A)) : spark P A (body P A)=0 := by
  unfold spark; rw [show relay P A (body P A)=relay P A A by rw [relay,relay,show body P (body P A)=body P A from Eq.trans (congrArg (fun x=>x*cc P) (body_left p A)) (body_right p A)]]; exact spark_equal p k
lemma authentic {P A C : Op n} (p : IsStarProjection P) (g : IsUnit (stage P A)) (h : ‖relay P A C-1‖ < 1) (e : Aᵀ= -A) (w : Cᵀ= -C) (k : filled P A ≠ 0) : filled P C=Complex.exp (spark P A C) • filled P A := by
  let f (t:ℝ) := A+(t:ℂ) • (C-A); have h0 : f 0=A := by simp [f]
  have h1 : f 1=C := by simp [f]
  let S := Set.Icc (0:ℝ) 1
  have ht t (z:t∈S): ‖relay P A (f t)-1‖ < 1 := by
    have he : relay P A (f t)=1+(t:ℂ) • (relay P A C-1) := by nth_rw 1 2 [← relay_base p g]; unfold f relay body; simp only [add_mul,mul_add,mul_sub,sub_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_add,smul_sub]; abel
    rw [he, add_sub_cancel_left,norm_smul,Complex.norm_real,Real.norm_of_nonneg z.1]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) z.2) h
  have hp t : (f t)ᵀ= -f t:= by unfold f; rw [Matrix.transpose_add,Matrix.transpose_smul, Matrix.transpose_sub,w,e]; module -- tune
  obtain ⟨U,W,H⟩:= spot_projection P p
  have hx := strata_gap U W A (H ▸ k)
  have hl t (v:t∈S) := spark_sq U W e (hp t) (H ▸ g) (show ‖relay (twist U (cutM W)) A (f t)-1‖<1 from H ▸ ht t v)
  let F (i:ℝ):=Complex.exp (spark P A (f i))*stratum U W A; let G (i:ℝ):=stratum U W (f i)
  have hf : Continuous f:= by unfold f; fun_prop
  have hg : Continuous G:= continuous_const.inner (pairWave_cont.comp hf)
  have hF : ContinuousOn F S:= by
    intro i v
    let J t : Op n × Op n × Op n:=(P,A,f t)
    let D := fun t:Op n × Op n × Op n=>spark t.1 t.2.1 t.2.2
    exact (ContinuousAt.mul_const (Complex.continuous_exp.continuousAt.comp (show ContinuousAt (D ∘ J) i from (spark_contAt g (ht i v)).comp (f:=J) (continuous_const.prodMk (continuous_const.prodMk hf)).continuousAt)) _).continuousWithinAt
  have hv : G 1=F 1 := stalk (convex_Icc _ _|>.isPreconnected) hg.continuousOn hF 0 ⟨le_rfl,zero_le_one⟩ (fun i v=> by unfold G F; rw [mul_pow,H]; exact (hl i v).symm) (fun i _=>mul_ne_zero (Complex.exp_ne_zero _) hx) (by unfold F G; rw [h0,spark_equal p g]; simp) 1 ⟨zero_le_one,le_rfl⟩
  unfold F G at hv; rw [h1,H] at hv; rw [H,placed, placed,hv,smul_smul]
lemma polar_hitch {P Q A C : Op n} (p : IsStarProjection P) (q : IsStarProjection Q) (v : ‖P-Q‖<1) (g : IsUnit (stage P A)) (h : ‖relay P A (body Q C)-1‖<1) (e : Aᵀ= -A) (w : Cᵀ= -C) (k : filled P A≠0) : acts (lineOp P) (filled Q C)=Complex.exp (spark P A (body Q C)) • filled P A := by rw [area _ p q v,authentic p g h e (body_skew q w) k]
end YM.CF.Delta
