import YM.CF.Fock.Semig

/-! Onsite Gaussian about a fixed sea. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset Function Filter NormedSpace
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
-- at a skew unitary commuting with P=cut A
lemma cut_unit {s : Finset n} (V : UNI n) (h : Commute (cutM s) V.val) :
    stage (cutM s) V.val=V.val ∧ reserve (cutM s) V.val= cutM s*star V.val*cutM s ∧ driftB (cutM s) V.val=0 ∧ weldB (cutM s) V.val= cutM sᶜ* V.val*cutM sᶜ := by
  let P := cutM s; let Q := cutM sᶜ; let A := V.val
  have hk : P*A=A*P := h.eq; have he : Q=1-P := dim_cut s
  have ht : Q*A=A*Q := by rw [he,mul_sub,mul_one,sub_mul,one_mul,hk]
  have hp : IsStarProjection P := cutM_idp _; have hq : IsStarProjection Q := cutM_idp _
  have hu : star A * A=1 := V.property.1; have hz : A * star A=1 := V.property.2
  have hj : stage P A=A := by
    rw [stage,← he,body, body, show cc P=P from cut_real _, show cc Q=Q from cut_real _,hk,ht,mul_assoc,mul_assoc,hp.isIdempotentElem,hq.isIdempotentElem,←mul_add,he,add_sub_cancel,mul_one]
  have hi : P*star A=star A*P := by
    have HH := congrArg star hk; rw [star_mul,star_mul, hp.isSelfAdjoint] at HH; exact HH.symm
  have hR : reserve P A=P*star A*P := by
    rw [reserve,hj]; have hr : A⁻¹=star A := by conv_rhs => rw [←one_mul (star A),← (live (starU V)).2]; rw [mul_assoc,hz,mul_one] -- tune
    rw [hr,hi,mul_assoc,hp.isIdempotentElem]
  have hO : P*Q=0 := by rw [he,Porth hp]
  have hv : reserve P A*A=P := by rw [hR,hi,mul_assoc (star A),hp.isIdempotentElem,mul_assoc,hk,←mul_assoc,hu,one_mul]
  refine ⟨hj,hR,?_,?_⟩
  · change driftB P A=0; rw [driftB,hv, ←he,show cc Q=Q from cut_real _,hO,neg_zero]
  change weldB P A=Q*A*Q; rw [weldB,mul_assoc A,hv, ←he,show cc Q=Q from cut_real _,mul_sub,sub_mul, ←mul_assoc Q, mul_assoc (Q*A), hO,mul_zero,sub_zero]
def seedR (s : Finset n) (A : Op n) := (2:ℂ)⁻¹ • (dyad (cutM s*star A*cutM s) takeF takeF + dyad (cutM sᶜ * A*cutM sᶜ) put put)
lemma cut_ex (s : Finset n) (V : UNI n) (h : Commute (cutM s) V.val) : excite (cutM s) V.val=seedR s V.val := by
  obtain ⟨-,e,g,k⟩ := cut_unit V h
  unfold excite; rw [e,g,k]; simp [inning,seedR,dyad]
lemma pf_unit (s : Finset n) (V : UNI n) (L : V.valᵀ= -V.val) (h : Commute (cutM s) V.val) : ‖pf V.val s‖ = 1 := by
  have hp := pf_square s V.val L; have he := column_product h.symm.eq (star V.val)
  rw [show star V.val*V.val=1 from V.property.1,quant_one, Matrix.one_apply_eq, quant_star,Matrix.star_apply,←hp] at he
  have hk := congrArg norm he; rw [norm_mul,norm_one,norm_star, norm_pow] at hk
  have hB : ‖pf V.val s‖^2=1 := by
    generalize hx : ‖pf V.val s‖ ^ 2 = y at *; have hp : 0≤y := hx ▸ sq_nonneg _; nlinarith
  nlinarith [norm_nonneg (pf V.val s)]
lemma ripe (s : Finset n) (V : UNI n) (g : V.valᵀ= -V.val) (k : Commute (cutM s) V.val) : pairWave V.val=acts (exp (seedR s V.val)) (pf V.val s • basisKet s) := by
  have he := starU V; rw [←(cut_unit V k).1] at he -- occurrence tune
  rw [cut_warm s g he,cut_ex s V k,filled,cutLine,cut_oneAct]; rfl
lemma same_s (s : Finset n) : cc (cutM s)=cutM s := cut_real _
lemma Occup {S : Finset n} {A : Op n} (h : Aᵀ= -A) (e : A=cutM S*A*cutM S) : Sector S false (coupl A) := by
  unfold coupl; apply Sector.scale; unfold squareP; apply Sector.sumS; intro i _; apply Sector.sumS; intro j _
  by_cases g:i∈S ∧ j∈S; exact ((Sector.up _ g.1).mul (Sector.up _ g.2)).scale _
  rw [show A i j=0 by nth_rw 1 [e]; rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; split_ifs <;> first | tauto | simp,zero_smul]; apply Sector.zero
-- seedR formula theta reflection via block cutM s ∩ S etc.
lemma theta_dyadF (U : UNI n) (A : Op n) (f g : FN n) : theta U (dyad A f g) = dyad (cc A) (fun i=>theta U (f i)) (fun i=>theta U (g i)) := by simp only [dyad,theta_sum, theta_smul,theta_mul, cc_apply]
lemma dyad_cs (A : Op n) (f g : FN n) (c d : ℂ) : dyad A (fun i=>c • f i) (fun i=>d • g i)=(c*d) • dyad A f g := by
  unfold dyad; simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sum, smul_smul]; simp [mul_comm,mul_assoc,mul_left_comm]
lemma theta_s2 (U : UNI n) (A) : theta U (dyad A put put)= -dyad (cc (congrC U A)) takeF takeF := by
  rw [theta_dyadF]; simp only [theta_up,←prong_t]; rw [dyad_cs,dyad_prong]; simp only [neg_mul_neg,Complex.I_mul_I, congrC,cc_mul, neg_smul, one_smul]; rfl -- tune
lemma theta_h2 (U : UNI n) (A) : theta U (dyad A takeF takeF)= -dyad (congrC U (cc A)) put put := by
  rw [theta_dyadF]; simp only [theta_down,←prong_p]; rw [dyad_cs,dyad_prong]; simp only [Complex.I_mul_I,neg_smul,one_smul]; rfl
lemma dyad_minus (A : Op n) (f g) : dyad (-A) f g= -dyad A f g := by simp [dyad,sum_neg_distrib]
lemma theta_seed (s : Finset n) (U : UNI n) (A : Op n) (h : twist U (cutM sᶜ)=cutM s) (e : Aᵀ= -A) :
    theta U (seedR s A)= seedR s (congrC U A) := by
  -- theta F of skew C projection = skew star; theta holes(cc) = projection flipped.
  let P := cutM s; let Q := cutM sᶜ; let V := congrC U A
  have hq : twist U P=Q := by
    have ht : twist U (1-P)=P := by rw [show 1-P=Q from (dim_cut s).symm]; exact h
    rw [map_sub,map_one] at ht; rw [show Q=1-P from dim_cut s]; exact (sub_sub_cancel _ _).symm.trans (congrArg ((1:Op n)-·) ht) -- tune
  have hp {A : Op n} (g:Aᵀ= -A) : star A= -cc A := by
    have hk : cc (star A)= -A := by rw [cc,star_star]; exact g
    calc star A=cc (cc (star A)) := (cc_cc _).symm
         _ = _ := by rw [hk,cc_neg]
  have he : Vᵀ= -V := skew_form e
  rw [seedR,theta_smul,theta_add,theta_s2,theta_h2,seedR]; rw [show star (2:ℂ)⁻¹=(2:ℂ)⁻¹ by norm_num]; apply congrArg
  have H : congrC U (Q*A*Q)=P*V*P := by
    have hf := board_twist U Q A; rw [h] at hf; simpa only [body,same_s,V,P,Q] using hf.symm -- tune
  have V' : congrC U (P*A*P)=Q*V*Q := by
    have hf := board_twist U P A; rw [hq] at hf; simpa only [body,same_s,V,P,Q] using hf.symm
  change -dyad (congrC U (cc (P*star A*P))) put put+ -dyad (cc (congrC U (Q*A*Q))) takeF takeF= dyad (P*star V*P) takeF takeF+dyad (Q*V*Q) put put -- theta_h order check: A star leads.
  have ht : cc (P*(-cc A)*P)= -(P*A*P) := by rw [cc_mul,cc_mul,cc_neg,cc_cc,show cc P=P from cut_real _, mul_neg,neg_mul]
  rw [H,hp he,hp e,ht,show congrC U (-(P*A*P))= -(Q*V*Q) by rw [←V',congrC,congrC,mul_neg,neg_mul], dyad_minus, cc_mul,cc_mul, show cc P=P from cut_real _,mul_neg,neg_mul,dyad_minus,neg_neg,add_comm]
end YM.CF.Fock
