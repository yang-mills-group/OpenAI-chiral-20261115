import YM.CF.Fock.Glacier

/-! Complementary minors unsuited to an absolute sign only; logarithmic differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset NormedSpace
attribute [local instance] opCStarAlgebra
section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma val_con (U V : UNI I) : congrC U V.val∈ unitary _ := by rw [congr_form]; exact (U * V * star (ccU U)).property
lemma congr_norm (U : UNI I) (A : Op I) : ‖congrC U A‖=‖A‖ := by
  rw [congr_form]; change ‖U.val*A*(star (ccU U)).val‖=_; rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
lemma mat_det_norm (V : UNI I) : ‖V.val.det‖=1 := by
  let C := V.val
  have he : Matrix.det C * Matrix.det (star C)=1 := by rw [← Matrix.det_mul,show C*star C=1 from V.property.2,Matrix.det_one]
  have hQ := congrArg norm he; rw [norm_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at hQ
  simp at hQ; change ‖C.det‖=1; nlinarith [norm_nonneg C.det]
end
variable {n : Type*} [LinearOrder n] [Fintype n]
def autumn (n : Type*) [LinearOrder n] [Fintype n] := flake (@univ n _)
lemma top_swap (i : n) : twist (autumn n) (put i)=takeF i := by rw [autumn, flake_put,drift,if_pos (mem_univ _)]
lemma bend (s : Finset n) : ∃ c : ℂ, ‖c‖=1 ∧ acts (autumn n).val (basisKet s)=c • basisKet sᶜ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,norm_one,by simp [show acts (autumn n).val (basisKet ∅)=basisKet univ from flake_vac univ]⟩ -- norm_one syntax
  | @insert i s e ih =>
    obtain ⟨c,-,h⟩ := ih
    let A := parity i s*(c*parity i sᶜ)
    have he : acts (autumn n).val (basisKet (insert i s))=A • basisKet (insert i s)ᶜ := by
      rw [create_basis_is i s e,map_smul,swivel (autumn n),top_swap,h,map_smul,take_act,if_pos (by simp [e]), show sᶜ.erase i=(insert i s)ᶜ by ext j; simp, smul_smul,smul_smul,mul_assoc]
    refine ⟨A,?_,he⟩; have hQ := congrArg norm he; rw [act_unit_norm,norm_smul] at hQ; simpa [basisKet] using hQ.symm
lemma full_map (A : Op n) : acts (quant A) (basisKet (@univ n _))=A.det • basisKet univ := by
  apply PiLp.ext; intro i; by_cases h:i=univ
  · rw [h,basis_act,volume]; simp
  have H : i.card≠(univ:Finset n).card := fun e=>h (eq_of_subset_of_card_le (subset_univ i) e.ge); simp [h,quant_grade _ _ _ H]
lemma carried_inv (V : UNI n) :
    twist (star (autumn n)) (quant V.val)= V.val.det • quant (cc V.val) := by
  let L := autumn n; let A := quant V.val; let B := quant (cc V.val); let F := twist (star L) A
  have he (i : n) : twist L (create (acts (cc V.val) (basisKet i)))=remove (acts V.val (basisKet i)) := by
    rw [create_def,remove_def]; simp_rw [map_sum,twist_scalar,show ∀ i:n, twist L (put i)=takeF i from top_swap,basis_act]; rfl
  have hf i : F*put i=create (acts (cc V.val) (basisKet i))*F := by
    apply (twist L).injective
    have hk : twist L F=A := by
      have hx : twist (star (star L)) F=A := twist_inv (star L) A; simpa only [star_star] using hx
    change twist L (F*put i)=twist L (create (acts (cc V.val) (basisKet i))*F)
    rw [map_mul,map_mul,he,hk,show twist L (put i)=takeF i from top_swap i]
    have h : takeF i=remove (basisKet i) := (remove_take i).symm
    rw [h,quant_ann,act_unit]
  apply op_columns; intro s
  change acts F _=acts (_ • B) _; rw [act_smul]
  induction s using Finset.induction_on with
  | empty =>
    change acts F (vacuum _) = _ • acts (quant _) (vacuum _); unfold F; rw [twist_formula]; change acts (star L.val*A*star (star L.val)) _=_
    have hm : acts L.val (vacuum n)=basisKet univ := flake_vac univ
    rw [act_mul,star_star,hm,act_mul, show acts A (basisKet univ)=V.val.det • basisKet univ from full_map _,map_smul,←hm,act_unit,quant_vac]
  | @insert i s e ih =>
    rw [create_basis_is i s e,map_smul,map_smul,←act_mul,hf,act_mul, ih,map_smul, ←act_mul B, show B*put i=create _ *B from quant_put (cc V.val) i,act_mul,smul_comm]
lemma autumn_diag (V : UNI n) (s : Finset n) : quant V.val sᶜ sᶜ= V.val.det * quant (cc V.val) s s := by
  have h (A : FC n) (p : Finset n) : inner ℂ (basisKet p) (acts A (basisKet p))=A p p := by simp
  obtain ⟨c,hc,H⟩ := bend s; let A := quant V.val; let B := twist (star (autumn n)) A
  have ht : B s s=A sᶜ sᶜ := by
    rw [←h B s]; unfold B; rw [twist_formula]; let L := autumn n
    change inner ℂ _ (acts (star L.val*A*star (star L.val)) _)=_; rw [act_mul, star_star,act_mul, ←act_inner (star L.val), star_star]
    change inner ℂ (acts (autumn n).val (basisKet s)) (acts A (acts (autumn n).val (basisKet s)))=_
    rw [H,map_smul,inner_smul_left,inner_smul_right]; change star c*(c*_) =_; rw [←mul_assoc,scale_unit_self hc,one_mul,h]
  unfold B A at ht; rw [carried_inv] at ht; exact ht.symm
lemma compPf (V : UNI n) (k : V.valᵀ= -V.val) (s : Finset n) : pf V.val sᶜ ^2= V.val.det*star (pf V.val s^2) := by
  rw [pf_square _ _ k,pf_square _ _ k,autumn_diag,cc,quant_transvol,quant_star]; rfl
lemma compNorm (V : UNI n) (k : V.valᵀ= -V.val) (s : Finset n) : ‖pf V.val sᶜ‖=‖pf V.val s‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] -- check
  rw [←norm_pow,←norm_pow,compPf V k,norm_mul,mat_det_norm,norm_star,one_mul]
lemma compStratum (U V : UNI n) (s : Finset n) (k : V.valᵀ= -V.val) : stratum U sᶜ V.val ^ 2=(congrC (star U) V.val).det* star (stratum U s V.val ^2) := by
  rw [stratum_pf,stratum_pf]; exact compPf ⟨_,val_con (star U) V⟩ (skew_form k) s
lemma compFilled {P : Op n} (h : IsStarProjection P) (V : UNI n) (k : V.valᵀ= -V.val) : ‖filled (1-P) V.val‖=‖filled P V.val‖ := by
  obtain ⟨U,s,rfl⟩ := spot_projection P h
  rw [show 1-twist U (cutM s)=twist U (cutM sᶜ) by rw [dim_cut s,map_sub,map_one],placed,placed,norm_smul,norm_smul,
    wedge_norm,wedge_norm,mul_one,mul_one,stratum_pf,stratum_pf]; exact compNorm ⟨_, val_con (star U) V⟩ (skew_form k) s
lemma frame_shift (U V : UNI n) (A : Op n) (s : Finset n) : stratum (U*V) s (congrC U A)=stratum V s A := by
  have h : wedge (U*V).val s=acts (quantU U).val (wedge V.val s) := by
    rw [←quant_column,← quant_column]; change acts (quant (U.val*V.val)) _=_; rw [quant_mul,act_mul]; rfl
  rw [stratum,stratum,congrC, h,←pair_cov]; exact act_unit_inner ..
end YM.CF.Fock
