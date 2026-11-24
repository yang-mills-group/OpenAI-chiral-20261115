import YM.CF.Fock.Grade

/-! Filled-band one-dimensional Fock projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]

def chooseK (N k : ℕ) (r : ℂ) : ℂ := ∏ j∈ (range (N+1)).erase k, (r-j)/((k:ℂ)-j)
lemma choose_nat (N k j : ℕ) (h : j≤N) : chooseK N k j=if j=k then 1 else 0 := by
  by_cases g : j=k
  · subst j; rw [chooseK,if_pos rfl,prod_eq_one]
    intro l hl; rw [div_self]; apply sub_ne_zero.mpr
    exact_mod_cast (mem_erase.mp hl).1.symm
  rw [chooseK,if_neg g]; exact prod_eq_zero (mem_erase.mpr ⟨g,mem_range.mpr (Nat.lt_add_one_of_le h)⟩) (by simp)
def lineOp (P : Op n) : FC n := quant P * ∑ k∈range (Fintype.card n+1), chooseK (Fintype.card n) k P.trace • selector n k
@[fun_prop] lemma line_cont : Continuous (lineOp (n:=n)) := by
  have h (k : ℕ) : Continuous (chooseK (Fintype.card n) k) := by unfold chooseK; fun_prop
  apply quant_cont.mul
  exact continuous_finsetSum _ (fun i _ => ((h i).comp (continuous_id.matrix_trace)).smul continuous_const)
lemma quant_twist (U : UNI n) (P : Op n) : quant (twist U P)=twist (quantU U) (quant P) := by rw [twist_formula,quant_mul,quant_mul,quant_star,twist_formula]; rfl
lemma twist_selector (U : UNI n) (k : ℕ) : twist (quantU U) (selector n k)=selector n k := by
  rw [twist_formula]; have h : quant U.val*star (quant U.val)=1 := (quantU U).property.2
  change quant U.val*_ * star (quant U.val)=_; rw [selector_quant,mul_assoc,h,mul_one]
section helpers
variable {I : Type*} [DecidableEq I] [Fintype I]
lemma trace_twist (U : UNI I) (P : Op I) : (twist U P).trace=P.trace := by
  rw [twist_formula,Matrix.trace_mul_comm, ← mul_assoc,show star U.val*U.val=1 from U.property.1,one_mul]
lemma trace_cut (s : Finset I) : (cutM s).trace=(s.card:ℂ) := by
  rw [cutM,Matrix.trace_diagonal,←sum_filter]; simp
lemma twist_scalar (U : UNI I) (P : Op I) (c : ℂ) : twist U (c • P)=c • twist U P := by
  rw [twist_formula,twist_formula,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma cut_apply (s : Finset I) (x : Ket I) (i) : (acts (cutM s) x).ofLp i=if i∈s then x.ofLp i else 0 := by
  rw [cutM,diag_apply]; by_cases h:i∈s <;> simp [h]
lemma cut_basis (s : Finset I) (i : I) : acts (cutM s) (basisKet i) = if i∈s then basisKet i else 0 := by
  rw [cutM,diag_basis]; by_cases h:i∈s <;> simp [h]
lemma cut_oneAct (i : I) (x : Ket I) : acts (cutM {i}) x=x.ofLp i • basisKet i := by
  apply PiLp.ext; intro j; rw [cut_apply]; by_cases h:j=i <;> simp [h]
end helpers
lemma line_twist (U : UNI n) (P : Op n) : lineOp (twist U P) = twist (quantU U) (lineOp P) := by
  unfold lineOp; rw [trace_twist,quant_twist,map_mul,map_sum]; simp_rw [twist_scalar,twist_selector]
lemma cutLine (s : Finset n) : lineOp (cutM s) = cutM {s} := by
  rw [lineOp,trace_cut,quantCut]
  simp_rw [choose_nat _ _ _ (card_le_univ _),ite_smul,one_smul,zero_smul]; rw [sum_ite_eq]
  rw [if_pos (mem_range.mpr (Nat.lt_add_one_of_le (card_le_univ _))),selector]
  apply op_columns; intro i
  rw [act_mul,cut_basis,cut_basis {s}]
  by_cases h:i=s
  · subst s; simp only [mem_filter,mem_univ,true_and,ite_true, mem_singleton]; rw [cut_basis]; simp
  simp only [mem_filter,mem_univ,true_and,mem_singleton,h,ite_false]; by_cases g:i.card=s.card
  · rw [if_pos g,cut_basis]; exact if_neg (fun he => h (eq_of_subset_of_card_le (mem_powerset.mp he) g.ge))
  rw [if_neg g,map_zero]
lemma line_proj {P : Op n} (h : IsStarProjection P) : IsStarProjection (lineOp P) := by
  obtain ⟨U,s,rfl⟩ := spot_projection P h
  rw [line_twist,cutLine]
  let Q := cutM {s}; let V := quantU U
  have H : Q*Q=Q := (cutM_idp _).1; have hq : star Q=Q := (cutM_idp _).2
  change IsStarProjection (twist V Q)
  constructor
  · unfold IsIdempotentElem; rw [← map_mul,H]
  unfold IsSelfAdjoint; rw [← map_star,hq]
lemma line_trace {P : Op n} (h : IsStarProjection P) : (lineOp P).trace=1 := by
  obtain ⟨U,s,rfl⟩ := spot_projection P h; rw [line_twist,cutLine,trace_twist,trace_cut]; simp
lemma act_twistLine (U : UNI n) (s : Finset n) (x : Wave n) :
    acts (lineOp (twist U (cutM s))) x=inner ℂ (wedge U.val s) x • wedge U.val s := by
  rw [line_twist,cutLine,twist_formula,act_mul,act_mul,cut_oneAct,map_smul, ← basis_inner, ← quant_column]
  congr 1
  change _=inner ℂ (acts (quantU U).val (basisKet s)) x
  nth_rw 2 [← star_star (quantU U).val]; rw [act_inner]
lemma line_quant {P : Op n} (h : IsStarProjection P) : quant P * lineOp P=lineOp P := by
  rw [lineOp,← mul_assoc,← quant_mul,show P*P=P from h.isIdempotentElem]
lemma quant_line {P : Op n} (h : IsStarProjection P) : lineOp P*quant P=lineOp P := by
  have he := congrArg star (line_quant h); rw [star_mul,← quant_star, h.isSelfAdjoint,(line_proj h).isSelfAdjoint] at he; exact he

/-- Kets in the top degree over this projection, of unit norm. -/
def Sea (P : Op n) (p : Wave n) : Prop := acts (lineOp P) p=p ∧ ‖p‖=1
lemma wedge_norm (U : UNI n) (s : Finset n) : ‖wedge U.val s‖=1 := by
  rw [← quant_column]; change ‖acts (quantU U).val _‖=_; rw [act_unit_norm]; simp [basisKet]
lemma scale_unit_self {c : ℂ} (h : ‖c‖=1) : star c*c=1 := by
  have he : inner ℂ c c=1 := by rw [inner_self_eq_norm_sq_to_K,h]; simp
  change c*star c=1 at he; rwa [mul_comm]
lemma Sea.scalar {P : Op n} {p : Wave n} (u : IsStarProjection P) (h : Sea P p) (x : Wave n) :
    acts (lineOp P) x=inner ℂ p x • p := by
  obtain ⟨U,s,rfl⟩ := spot_projection P u
  rw [act_twistLine]
  let w := wedge U.val s
  let c := inner ℂ w p
  have he : p=c • w := h.1.symm.trans (act_twistLine ..)
  have hb := h.2; rw [he,norm_smul,show ‖w‖=1 from wedge_norm U s,mul_one] at hb
  change inner ℂ w x • w=_; rw [he,inner_smul_left,smul_smul]
  change _=(star c*inner ℂ w x*c) • w
  rw [mul_right_comm,scale_unit_self hb,one_mul]
end YM.CF.Fock
