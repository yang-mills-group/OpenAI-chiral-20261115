import YM.CF.Reed.Skiff

/-! Exact identification of the band input chiral Gaussian, also rectangular. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock NormedSpace Function Finset Pastry Phase
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
-- representative bras handle a packed linear combination of words.
def syms (s : Finset n) : Poly n (LeanV n) where
  term i := if i∈s then bar i else col i
  anti i j:= by split <;> split <;> exact put_put ..
def think (s : Finset n) : Poly n n where
  term i:= if i∈s then put i else -takeF i
  anti i j:= by
    by_cases g:i∈s <;> by_cases h:j∈s <;> simp only [g,h,ite_true,ite_false]
    · exact put_put ..
    · unfold antiB; rw [mul_neg,neg_mul, ←neg_add,add_comm, mixed,if_neg (show j≠i from fun u=> h (u.symm ▸ g)),neg_zero]
    · unfold antiB; rw [neg_mul,mul_neg, ←neg_add,mixed,if_neg (show i≠j from fun u=>g (u.symm ▸ h)),neg_zero]
    unfold antiB; rw [neg_mul_neg, neg_mul_neg, take_take]
abbrev wordF {m : Type*} [LinearOrder m] [Fintype m] (v : Poly n m) (l : List n) := (l.map v.term).prod
lemma unspoken (s : Finset n) (l : List n) {i:n} (h : i∈s) : Absorb (avoid i) (wordF (syms s) l) := by
  induction l with
  | nil=> exact Absorb.one
  | cons j l ih=>
    rw [wordF,List.map_cons,List.prod_cons]; refine Absorb.times ?_ ih
    change Absorb _ (if j∈s then bar j else col j); by_cases g:j∈s; rw [if_pos g]; exact Absorb.blade (by simp [avoid]); rw [if_neg g]; exact Absorb.blade (by simp [avoid,show j≠i from fun u=>g (u.symm ▸ h)])
lemma word_abs (s : Finset n) (l : List n) : Plain (wordF (syms s) l) := by
  induction l with
  | nil=>exact Absorb.one
  | cons i l ih=>
    apply Absorb.times _ ih
    change Plain (if i∈s then bar i else col i); split_ifs <;> exact Absorb.blade (mem_univ _)
lemma whisper (s t : Finset n) (l : List n) : zap s t (wordF (syms s) l*jolt s)= wordF (think s) l s t := by
  induction l using List.reverseRecOn generalizing t with
  | nil=> change zap s t (1*jolt s)=(1:FC n) s t; rw [one_mul,jolt_all,zap_sum, Matrix.one_apply]
          by_cases g:s=t; subst s; rw [if_pos rfl]; simp_rw [zap_one]; simp
          rw [if_neg g,sum_eq_zero]; intro i _; rw [zap_one,if_neg]; exact fun p=>g ((Prod.mk.inj p).1.trans (Prod.mk.inj p).2.symm)
  | append_singleton l i ih=>
    let F:=wordF (syms s) l; let T:= F*jolt s; let V:= wordF (think s) l
    have he : wordF (syms s) (l++[i])= F*(syms s).term i := by simp [F,wordF]
    have hv : wordF (think s) (l++[i])=V*(think s).term i := by simp [V,wordF]
    rw [he,hv,←basis_act (V*(think s).term i),act_mul]; by_cases g:i∈s
    · rw [show (syms s).term i = bar i from if_pos g, bar_in _ _ g (unspoken s l g), show (think s).term i=put i from if_pos g, put_act]; by_cases h:i∈t
      · rw [if_pos h,if_pos h,map_zero]; rfl
      rw [if_neg h,if_neg h, map_smul,show zap s (insert i t) (F*jolt s)=_ from ih _,WithLp.ofLp_smul, Pi.smul_apply,basis_act]; rfl
    rw [show (syms s).term i=col i from if_neg g,mul_assoc, show col i*jolt s=jolt s*col i from Eq.symm (lost s (true,i)),←mul_assoc,
        gaze ((word_abs s l).times (jolt_abs s)),show (think s).term i= -takeF i from if_neg g,act_neg,take_act]; split_ifs with p
    · rw [map_neg,map_smul, WithLp.ofLp_neg,WithLp.ofLp_smul,Pi.neg_apply,Pi.smul_apply, basis_act,show zap s (t.erase i) (F*jolt s)=_ from ih _,neg_mul]; rfl
    rw [neg_zero,map_zero]; rfl
def chemical (A : Op n) (s t: Finset n) := -∑ i∈s, bar i*tote t A i
def spell (v : Poly n (LeanV n)) (P : Op n) (q s : Finset n) (A : FC n) := zap q s ((tube s P).eval (v.eval A)* exp (chemical P q s)) -- Poly input for convenience
lemma actionS (q t:Finset n) (U:Op n): exp (chemical U q t)=(tube t U).eval (jolt q) := by
  rw [jolt,eval_expose (plain_axis q)]; unfold chemical axis; rw [map_sum,←sum_neg_distrib]; congr 1; apply sum_congr rfl; intro i h
  rw [ballad,map_neg,Absorb.eval (show Plain (bar i) from Absorb.blade (mem_univ _)) (show Plain (col i) from Absorb.blade (mem_univ _)) _,tube_bar,tube_eta]
lemma wire_read (U : Op n) (A S T : Finset n) : spell (syms A) U A S (poke T)= inner ℂ (basisKet A) (acts ((think A).eval (poke T)) (wedge U S)) := by
  let P:= (syms A).tag T
  have hp : Plain P:= word_abs A _
  unfold spell; rw [Poly.eval_oneT,Poly.eval_oneT]; change zap _ _ ((tube S _).eval P * _)=_; rw [actionS,← Absorb.eval hp (jolt_abs A), zach _ (hp.times (jolt_abs A)),basis_inner, ←quant_column, ←act_mul,basis_act, Matrix.mul_apply]
  apply sum_congr rfl; intro i _; exact congrArg (fun x:ℂ=>x*_) (whisper A i _)
-- full-space conventional integral
lemma moment (U : Op n) (A S : Finset n) (P : FC n) (h : Plain P) : spell (syms A) U A S P = inner ℂ (basisKet A) (acts ((think A).eval P) (wedge U S)) := by
  rw [h.full]; unfold spell; simp only [map_sum,map_smul,sum_mul,Algebra.smul_mul_assoc,zap_sum,zap_s]
  -- simplify acts
  have he i: zap A S ((tube S U).eval ((syms A).eval (poke i))*exp (chemical U A S)) = inner ℂ (basisKet A) (acts ((think A).eval (poke i)) (wedge U S)) := wire_read ..
  simp_rw [he]; rw [ContinuousLinearMap.sum_apply,inner_sum]; apply sum_congr rfl; intro i _; rw [ContinuousLinearMap.smul_apply,inner_smul_right] -- tune map_sum
end YM.CF.Reed
