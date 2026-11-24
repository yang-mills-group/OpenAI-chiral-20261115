import YM.CF.Fock.CAR

set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]

/-- Ascending creation word after one-particle map. -/
def wedge (A : Op n) (s : Finset n) : Wave n :=
    acts (((s.sort (· ≤ ·)).map (fun i => create (acts A (basisKet i)))).prod) (vacuum n)
/-- All degrees second quantization. -/
def quant (A : Op n) : FC n := Matrix.of fun t s => (wedge A s).ofLp t
lemma quant_column (A : Op n) (s) : acts (quant A) (basisKet s)=wedge A s := by
  apply PiLp.ext; intro j; rw [basis_act]; rfl
lemma wedge_empty (A : Op n) : wedge A ∅=vacuum n := by simp [wedge]
lemma wedge_min (A : Op n) (s : Finset n) (i : n) (g : ∀ j∈s, i < j) :
    wedge A (insert i s)=acts (create (acts A (basisKet i))) (wedge A s) := by
  unfold wedge; rw [sort_insert _ (fun j h => (g j h).le) (fun h => lt_irrefl i (g i h)),List.map_cons,List.prod_cons,act_mul]
lemma wedge_any (A : Op n) (s : Finset n) (i : n) (g : i ∉ s) :
    wedge A (insert i s)=parity i s • acts (create (acts A (basisKet i))) (wedge A s) := by
  induction s using induction_on_min with
  | empty => rw [wedge_min _ _ _ (by simp)]; simp [parity]
  | insert j s h ih =>
    simp only [mem_insert,not_or] at g
    have he : j∉s := fun e => lt_irrefl _ (h j e)
    let B (i) := create (acts A (basisKet i))
    rcases lt_or_gt_of_ne g.1 with hx|hx
    · have hq : ∀ k ∈ insert j s, i < k := by
        intro k hk; rw [mem_insert] at hk
        exact hk.elim (fun l => l.symm ▸ hx) (fun l => hx.trans (h k l))
      rw [wedge_min A _ _ hq]; unfold parity; rw [Finset.filter_eq_empty_iff.mpr (fun _ l => not_lt.mpr (hq _ l).le)]
      simp
    have hq : ∀ k ∈ insert i s, j < k := by
      intro k hk; rw [mem_insert] at hk
      exact hk.elim (fun l => l.symm ▸ hx) (fun l => h k l)
    rw [insert_comm i j,wedge_min A _ _ hq, ih g.2,wedge_min A _ _ h,map_smul,
      parity_lo s i j hx he,← act_mul,← act_mul]
    change _ = _ • acts (B i*B j) _
    rw [show B i * B j= -(B j * B i) from eq_neg_of_add_eq_zero_left (car_create ..),act_neg]
    simp [B]
@[simp] lemma quant_vac (A : Op n) : acts (quant A) (vacuum n)=vacuum n := by rw [vacuum,quant_column,wedge_empty]
@[fun_prop] lemma quant_cont : Continuous (quant (n:=n)) := by
  have h (s : Finset n) : Continuous (fun A : Op n => wedge A s) := by
    induction s using induction_on_min with
    | empty => simp_rw [wedge_empty]; exact continuous_const
    | insert i s e ih =>
      simp_rw [wedge_min _ _ _ e]
      exact (acts_cont.comp (create_cont.comp (acts_cont.clm_apply continuous_const))).clm_apply ih
  exact continuous_matrix (fun i j => (PiLp.continuous_apply _ _ i).comp (h j))
lemma quant_put (A : Op n) (i : n) : quant A*put i=create (acts A (basisKet i))*quant A := by
  apply op_columns; intro s
  rw [act_mul,act_mul,quant_column,put_act]
  by_cases g:i∈s
  · rw [if_pos g,map_zero]; nth_rw 1 [← show insert i (s.erase i)=s from insert_erase g] -- tune occurrence
    rw [wedge_any _ _ _ (by simp),map_smul,← act_mul,create_sq,act_zero,smul_zero]
  rw [if_neg g,map_smul,quant_column,wedge_any _ _ _ g,smul_smul,parity_sq,one_smul]
lemma quant_create (A : Op n) (x : Ket n) : quant A*create x=create (acts A x)*quant A := by
  nth_rw 1 [create_def]; nth_rw 2 [← basis_expand x] -- occurrence
  simp_rw [map_sum,map_smul,mul_sum,sum_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,quant_put]
lemma create_basis_is (i : n) (s : Finset n) (g : i ∉ s) : basisKet (insert i s)=parity i s • acts (put i) (basisKet s) := by
  rw [put_act,if_neg g,smul_smul,parity_sq,one_smul]
lemma quant_unique (A : Op n) (X : FC n) (he : acts X (vacuum n)=vacuum n)
    (h : ∀ i:n, X*put i=create (acts A (basisKet i))*X) : X=quant A := by
  apply op_columns; intro s; induction s using Finset.induction_on with
  | empty => change acts X (vacuum _) = acts _ (vacuum _); rw [he,quant_vac]
  | @insert i s e ih =>
    rw [create_basis_is i s e,map_smul,map_smul,← act_mul,← act_mul,h,quant_put,act_mul,act_mul,ih]
lemma quant_mul (A B : Op n) : quant (A*B)=quant A*quant B := by
  symm; apply quant_unique
  · rw [act_mul,quant_vac,quant_vac]
  intro i; rw [mul_assoc,quant_put, ←mul_assoc,quant_create,mul_assoc,act_mul]
lemma quant_one : quant (1 : Op n)=1 := by symm; exact quant_unique _ _ (act_one _) (by intro i; simp)

lemma quant_ann (A : Op n) (x : Ket n) : remove x * quant A=quant A*remove (acts (star A) x) := by
  let L := quant A; let U := acts (star A) x
  apply op_columns; intro s
  induction s using Finset.induction_on with
  | empty => change acts (_*L) (vacuum _) = acts (L*_) (vacuum _); rw [act_mul,act_mul,show L=quant A from rfl,quant_vac,vacuum_take,vacuum_take,map_zero]
  | @insert i s g ih =>
    let c := create (acts A (basisKet i))
    let b := inner ℂ U (basisKet i)
    have hx : remove x * c=b • 1-c*remove x := by apply eq_sub_of_add_eq; unfold b U; rw [act_inner]; exact car ..
    have hy : remove U*put i=b • 1-put i*remove U := by apply eq_sub_of_add_eq; simpa only [create_put] using car U (basisKet i)
    change acts (_ * L) _=acts (L * remove U) _
    have h : L*put i=c*L := quant_put A i
    rw [create_basis_is i s g,map_smul,map_smul,← act_mul,← act_mul,mul_assoc,mul_assoc,h,
      ← mul_assoc (remove x),hx,hy,mul_sub,sub_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,
      one_mul,mul_one,← mul_assoc L,h,mul_assoc c,mul_assoc c,act_sub,act_sub,act_mul c,act_mul c]
    change _= _
    have hi : acts (remove x * L) (basisKet s)=acts (L * remove U) (basisKet s) := ih
    rw [hi]
lemma remove_vac_pair (A : Op n) : acts (star (quant A)) (vacuum n)=vacuum n := by
  apply PiLp.ext; intro s
  rw [← basis_inner,show inner ℂ (basisKet s) (acts (star (quant A)) (vacuum _)) =
        inner ℂ (acts (quant A) (basisKet s)) (vacuum n) by
    nth_rw 2 [← star_star (quant A)]; rw [act_inner]]
  by_cases e:s=∅
  · subst s; change inner ℂ (acts _ (vacuum _)) (vacuum _)=(vacuum _).ofLp _; rw [quant_vac]; exact basis_inner ..
  obtain ⟨i,h⟩ := nonempty_iff_ne_empty.mpr e
  rw [quant_column,← insert_erase h,wedge_any _ _ _ (by simp)]
  rw [inner_smul_left]
  nth_rw 1 [← star_star (create _)]
  rw [act_inner, show ∀ x:Ket n, acts (star (create x)) (vacuum n)=0 from vacuum_take,inner_zero_right,mul_zero,insert_erase h,vacuum,basis_apply,if_neg e]
lemma quant_star (A : Op n) : quant (star A)=star (quant A) := by
  symm; apply quant_unique _ _ (remove_vac_pair _); intro i
  have h := congrArg star (quant_ann A (basisKet i)); simpa [remove] using h

def quantU (U : UNI n) : UNI (Finset n) := ⟨quant U.val,by
    have he : star (quant U.val)*quant U.val=1 := by rw [← quant_star,← quant_mul,show star U.val*U.val=1 from U.property.1,quant_one]
    exact ⟨he,mul_eq_one_comm.mp he⟩⟩
lemma quantU_star (U : UNI n) : quantU (star U)=star (quantU U) := by apply Subtype.ext; exact quant_star U.val
lemma twist_create (U : UNI n) (x : Ket n) : twist (quantU U) (create x)=create (acts U.val x) := by
  rw [twist_formula]; change quant U.val * _*_=_; rw [quant_create,mul_assoc]
  have he : quant U.val*star (quantU U).val=1 := (quantU U).property.2; rw [he,mul_one]
lemma twist_remove (U : UNI n) (x : Ket n) : twist (quantU U) (remove x)=remove (acts U.val x) := by rw [remove,map_star,twist_create]
end YM.CF.Fock
