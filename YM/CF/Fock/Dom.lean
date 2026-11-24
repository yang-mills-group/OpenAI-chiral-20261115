import YM.CF.Fock.Complement

/-! Parity-graded state sectors, disjoint product rule at a coordinate vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset Function Filter NormedSpace
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
inductive Sector (S : Finset n) : Bool → FC n → Prop where
  | zero (b) : Sector S b 0
  | one : Sector S false 1
  | up : ∀ i∈S,Sector S true (put i)
  | down : ∀ i∈S,Sector S true (takeF i)
  | add {b P Q} : Sector S b P → Sector S b Q → Sector S b (P+Q)
  | mul {a b P Q} : Sector S a P → Sector S b Q → Sector S (a.xor b) (P*Q)
  | scale {b P} : Sector S b P→∀ c:ℂ,Sector S b (c • P)

variable {S T : Finset n} {a b c : Bool} {P Q A : FC n}
namespace Sector
lemma sumS {ι : Type*} (p : Finset ι) (x : ι→FC n) (e : ∀ i ∈ p,Sector S b (x i)) : Sector S b (∑ i∈p,x i) := by
  classical
  induction p using Finset.induction_on with
  | empty => rw [sum_empty]; apply zero
  | @insert i p l ih => rw [sum_insert l]; exact (e i (mem_insert_self ..)).add (ih (fun j g=>e j (mem_insert_of_mem g)))
lemma contr (h : Sector S b P) : Sector S b (star P) := by
  induction h with
  | zero => rw [star_zero]; apply zero
  | one => rw [star_one]; apply one
  | up i h => exact down i h
  | down i h => rw [takeF,star_star]; exact up i h
  | scale _ c ih => rw [star_smul]; exact ih.scale _
  | add _ _ ih it=> rw [star_add]; exact ih.add it
  | @mul a b p q _ _ ih it => rw [star_mul,Bool.xor_comm]; exact it.mul ih
lemma makeP (x : Ket n) (h : acts (cutM S) x=x) : Sector S true (create x) := by
  rw [create_def]; apply sumS; intro i _; by_cases g:i∈S
  · exact (up i g).scale _
  rw [show x.ofLp i=0 by nth_rw 1 [←h]; rw [cut_apply,if_neg g], zero_smul]; apply zero
lemma dotGrade (h : Sector S b P) : ∀ A t:Finset n, P A t≠0→∀ i∉ S,i∈t↔i∈A := by
  induction h with
  | zero=> simp
  | one=>
    intro A t h; rw [Matrix.one_apply] at h; split at h; subst t; tauto; tauto
  | up i k=>
    intro A t h j l; have hl : j≠i := fun u=> l (u ▸ k); rw [put_entry] at h; split_ifs at h with e hx; tauto; rw [hx]; simp only [mem_insert]; tauto; tauto -- tune
  | down i k=>
    intro A t h j l; have hl : j≠i := fun u=> l (u ▸ k); rw [take_entry] at h; split_ifs at h with e hx; rw [hx]; simp only [mem_erase]; tauto; tauto; tauto
  | @add b X Y _ _ ih it =>
    intro A t h; rw [Matrix.add_apply] at h; by_cases g:X A t=0; rw [g,zero_add] at h; exact it _ _ h; exact ih _ _ g
  | @mul a b X Y _ _ ih it =>
    intro A t h; rw [Matrix.mul_apply] at h; obtain ⟨j,_,k⟩ := exists_ne_zero_of_sum_ne_zero h; intro i l; exact (it j t (right_ne_zero_of_mul k) i l).trans (ih A j (left_ne_zero_of_mul k) i l)
  | scale h c ih =>
    intro A t H; rw [Matrix.smul_apply,smul_eq_mul] at H; exact ih _ _ (right_ne_zero_of_mul H)
def grainB (a b : Bool) : ℂ := if a && b then -1 else 1
lemma grain_swap (a b : Bool) : grainB a b=grainB b a := by cases a <;> cases b <;> rfl
lemma grain_self (a b) : grainB a b*grainB a b=1 := by cases a <;> cases b <;> simp [grainB]
private lemma row_inv (a b : Bool) (P Q : FC n) (h : P*Q=grainB a b • (Q*P)) : Q*P=grainB b a • (P*Q) := by rw [h,grain_swap a b,smul_smul, grain_self,one_smul]
private lemma secs (h : P*Q=grainB a b • (Q*P)) (e : P*A=grainB a c • (A*P)) : P*(Q*A) = grainB a (b.xor c) • (Q*A*P) := by
  have ht : grainB a (b.xor c)=grainB a b*grainB a c := by cases a <;> cases b <;> cases c <;> simp [grainB]
  rw [←mul_assoc,h, Algebra.smul_mul_assoc,mul_assoc,e, Algebra.mul_smul_comm, ←mul_assoc Q,smul_smul,ht]
private lemma edge_up (i) (k:i∈S) (g : Disjoint S T) (h : Sector T b P) : put i * P = grainB true b • (P*put i) := by
  induction h with
  | zero=> simp
  | one=> simp [grainB]
  | up j p=> simp only [grainB,Bool.and_true,ite_true, neg_smul,one_smul]; exact eq_neg_of_add_eq_zero_left (put_put ..)
  | down j p=>
    simp only [grainB,Bool.and_true,ite_true,neg_smul,one_smul]; exact eq_neg_of_add_eq_zero_left (by rw [add_comm,mixed]; exact if_neg (fun h=> disjoint_left.mp g (h.symm ▸ k) p))
  | add _ _ ih it => rw [mul_add, add_mul,ih,it,smul_add]
  | mul _ _ ih it => exact secs ih it
  | @scale b p h c ih => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ih,smul_comm c]
theorem apart (e : Sector S a A) (h : Sector T b P) (g : Disjoint S T) : A*P=grainB a b • (P*A) := by
  induction e with
  | zero=> simp
  | one=> simp [grainB]
  | up i k=> exact edge_up _ k g h
  | down i k=>
    apply row_inv b true _ _
    have he := congrArg star (edge_up _ k g h.contr)
    have hx : star (grainB true b) = grainB b true := by cases b <;> simp [grainB]
    rw [star_smul,hx,star_mul, star_mul,star_star] at he; exact he
  | add _ _ ih it=> rw [add_mul,mul_add,ih,it,smul_add]
  | mul _ _ ih it=> exact row_inv _ _ _ _ (secs (row_inv _ _ _ _ ih) (row_inv _ _ _ _ it))
  | @scale b p h c ih=> rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,ih,smul_comm c]
lemma grade_diag (e : Sector S a A) : twist (quantU (phaseU (-1) (by simp))) A=(if a then (-1:ℂ) else 1) • A := by
  let U : UNI n := phaseU (-1) (by simp); have he i : twist (quantU U) (put i)=(-1:ℂ) • put i := by rw [←create_put i,twist_create,show acts _ (basisKet i)=(-1:ℂ) • basisKet i by rw [show U.val=(-1:ℂ) • 1 from rfl,act_smul,act_one],map_smul]
  induction e with
  | zero => simp
  | one => simp
  | up i k=> exact he i
  | down i k=> change twist (quantU U) (star (put i))=(-1:ℂ) • takeF i; rw [map_star,he,star_smul]; simp
  | add _ _ ih it=> rw [map_add, ih,it,smul_add]
  | @mul a b p q _ _ ih it=> rw [map_mul,ih,it]; cases a <;> cases b <;> simp
  | scale _ c ih=> rw [twist_scalar, ih, smul_comm c]
lemma odd_lost (h : Sector S true A) (t : Finset n) : A t t=0 := by
  have he := grade_diag h; rw [if_pos rfl] at he; let U : UNI n := phaseU (-1) (by simp)
  have hu : U.val=Matrix.diagonal fun _=> -1 := by change (-1:ℂ) • (1:Op n)= _; ext i j; by_cases g:i=j <;> simp [g]
  have ht : A t t= -A t t := by
    rw [twist_formula] at he; change quant U.val*A*star (quant U.val)=(-1:ℂ) • A at he
    rw [←quant_star,show star U.val=U.val by rw [show U.val=(-1:ℂ) • 1 from rfl,star_smul]; simp, hu, quant_diag] at he
    have H := Matrix.ext_iff.mpr he t t
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at H
    simp only [prod_const,Matrix.smul_apply, neg_smul,one_smul] at H
    rwa [mul_right_comm,←mul_pow,neg_mul_neg,one_mul,one_pow,one_mul] at H
  exact add_self_eq_zero.mp (add_eq_zero_iff_eq_neg.mpr ht)
lemma sliced (e : Sector S a P) (h : Sector T b A) (g : Disjoint S T) (k : Finset n) : (P*A) k k= P k k*A k k := by
  rw [Matrix.mul_apply,sum_eq_single _]
  · intro i _ hi; by_contra hp; apply hi; ext j
    -- each
    by_cases l:j∈S
    · exact (h.dotGrade i k (right_ne_zero_of_mul hp) j (fun p=>disjoint_left.mp g l p)).symm
    exact e.dotGrade k i (left_ne_zero_of_mul hp) j l
  simp
end Sector
end YM.CF.Fock
