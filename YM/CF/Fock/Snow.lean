import YM.CF.Fock.Rows

/-! Orientation-pinned particle--hole implementers. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
section
variable {I : Type*} [DecidableEq I] [Fintype I]
lemma one_des (X : Op I) : twist 1 X=X := by rw [twist_formula]; simp
lemma twin (U V : UNI I) (A : Op I) : twist (U*V) A=twist U (twist V A) := by
  rw [twist_formula,twist_formula,twist_formula]; change U.val*V.val*A*star (U.val*V.val)=_; rw [star_mul]; simp [mul_assoc]
lemma swivel (U : UNI I) (A : Op I) (x : Ket I) : acts U.val (acts A x) = acts (twist U A) (acts U.val x) := by
  rw [twist_formula,act_mul,act_unit,act_mul]
def phaseU (c : ℂ) (h : ‖c‖=1) : UNI I := ⟨c • (1:Op I),by
  constructor
  · rw [star_smul,star_one,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,smul_smul,scale_unit_self h,one_smul]
  rw [star_smul,star_one,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,smul_smul,mul_comm,scale_unit_self h,one_smul]⟩
lemma rankPhase (c : ℂ) (h : ‖c‖=1) (A : Op I) : twist (phaseU c h) A=A := by
  rw [twist_formula]; change c • 1*A*star (c • 1)=A; rw [star_smul, star_one,Algebra.smul_mul_assoc,one_mul,Algebra.mul_smul_comm,mul_one, smul_smul,scale_unit_self h,one_smul]
end
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma take_sq (i : n) : takeF i*takeF i=0 := by rw [takeF,← star_mul,put_sq,star_zero]
def switchM (i : n) : FC n := put i+takeF i
lemma switch_star (i : n) : star (switchM i)=switchM i := by simp only [switchM,takeF,star_add,star_star,add_comm]
lemma switch_unit (i : n) : switchM i*switchM i=1 := by
  rw [switchM,add_mul,mul_add,mul_add,put_sq,take_sq,zero_add,add_zero,add_comm,mixed]; exact if_pos rfl
def swapW (i : n) : UNI (Finset n) := ⟨switchM i,⟨by rw [switch_star,switch_unit],by rw [switch_star,switch_unit]⟩⟩
lemma push_swap (i : n) : twist (swapW i) (put i)=takeF i := by
  rw [twist_formula]; change switchM i*_ * star (switchM i)=_; rw [switch_star]
  have he : switchM i*put i=takeF i*switchM i := by rw [switchM,add_mul,put_sq,zero_add,mul_add,take_sq,add_zero]
  rw [he,mul_assoc,switch_unit,mul_one]
lemma push_aside (i j : n) (h : i≠j) : twist (swapW i) (put j)= -put j := by
  rw [twist_formula]; change switchM i*_ * star (switchM i)=_; rw [switch_star]
  have he : switchM i*put j= -(put j*switchM i) := by
    apply eq_neg_of_add_eq_zero_left
    rw [switchM,add_mul,mul_add,add_add_add_comm,put_put,mixed,if_neg h,zero_add]
  rw [he,neg_mul,mul_assoc,switch_unit,mul_one]
def blot (i j : n) : ℂ := if i=j then 1 else -1
def flipM (i : n) : Op n := Matrix.diagonal (blot i)
lemma flip_star (i : n) : star (flipM i)=flipM i := by
  ext r s; by_cases he:r=s
  · subst s; unfold flipM; by_cases h:i=r <;> simp [blot,h]
  simp [flipM,he,Ne.symm he]
lemma flip_sq (i : n) : flipM i*flipM i=1 := by
  unfold flipM; rw [Matrix.diagonal_mul_diagonal]
  ext r s; by_cases g:r=s
  · subst s; by_cases h:i=r <;> simp [blot,h]
  simp [g]
def flipU (i : n) : UNI n := ⟨flipM i,⟨by rw [flip_star,flip_sq],by rw [flip_star,flip_sq]⟩⟩
def frost (i : n) := swapW i * quantU (flipU i)
lemma frost_put (i j : n) : twist (frost i) (put j)=if i=j then takeF j else put j := by
  rw [frost,twin]; nth_rw 1 [←create_put j]; rw [twist_create,show (flipU i).val=flipM i from rfl,flipM,diag_basis]
  by_cases g : i=j
  · subst j; simp [blot, push_swap]
  simp only [if_neg g,map_neg,create_put,push_aside i j g,blot,neg_smul, one_smul,neg_neg]
lemma frost_take (i j : n) : twist (frost i) (takeF j)=if i=j then put j else takeF j := by
  rw [takeF,map_star,frost_put]; split <;> simp [takeF]
lemma frost_act (i : n) (s : Finset n) (h : i∉s) : ∃ c : ℂ, ‖c‖=1 ∧ acts (frost i).val (basisKet s)=c • basisKet (insert i s) := by
  let c := (∏ j∈s, blot i j)*parity i s
  have he : acts (frost i).val (basisKet s)=c • basisKet (insert i s) := by
    change acts (switchM i* quant (Matrix.diagonal (blot i))) _=_
    rw [act_mul,quant_diag,diag_basis,map_smul,switchM, act_add,put_act,take_act, if_neg h,if_neg h,add_zero,smul_smul]
  refine ⟨c,?_,he⟩
  have hh := congrArg norm he; rw [act_unit_norm,norm_smul] at hh; simpa [basisKet] using hh.symm

def drift (s : Finset n) (i : n) : FC n := if i∈s then takeF i else put i
lemma snowing (s : Finset n) : ∃ U : UNI (Finset n), (∀ i:n, twist U (put i)=drift s i) ∧ acts U.val (vacuum n)=basisKet s := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,(by intro i; simp [drift,one_des]),act_one _⟩
  | @insert i s hi ih =>
    obtain ⟨U,h,H⟩ := ih
    obtain ⟨c,g,e⟩ := frost_act i s hi
    refine ⟨phaseU (star c) (by simp [g])*(frost i*U),fun j=>?_,?_⟩
    · rw [twin,rankPhase,twin,h]; by_cases l:j=i
      · subst j; simp [drift,hi,frost_put]
      by_cases m:j∈s <;> simp [drift,m,frost_take,l,Ne.symm l,frost_put]
    change acts (star c • 1*((frost i).val*U.val)) _=_
    rw [act_mul,act_mul,H,e,act_smul,act_one,smul_smul,scale_unit_self g,one_smul]
def flake (s : Finset n) : UNI (Finset n) := (snowing s).choose
lemma flake_put (s : Finset n) (i : n) : twist (flake s) (put i)=drift s i := (snowing s).choose_spec.1 _
lemma flake_take (s : Finset n) (i : n) : twist (flake s) (takeF i)=star (drift s i) := by rw [takeF,map_star,flake_put]
lemma flake_vac (s : Finset n) : acts (flake s).val (vacuum n)=basisKet s := (snowing s).choose_spec.2
lemma flake_flip_p (s : Finset n) (i : n) : twist (star (flake s)) (drift s i)=put i := by rw [← flake_put s i, twist_inv]
lemma flake_flip_t (s : Finset n) (i : n) : twist (star (flake s)) (star (drift s i))=takeF i := by rw [map_star,flake_flip_p]
end YM.CF.Fock
