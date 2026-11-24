import YM.CF.Fock.Dom

/-! Explicit ordered creator words, expense and substitutions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Finset NormedSpace
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [LinearOrder n] [Fintype n] [LinearOrder m] [Fintype m]
-- for Hom into FC
structure Poly (n m : Type*) [LinearOrder m] [Fintype m] where
  term : n → FC m
  anti (i j:n) : antiB (term i) (term j)=0
variable (v : Poly n m)
namespace Poly
lemma square (i : n) : v.term i*v.term i=0 := by
  have h := v.anti i i
  ext a b; exact add_self_eq_zero.mp (Matrix.ext_iff.mpr h a b)
lemma swapV (i j) : v.term i*v.term j = -(v.term j*v.term i) := eq_neg_of_add_eq_zero_left (v.anti i j)
def tag (S : Finset n) := ((S.sort (· ≤ ·)).map v.term).prod
lemma tag_void : v.tag ∅=1 := by simp [tag]
lemma tag_min (S : Finset n) (i : n) (h : ∀ j∈S, i<j) : v.tag (insert i S)=v.term i * v.tag S := by unfold tag; rw [sort_insert _ (fun j p=>(h j p).le) (fun p=>lt_irrefl _ (h i p)), List.map_cons,List.prod_cons]
lemma tag_any (S : Finset n) (i : n) (p : i∉S) : v.tag (insert i S)=parity i S • (v.term i*v.tag S) := by
  induction S using induction_on_min with
  | empty=> rw [tag_min _ _ _ (by simp)]; simp [parity]
  | insert j S k ih=>
    rw [mem_insert,not_or] at p
    have he : j∉ S:= fun x=>lt_irrefl _ (k j x)
    rcases lt_or_gt_of_ne p.1 with l|l
    · have hq : ∀ x∈insert j S, i<x := fun x p=>(mem_insert.mp p).elim (fun e=>e.symm ▸ l) (fun e=>l.trans (k _ e))
      rw [tag_min _ _ _ hq]; unfold parity; rw [Finset.filter_eq_empty_iff.mpr (fun _ p=>not_lt.mpr (hq _ p).le)]; simp
    have hx : ∀ x∈insert i S,j<x := fun x p=>(mem_insert.mp p).elim (fun e=>e.symm ▸ l) (k x)
    rw [insert_comm i j,tag_min _ _ _ hx,ih p.2,tag_min _ _ _ k,parity_lo _ _ _ l he,Algebra.mul_smul_comm,←mul_assoc,←mul_assoc, swapV v j i,neg_smul,neg_mul,smul_neg]
lemma tag_once (i:n) : v.tag {i}=v.term i := by
  have he := tag_min v ∅ i (by simp); simpa [tag_void] using he
lemma tag_mute (S : Finset n) (i:n) (h:i∈S) : v.term i*v.tag S=0 := by rw [←insert_erase h,tag_any v _ _ (notMem_erase i S),Algebra.mul_smul_comm, ←mul_assoc, v.square,zero_mul,smul_zero]
-- type-independent structure constants
-- induct reduce product
def sail (S T : Finset n) : ℂ := ∏ i∈S, parity i T
lemma sail_size (S T : Finset n) : ‖sail S T‖=1 := by simp [sail,norm_prod,parity]
lemma tag_mul (S T : Finset n) : v.tag S * v.tag T= if Disjoint S T then sail S T • v.tag (S∪T) else 0 := by
  induction S using induction_on_min with
  | empty=> simp [tag_void,sail]
  | insert i S u ih=>
    have he : i∉S:= fun e=>lt_irrefl _ (u i e)
    rw [tag_min v _ _ u,mul_assoc,ih]
    have hp : parity i (S∪T)=parity i T := by
      unfold parity; rw [filter_union,filter_eq_empty_iff.mpr (fun x h=> not_lt.mpr (u x h).le),empty_union]
    by_cases h : Disjoint S T
    · rw [if_pos h]; by_cases g:i∈T
      · rw [Algebra.mul_smul_comm,v.tag_mute (S∪T) i (mem_union_right _ g),smul_zero, if_neg]; simp [g]
      have hx : i∉ S∪T := by simp [he,g]
      rw [Algebra.mul_smul_comm, if_pos (by simp [g,h]), insert_union, tag_any v _ _ hx,smul_smul,hp,sail,sail, prod_insert he, mul_right_comm,parity_sq,one_mul]
    rw [if_neg h,mul_zero,if_neg (fun p=> h (Disjoint.mono_left (subset_insert ..) p))]
lemma flip (S : Finset n) (i:n) : v.term i * v.tag S=(-1:ℂ)^S.card • (v.tag S*v.term i) := by
  induction S using induction_on_min with
  | empty=> simp [tag_void]
  | insert j S k ih=>
    rw [tag_min _ _ _ k, ←mul_assoc,v.swapV,neg_mul,mul_assoc,ih,Algebra.mul_smul_comm, card_insert_of_notMem (fun p=>lt_irrefl _ (k j p)),pow_succ',neg_mul,one_mul,neg_smul,mul_assoc]
lemma commute (S T : Finset n) (h : Even T.card) : Commute (v.tag S) (v.tag T) := by
  have he i : Commute (v.term i) (v.tag T) := by
    unfold Commute SemiconjBy; rw [v.flip T i,h.neg_one_pow,one_smul]
  induction S using induction_on_min with
  | empty=> rw [tag_void]; exact Commute.one_left _
  | insert i S p ih=> rw [tag_min _ _ _ p]; exact (he i).mul_left ih
end Poly

def cane (n : Type*) [LinearOrder n] [Fintype n] : Poly n n := ⟨put,put_put⟩
abbrev poke (S : Finset n) := (cane n).tag S
lemma poked (S : Finset n) : acts (poke S) (vacuum n)=basisKet S := by
  have he:=quant_column (1:Op n) S; rw [quant_one,act_one] at he; simpa [wedge,poke,Poly.tag,cane,Function.comp_def] using he.symm
def crumb (A : FC n) (S : Finset n) := A S ∅
lemma chip (S T : Finset n) : crumb (poke S) T=if T=S then 1 else 0 := by rw [crumb, ←basis_act (poke S) T ∅,vac_eq] -- tune
where vac_eq : (acts (poke S) (basisKet ∅)).ofLp T=if T=S then 1 else 0 := by rw [show acts _ _=basisKet S from poked S,basis_apply]
lemma tag_size (S : Finset n) : ‖poke S‖≤1 := by
  have ht i : ‖put (n:=n) i‖≤1 := by
    have he : IsStarProjection (takeF i*put i) := by
      have hx := op_scale_column (A:=takeF i*put i) (fun s:Finset n=> if i∈s then 0 else 1) (fun s=>by
        rw [vacant_act]; split <;> simp)
      rw [show takeF i*put i=cutM (univ.filter fun s=> i∉s) from hx.trans (by apply congrArg Matrix.diagonal; ext j : 1; by_cases g:i∈j <;> simp [g])]
      exact cutM_idp _
    have hg : ‖takeF i*put i‖ ≤ 1 := by
      let A := takeF i*put i
      have ht : star A*A=A := by rw [show star A=A from he.isSelfAdjoint,show A*A=A from he.isIdempotentElem]
      have hf : ‖A‖= ‖A‖*‖A‖ := (congrArg norm ht.symm).trans (CStarRing.norm_star_mul_self); change ‖A‖≤1; nlinarith
    have hf : ‖takeF i*put i‖=‖put i‖*‖put i‖ := CStarRing.norm_star_mul_self -- tune
    rw [hf] at hg; nlinarith
  induction S using induction_on_min with
  | empty=> simp [poke,Poly.tag_void]
  | insert i S p ih=> unfold poke; rw [Poly.tag_min _ _ _ p]; exact (norm_mul_le ..).trans ((mul_le_mul (ht _) ih (norm_nonneg _) zero_le_one).trans (by rw [one_mul]))
lemma crumb_scale (A : FC n) (S : Finset n) (c : ℂ) : crumb (c • A) S=c*crumb A S := rfl
lemma crumb_scaleR (A : FC n) (S : Finset n) (c : ℝ) : crumb (c • A) S=c • crumb A S := rfl
lemma crumb_add (A B : FC n) (S : Finset n) : crumb (A+B) S=crumb A S+crumb B S := rfl
lemma crumb_sum (S : Finset n) {I : Type*} (p : Finset I) (F : I→FC n) : crumb (∑ i∈p,F i) S=∑ i∈p,crumb (F i) S := by rw [crumb,Matrix.sum_apply]; rfl
end YM.CF.Pastry
