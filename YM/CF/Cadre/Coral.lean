import YM.CF.Cadre.Lope
import Mathlib.Analysis.SpecialFunctions.Log.Summable
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
abbrev blaze(X:ΣA): Finset ΣA:=univ.filter fun S:ΣA=>¬ Disjoint X.val S.val
abbrev spark(o:A): Finset ΣA:=univ.filter fun X:ΣA=>o∈ X.val
variable (p:Palot.leaf A→ℝ)(g:∀ X:Palot.leaf A,0 ≤ p X)
include g
lemma beam(b:ℝ)(h:∀ i∈ Y.val, ∑ X∈ spark i,p X ≤ b):∑ X∈ blaze Y,p X ≤ Y.val.card*b:=by
 have hp(s:ΣA)(v:s∈ blaze Y):p s ≤ ∑ i∈ Y.val, if i∈ s.val then p s else 0:=by
    obtain ⟨i,t,a⟩:=Finset.not_disjoint_iff.mp ((mem_filter.mp v).2); nth_rw 1 [← (show (if i∈s.val then p s else 0)=_ from if_pos a)]; exact single_le_sum (fun j _=>ite_nonneg (g _) le_rfl) t
 apply (sum_le_sum hp).trans; rw [sum_comm,show (Y.val.card:ℝ)*b= ∑ _∈Y.val,b from (by simp)]
 refine sum_le_sum fun i v=> le_trans ?_ (h i v); rw [←sum_filter]; exact sum_le_sum_of_subset_of_nonneg (by intro j t; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp t).2⟩) (fun i _ _=>g i) -- tune
lemma hymn_v(b:ℝ)(h:∀ i∈ Y.val,∑ X∈spark i,p X ≤ b): (∑ G∈ (blaze Y).powerset,∏ j∈G,p j) ≤ Real.exp (Y.val.card*b):=by rw [←prod_one_add]; exact (Real.prod_one_add_le_exp_sum _ g).trans (Real.exp_le_exp.mpr (beam Y p g b h))
lemma supportV (X:ΣA)(k: Finset ΣG)(v:∀ T∈k,X∈T)(h:∀ T∈k,T⊆blaze Y) : (∑ G∈k,∏ i∈G,p i)≤ p X*∑ G∈ (blaze Y).powerset, ∏ i∈G,p i:=by
 let f(T:ΣG):=T.erase X; let V:= k.image f; rw [mul_sum]; refine Eq.trans_le ?_ (sum_le_sum_of_subset_of_nonneg (show V ⊆ _ from ?_) (fun i _ _=> mul_nonneg (g _) (prod_nonneg fun i _=>g i))) -- tune order
 · rw [sum_image]; apply sum_congr rfl; intro i hk; have ht:=v i hk; nth_rw 1 [←insert_erase ht]; rw [prod_insert (notMem_erase _ _)]
   intro i u j t p'; rw [←insert_erase (v i u), ←insert_erase (v j t)]; exact congrArg (insert X) p'
 intro G p; obtain ⟨H,l,rfl⟩:=mem_image.mp p; exact mem_powerset.mpr ((erase_subset ..).trans (h H l)) -- tune
lemma cop (q:Finset ΣA)(b:ℝ)(h:∀ i∈ Y.val,∑ X∈spark i,p X ≤ b)(k: Finset ΣG)(hx:∀ F∈k,F⊆ blaze Y)(hk:∀ F∈k,∃ a∈q,a∈F): (∑ G∈k,∏ i∈G,p i) ≤ (∑ i∈q,p i)*Real.exp (Y.val.card*b):=by
 let H(G:ΣG)(i:ΣA):= if i∈G then ∏ j∈G,p j else 0; have he(T:ΣG)(u:T∈k): (∏ i∈T,p i) ≤∑ i∈q,H T i:=by obtain ⟨i,h,v⟩:=hk T u; refine Eq.trans_le (show H T i=_ from if_pos v).symm (single_le_sum (fun j v=>?_ ) h); unfold H; split; exact prod_nonneg (fun j _=>g j); exact le_rfl
 refine (sum_le_sum he).trans ?_; rw [sum_comm,sum_mul]; apply sum_le_sum; intro i _; unfold H; rw [←sum_filter]; exact (supportV Y p g _ _ (fun T t=> (mem_filter.mp t).2) (fun T t=>hx T (filter_subset _ _ t))).trans (mul_le_mul_of_nonneg_left (hymn_v Y p g b h) (g _))
end YM.CF.Cadre
