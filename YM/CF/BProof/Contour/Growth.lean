import YM.CF.BProof.Contour.Parts
import YM.CF.BProof.Moment.Priced
import Mathlib.Algebra.BigOperators.Ring.Finset

/- B-rootK second estimate on finite addresses. Recursion over rooted
components (height via subset available), bounded by the rooted tree fees
at previous rate. Allows supports in any finite block space. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Filter Finset Moment Relation Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {B I: Type*}[Fintype B][DecidableEq B][Fintype I][DecidableEq I]
variable (S:I→Finset B)(u:I→ℝ)
def liftP (a:ℝ)(i:I):=Real.exp (a*(S i).card)*u i
def wage (V:Finset I):=∏ j∈V,u j
def rests(P:Finset I)(x:I):= P.powerset.filter fun s=> Spark S s∧ x∈s
def forest(P:Finset I)(T:Finset B):= P.powerset.filter fun s=> Spark S s∧ ∃ x∈s,meets S x T
lemma excises(P:Finset I)(i:I){V:Finset I}(h:V∈rests S P i): Parts S (V.erase i) ⊆ forest S (P.erase i) (S i):=by
 obtain ⟨h,t,p⟩:= mem_filter.mp h; intro x v; obtain ⟨e,f⟩:= lives S _ v; exact mem_filter.mpr ⟨mem_powerset.mpr (e.trans (erase_subset_erase i (mem_powerset.mp h))), f, packHits S (excise S t p) x v⟩
variable (p:∀ i,0≤u i)
lemma wage_eq(i:I)(V:Finset I)(g:i∈ V) : wage u V=u i* ∏ j∈ Parts S (V.erase i), wage u j:=by
 rw [wage,← mul_prod_erase _ u g]; change _ = u i * ∏ j∈ Parts S (V.erase i),∏ k∈ id j,u k; rw [←prod_biUnion (different S _),reconstruct S _]
include p
lemma wage_pos(V:Finset I): 0≤wage u V:= prod_nonneg fun i _=>p i
lemma root_recur(P:Finset I)(x:I) : ∑ j∈ rests S P x,wage u j ≤ u x* Real.exp (∑ j∈forest S (P.erase x) (S x),wage u j):=by
 let f(j:Finset I):= Parts S (j.erase x); let F:=forest S (P.erase x) (S x); let V:= rests S P x
 have he(j:Finset I)(h:j∈ V): insert x ((f j).biUnion id)=j:=by rw [show (f j).biUnion id=j.erase x from reconstruct ..,insert_erase (mem_filter.mp h).2.2]
 let W(v:Finset (Finset I)):=∏ j∈v,wage u j
 calc
    _ = u x * ∑ j∈ V.image f,W j:= by rw [mul_sum,sum_image (show Set.InjOn f V from fun i hi j hj v=>(he i hi).symm.trans ((congrArg (fun i:Finset (Finset I)=> insert x (i.biUnion id)) v).trans (he j hj)))]; exact sum_congr rfl fun i h=> wage_eq S u _ _ (mem_filter.mp h).2.2
    _ ≤ u x * ∑ j∈ F.powerset,W j:=mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (fun i (h:i∈V.image f) =>by obtain ⟨j,hg,rfl⟩:= mem_image.mp h; exact mem_powerset.mpr (excises S _ _ hg)) (fun i _ _=> prod_nonneg fun i _=> wage_pos u p i)) (p x)
    _ ≤ _ := by
       unfold W; apply mul_le_mul_of_nonneg_left _ (p x); rw [show F=forest S _ _ from rfl,←Finset.prod_one_add,Real.exp_sum]; exact prod_le_prod (fun i _=> by linarith [wage_pos u p i]) (fun i _=> (le_of_eq (add_comm ..)).trans (Real.add_one_le_exp _))
variable {u}
omit p
lemma window {α δ:ℝ}(h:Toll S u α δ)(F:Finset B)(V:Finset I) : ∑ j∈ V with meets S j F,liftP S u α j ≤ F.card*δ:=by
 calc
   _ ≤ ∑ j∈ V, ∑ x∈ F,hit S u α x j:= by
        rw [sum_filter]; apply sum_le_sum; intro j p; split; · rename_i t; obtain ⟨x,v,l⟩:= t; exact le_trans (le_of_eq (if_pos l).symm) (single_le_sum (f:=fun x=>hit S u α x j) (fun x _=> (h.pays x).1 j) v)
        exact sum_nonneg (fun x _=> (h.pays x).1 j)
           
   _ ≤ ∑ x∈ F,δ:= by rw [sum_comm]; exact sum_le_sum (fun x _=> budget_sum (h.pays x) V)
   _ = _:= by rw [sum_const,nsmul_eq_mul]; -- tune
include p
lemma wages {P:Finset I}{p':I→ℝ}(h:∀ i∈P,∑ j∈ rests S P i,wage u j ≤ p' i)(F:Finset B) : ∑ j∈forest S P F, wage u j ≤ ∑ j∈P with meets S j F,p' j:=by
 let V:= forest S P F; let T:= P.filter fun i=> meets S i F
 let f(v:Finset I)(x:I):= if x∈v then wage u v else 0
 have hf(v:Finset I)(x:I):0≤f v x:=by unfold f; split; exact wage_pos u p v; exact le_rfl
 apply le_trans (b:=∑ x∈T,∑ v∈ V,f v x)
 · rw [sum_comm]; apply sum_le_sum; intro j g; obtain ⟨e,k,i,h,v⟩:= mem_filter.mp g; exact le_trans (le_of_eq (if_pos h).symm) (single_le_sum (f:=f j) (fun i _=> hf j i) (mem_filter.mpr ⟨mem_powerset.mp e h,v⟩)) -- tune
 apply sum_le_sum; intro i t; obtain ⟨e,b⟩:= mem_filter.mp t; apply le_trans _ (h i e); unfold f; rw [← sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun j (g:j ∈ _) => (by obtain ⟨t,h⟩:= mem_filter.mp g; obtain ⟨e,h',-⟩:= mem_filter.mp t; exact mem_filter.mpr ⟨e,h',h⟩)) (fun i _ _=> wage_pos u p i)
omit p
lemma anchor {a α δ:ℝ}(h:Toll S u α δ)(g:a+δ ≤α)(P:Finset I)(x:I)(l:x∈ P) : ∑ j∈ rests S P x, wage (liftP S u a) j ≤ liftP S u α x:=by
 let v:=liftP S u a; have hp(i):0≤v i:=mul_nonneg (Real.exp_pos _).le (h.nonneg i)
 induction P using Finset.strongInduction generalizing x with
 | H P ih=>
   have hv:= (wages S hp (p':= liftP S u α) (P:=P.erase x) (fun i=> ih (P.erase x) (erase_ssubset l) i) (S x)).trans (window S h (S x) (P.erase x)); apply (root_recur S v hp P x).trans; apply (mul_le_mul_of_nonneg_left (Real.exp_monotone hv) (hp x)).trans; unfold v liftP; rw [mul_right_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (h.nonneg x); apply Real.exp_monotone; rw [mul_comm ((S x).card:ℝ), ← add_mul]; exact mul_le_mul_of_nonneg_right g (by positivity)
def payC (u:I→ℝ)(v:Finset I) := if Spark S v then wage u v else 0
lemma counts {a α δ:ℝ}(h:Toll S u α δ)(g:a+δ ≤α)(v:0≤a): Toll (fun i:Finset I=> i.biUnion S) (payC S u) a δ:=by
 have hu(j):0≤liftP S u a j:= mul_nonneg (Real.exp_pos _).le (h.nonneg j)
 have hp(q:Finset I):0≤payC S u q:=by unfold payC; split; exact wage_pos u h.nonneg q; exact le_rfl
 refine ⟨hp,fun x=>?_⟩
 refine budget_of_sum (fun i=> by unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (hp i); exact le_rfl) fun t=>?_
 let T:=forest S univ {x}
 calc
   _ ≤ ∑ j∈ t, if j ∈ T then wage (liftP S u a) j else 0:=by
        apply sum_le_sum; intro j _; have he:0≤wage (liftP S u a) j:=wage_pos _ hu _; have hf: 0 ≤ if j∈T then wage (liftP S u a) j else 0:=by split; exact he; exact le_rfl
        unfold hit; split; swap; · exact hf
        rename_i hh; unfold payC; split; swap; · rw [mul_zero]; exact hf
        rename_i hS; obtain ⟨i,hp,v⟩:=mem_biUnion.mp (show x∈ j.biUnion S from hh); rw [if_pos (show j∈ T from mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),hS,i,hp,x,mem_singleton_self _,v⟩)]; unfold wage liftP; rw [prod_mul_distrib,←Real.exp_sum]; apply mul_le_mul_of_nonneg_right _ (wage_pos u h.nonneg _); apply Real.exp_monotone; dsimp only; rw [←mul_sum,← Nat.cast_sum]; gcongr; exact card_biUnion_le
   _ ≤ ∑ j∈ T,wage (liftP S u a) j:=by rw [←sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun i (h:i∈_)=> (mem_filter.mp h).2) (fun _ _ _=> wage_pos _ hu _)
   _ ≤ ∑ j:I with meets S j {x},liftP S u α j:= wages S hu (fun i=>anchor S h g univ i) _
   _ ≤ δ:= by simpa only [card_singleton,Nat.cast_one,one_mul] using window S h {x} univ
end YM.CF.BProof.Contour
