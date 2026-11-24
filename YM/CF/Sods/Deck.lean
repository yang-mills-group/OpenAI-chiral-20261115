import YM.CF.Sods.Mars
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E F:Type*}[Fintype E][DecidableEq E][DecidableEq F]{f:E→F}{A B:Op E}{k a m w:ℝ}
-- eigen tolerance separation
lemma turn(C:Finset ℝ)(k:ℝ)(h:0 ≤ k): ∃ F:ℝ→ℝ,(∀ i∈C, |i-F i|≤ C.card*k) ∧ ∀ i∈C,∀ j∈C,F i≠F j→k ≤|i-j|:=by
 induction C using Finset.strongInductionOn
 rename_i C ih
 rcases C.eq_empty_or_nonempty with u|u; · subst C; simp
 let z:= C.min' u; let W:= C.erase z; have hp:z∈C:=min'_mem _ _; obtain ⟨g,H,T⟩:= ih W (erase_ssubset hp); have ht:(W.card:ℝ)+1=C.card:=by exact_mod_cast card_erase_add_one hp
 rcases W.eq_empty_or_nonempty with e|e
 · have hx:C={z}:=by rw [← insert_erase hp, (show C.erase z= _ from e)]; rfl
   refine ⟨id,?_,?_⟩ <;> simp [hx,h]
 let y:= W.min' e; have hy:y∈W:=min'_mem _ _; have hv(t)(h:t∈W):z<t:=lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase h)) (Ne.symm (ne_of_mem_erase h)); have he:= hv _ hy
 let q:=if k ≤ y-z then z else g y
 let F(t:ℝ):= if t=z then q else g t
 have hh (i) (p:i∈W): F i=g i:=if_neg (hv i p).ne'
 have hg(i)(l:i∈W)(p:F z≠F i): k ≤ |z-i|:=by
   have hk : z-i ≤0:=(by linarith [hv i l]); rw [abs_of_nonpos hk]; have hr:= min'_le _ _ l; change y ≤ i at hr; by_cases ht:k ≤ y-z; · linarith
   have hz:g y ≠ g i:=by intro h; apply p; rw [hh i l,show F z=q from if_pos rfl,show q=g y from if_neg ht,h]
   have hv:=T y hy i l hz; rw [abs_of_nonpos (show y-i≤0 by linarith)] at hv; linarith
 refine ⟨F,fun i l=>?_,fun i t j r q=>?_⟩
 · by_cases p:i=z; swap; · have hv:i∈W:=mem_erase.mpr ⟨p,l⟩; rw [hh i hv]; exact (H i hv).trans (mul_le_mul_of_nonneg_right (by linarith) h)
   subst i; rw [show F z=q from if_pos rfl]; unfold q; split_ifs with p; · simp; positivity
   push Not at p; have hj:= abs_le.mp (H y hy); rw [abs_le]; constructor <;> nlinarith
 rcases eq_or_ne i z with g|g
 · subst i; exact hg j (mem_erase.mpr ⟨(fun w=>q (w.symm ▸ rfl)),r⟩) q
 rcases eq_or_ne j z with v|v
 · subst j; rw [abs_sub_comm]; exact hg i (mem_erase.mpr ⟨g,t⟩) (Ne.symm q)
 have ht:i∈W:=mem_erase.mpr ⟨g,t⟩; have hl:j∈W:=mem_erase.mpr ⟨v,r⟩; apply T _ ht _ hl; rwa [←hh i ht,←hh j hl]

def crew(f:E→F)(A:Op E):Op E := Matrix.of fun i j=>if f i=f j then A i j else 0
lemma crew_at(f:E→F)(A:Op E)(i j:E):crew f A i j= if f i=f j then A i j else 0:=rfl
lemma crew_f(f:E→F)(A:Op E):Bl f (crew f A):=fun i j h=> by rw [crew_at,if_neg h]
lemma crew_s(f:E→F)(A:Op E):crew f (star A)=star (crew f A):=by ext i j; by_cases e:f i=f j <;> simp [crew_at,e,Ne.symm]
lemma crown {F':Type*}[DecidableEq F']{d e:E→ℝ}(h:Bl f A)(p:Switch A (Matrix.diagonal (fun i=>(d i:ℂ))) m)(q:0<a)(he:∀ i j,e i ≠ e j → a ≤|d i-d j|)(l:E→F')(hl:∀ i j, l i=l j ↔ f i=f j ∧ e i=e j): ‖A-crew l A‖ ≤ Fintype.card E*(m/a):=by
 have hp:0≤m:=(norm_nonneg _).trans p
 apply Branch.schur (fun _ _=>m/a) _ _ (by positivity)
 · intro i j; rw [Matrix.sub_apply,crew_at]; split; · rw [sub_self,norm_zero]; positivity
   rename_i hQ; rw [sub_zero]; by_cases H:f i=f j; swap; · rw [h _ _ H,norm_zero]; positivity
   have hz:=he i j (fun e=> hQ ((hl i j).mpr ⟨H,e⟩)); have hx:= (norm_entry (A* (Matrix.diagonal (fun i=>(d i:ℂ)))-Matrix.diagonal (fun i=>(d i:ℂ))*A) i j).trans p; rw [Matrix.sub_apply,Matrix.mul_diagonal, Matrix.diagonal_mul,mul_comm ((d i:ℂ)), ←mul_sub,norm_mul, ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs, abs_sub_comm] at hx; exact (le_div_iff₀ q).mpr (le_trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) hx)
 · intro i; simp
 intro i; simp
end YM.CF.Sods
