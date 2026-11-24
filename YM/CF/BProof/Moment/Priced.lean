import YM.Push.ABSOLUTE_SUMS.Basic

/-! Real support-price. Always absolute summability. `Moment.Toll` lumps countable
rows if needed including footprint tie. Terms may be different addresses with identical
supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Moment
open Function Filter Set RG Push.AbsoluteSums Finset MeasureTheory
open scoped Topology BigOperators Classical
variable {A B D E I K : Type*}

def hit (S:A→Finset B)(v:A→ℝ)(r:ℝ)(o:B)(i:A):= if o∈ S i then Real.exp (r*(S i).card)*v i else 0
structure Toll (S:A→Finset B)(v:A→ℝ)(r C : ℝ) : Prop where
 nonneg (i:A): 0≤v i
 pays (x:B) : SumBudget (hit S v r x) C

variable (S:A→Finset B)(v:A→ℝ){r C r' C':ℝ}
lemma Toll.weaken (h:Toll S v r C)(l:r'≤r)(p:C≤C') : Toll S v r' C':= ⟨h.nonneg,fun x=> budget_loosen (budget_mono (h.pays x) (fun i=> by unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (h.nonneg i); exact le_rfl) (fun i=> by unfold hit; split; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr)) (h.nonneg i); exact le_rfl)) p⟩
lemma Toll.shrink (h:Toll S v r C)(v':A→ℝ)(hp:∀ i,0≤v' i)(he:∀ i,v' i≤v i) : Toll S v' r C:= ⟨hp,fun x=>budget_mono (h.pays x) (fun i=> by unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (hp i); exact le_rfl) (fun i=> by unfold hit; split; exact mul_le_mul_of_nonneg_left (he i) (Real.exp_pos _).le; exact le_rfl)⟩
lemma Toll.scale (h:Toll S v r C)(p:ℝ)(hp:0≤p) : Toll S (fun i=>p*v i) r (p*C):= by
 refine ⟨fun i=>mul_nonneg hp (h.nonneg i),fun x=>?_⟩; convert budget_scale hp (h.pays x) using 1; ext i; unfold hit; split; ring; rw [mul_zero]
lemma Toll.total [Fintype B] (h:Toll S v r C)(hr:0≤r)(hp:∀ i,(S i).Nonempty): SumBudget v ((Fintype.card B:ℝ)*C):=by
 simpa only [sum_const,card_univ,nsmul_eq_mul] using budget_mono (budget_over Finset.univ (hit S v r) (fun _=>C) (fun b _=>h.pays b)) h.nonneg (fun i=> by obtain ⟨x,hx⟩:=hp i; refine le_trans (b:= hit S v r x i) ?_ (single_le_sum (f:=fun x=>hit S v r x i) (fun x _=> (h.pays x).1 i) (mem_univ x)); unfold hit; rw [if_pos hx]; exact le_mul_of_one_le_left (h.nonneg _) (Real.one_le_exp (by positivity)))

lemma Toll.sum {A':Type*}(u:Toll S v r C)(S':A'→Finset B)(v':A'→ℝ)(w:Toll S' v' r C') : Toll (Sum.elim S S') (Sum.elim v v') r (C+C'):=by
 refine ⟨fun i=> by cases i; exact u.nonneg _; exact w.nonneg _,fun i=>?_⟩
 refine ⟨fun j=> by cases j; exact (u.pays i).1 _; exact (w.pays i).1 _, ?_⟩
 let H:=HasSum.sum (f:=hit (Sum.elim S S') (Sum.elim v v') r i) ((u.pays i).2.1.hasSum) ((w.pays i).2.1.hasSum)
 exact ⟨H.summable,H.tsum_eq.trans_le (add_le_add (u.pays i).2.2 (w.pays i).2.2)⟩

/-- finite fiber product iteration. -/
lemma Toll.prod [Fintype I] (U:I→A→Finset B)(u:I→A→ℝ)(C:I→ℝ)(h:∀ i,Toll (U i) (u i) r (C i)): Toll (Function.uncurry U) (Function.uncurry u) r (∑ i,C i):=by
 refine ⟨fun i=> (h _).nonneg _,fun x=>?_⟩
 let Z:=hit (Function.uncurry U) (Function.uncurry u) r x
 have H(i:I×A): 0≤Z i:=((h _).pays x).1 (i.2)
 apply budget_of_sum H; intro s; change (∑ i∈ s,Z i)≤_
 have hh(i:I): (∑ j∈ s with j.1=i,Z j)≤ C i:= by
   let T:=s.filter (fun j=>j.1=i); change (∑ j∈ T,Z j)≤_
   have hi:Set.InjOn (Prod.snd : I×A→ A) (↑T):= by intro i hi j hj h; exact Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) h
   refine le_trans ?_ (budget_sum ((h i).pays x) (T.image Prod.snd)); rw [sum_image hi]; exact le_of_eq (sum_congr rfl fun j hj=> by rw [← (mem_filter.mp hj).2]; rfl)
 rw [← sum_fiberwise s Prod.fst]; exact sum_le_sum fun i _=>hh i
lemma Toll.pool (T:A→ D)(U:D→Finset B)(hp:S=U ∘ T) (h:Toll S v r C)(p:D→ℝ) (he: ∀ i:D, HasSum (fun j=> if T j=i then v j else 0) (p i)): Toll U p r C:=by
 have hp'(i:D):0≤p i:=hasSum_le (f:=fun _:A=>(0:ℝ)) (fun j=>by split; exact h.nonneg _; exact le_rfl) hasSum_zero (he i)
 refine ⟨hp',fun o=>?_⟩; apply budget_of_sum (fun i=> by unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (hp' i); exact le_rfl)
 intro s; let Z(i:D)(j:A):= if T j=i then hit S v r o j else 0; have hl(i:D) : HasSum (Z i) (hit U p r o i):= by
    unfold hit; split; next H=> apply HasSum.congr_fun ((he i).mul_left _); intro j; by_cases e:T j=i<;> simp [Z,e,hp,hit,H] -- tune
    next hh=>
     apply (show HasSum (fun _ : A => (0:ℝ)) 0 from hasSum_zero).congr_fun; intro j; by_cases e:T j=i<;>simp [Z,e,hp,hh,hit]
 apply le_trans _ (h.pays o).2.2; apply hasSum_le _ (hasSum_sum (s:=s) (fun i _=>hl i)) (h.pays o).2.1.hasSum -- tune direction order
 intro i; by_cases H:T i∈s
 · simp [Z,@eq_comm D (T i),H]
 rw [sum_eq_zero]; exact (h.pays o).1 _; intro j hj; exact if_neg (show ¬T i=j from fun e=> H (e ▸ hj))
end YM.CF.BProof.Moment
