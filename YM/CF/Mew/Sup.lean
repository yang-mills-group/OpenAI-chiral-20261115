import YM.CF.Mew.Stream
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter MeasureTheory Finset
variable {I J :Type*}[Fintype I]
lemma high_sum(S:I→Type*)(h:∀ i,Nonempty (S i))(W: I→ℝ)(w:∀ i,0 ≤ W i)(F:∀ i,S i→ℝ)(p:I→ℝ) (l:∀ i,p i=sSup (Set.range (F i))) (b:∀ i,BddAbove (Set.range (F i))):∀ (s: Finset I){c:ℝ},(∀ f:(i:I)→ S i,∑ i∈s,W i*F i (f i)≤c) →∑ i∈s,W i*p i ≤c:=by
 classical
 intro s; induction s using Finset.induction_on with
 | empty=> intro i hp; exact hp (fun i=>Classical.choice (h i)) -- infer
 | insert i s e ih=>
    intro c t; let T:=∑ j∈s,W j*p j
    have hx (X:S i):T ≤ c-W i*F i X:=by
       refine ih fun f=>?_ ; have he:=t (update f i X); rw [sum_insert e,update_self] at he; rw [le_sub_iff_add_le']; refine le_trans (le_of_eq (congrArg (_+·) (sum_congr rfl (fun j hj=>?_)))) he; rw [update_of_ne]; exact fun q=>e (q ▸ hj)
    rw [sum_insert e]
    by_cases l':W i=0; · rw [l', zero_mul,zero_add]; exact (hx (Classical.choice (h i))).trans (by simp [l'])
    have ht:= (w i).lt_of_ne (Ne.symm l'); have hp:p i≤ (c-T)/ W i:=by
       rw [l]; apply csSup_le ⟨_,Set.mem_range_self (Classical.choice (h i))⟩; rintro r ⟨z,hz⟩; subst r; apply (le_div_iff₀ ht).mpr; linarith only [hx z]
    linarith only [(le_div_iff₀ ht).mp hp]
-- leverage while not demanding component monotone 
lemma pulse_max(S:I→Type*)(h:∀ i,Nonempty (S i))(W: I→J→ℝ)(w:∀ i j,0 ≤ W i j)(u:∀ i, ∃ j,0<W i j)(F:∀ i,S i→ℝ)(l:∀ i j,0 ≤ F i j)(p:J→ℝ)(t:∀ j (f:(i:I)→ S i),∑ i, W i j*F i (f i) ≤ p j) :∃ P:I→ℝ, 0≤ P ∧ (∀ i j,F i j ≤ P i) ∧ ∀ j,∑ i,W i j* P i ≤ p j:=by
 classical
 let U(i):S i:=Classical.choice (h i); let Z(i):=sSup (Set.range (F i))
 have hb(i):BddAbove (Set.range (F i)):=by
    obtain ⟨j,hj⟩:=u i; refine ⟨(p j)/W i j,?_⟩; rintro x ⟨y,rfl⟩; obtain ⟨f,rfl'⟩:∃ f:(i:I)→ S i,y=f i:=⟨update U i y,(update_self ..).symm⟩; rw [rfl']; apply (le_div_iff₀ hj).mpr; rw [mul_comm]; exact (Finset.single_le_sum (fun k _=>mul_nonneg (w k j) (l k (f k))) (mem_univ i)).trans (t j f)
 have he(i j): F i j ≤ Z i:=le_csSup (hb i) (Set.mem_range_self _)
 exact ⟨Z,fun i=>(l i (U i)).trans (he i (U i)),he,fun j=>high_sum S h _ (fun i=>w i j) F _ (fun i=>rfl) hb _ (t j)⟩
end YM.CF.Mew
