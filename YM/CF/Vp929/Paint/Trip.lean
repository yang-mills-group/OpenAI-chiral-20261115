import YM.CF.Vp929.Paint.Line
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
local notation "ℙ" => Fin 4
def CD(f:Bill): Bill
 | []=>0
 | a::x=> D f (a::x) - if x.getLast?=some a then 2*f x else 0

def circle : ℕ→ Bill
 | 0=> chain 2
 | k+1 => CD (circle k)
local notation "C"=>circle
lemma pair_pay(a b:ℙ): C 0 [a,b]=if a=b then 0 else 2:=by change D (D (chain 0)) [a,b]=_; by_cases h:a=b <;> simp [D_cons,h,eq_comm]
lemma circShift (a:ℙ)(x:Word)(k:ℕ)(p:x.length=k+1): C k (a::x)=C k (x++[a]):=by
 induction k generalizing x a with
 | zero=> obtain ⟨b,rfl⟩:=List.length_eq_one_iff.mp p; change C 0 [a,b]=C 0 [b,a]; simp [pair_pay,eq_comm]
 | succ k ih=>
   cases x with
   | nil=> simp at p
   | cons b x=>
    unfold circle; change D (C k) _ - (if (b::x).getLast?=some a then 2*C k (b::x) else 0)= D (C k) ((b::x)++[a]) - if (x++[a]).getLast?=some b then 2 * C k (x++[a]) else 0
    rw [D_append,D_ext (fun z=>C k (z++[a])) (fun z=>C k (a::z)) (b::x) (fun z h=> (ih a z (by omega)).symm),D_cons (C k),D_cons (fun z=> C k (b::x++z))]; simp; by_cases h:a=b; · subst b; rw [ih a x (by simpa using p)]; ring
    simp only [h,Ne.symm h,↓reduceIte,sub_zero]; ring
lemma circShift' (i j:Word)(k:ℕ)(p:i.length+j.length=k+2): C k (i++j)= C k (j++i):=by
 induction i generalizing j with
 | nil=> simp
 | cons a i ih=> rw [List.cons_append,circShift a _ k (by simp at *; omega),List.append_assoc,ih (j++[a]) (by simp at *; omega)]; simp
lemma circ_zero (x:Word)(k:ℕ)(p:x.length=k+2)(h:¬ Diverse x): C k x=0:=by
 induction k generalizing x with
 | zero=> exact chain_zero 2 p h
 | succ k ih=>
    unfold Diverse at h; push Not at h; obtain ⟨i,j,a,rfl⟩:=h; rw [circShift' _ _ _ (by simpa using p)]; let y:=j++i; have v:y.length=k+1:=by simp at *; unfold y; simp; omega
    change D (C k) ([]++ a::a::y) - (if (a::y).getLast?=some a then 2*C k (a::y) else 0)=0; rw [D_eq_zero]; rotate_left
    · intro t w b e; apply ih _ ?_ (fun g=>g t w b rfl); simp at *; omega
    split_ifs with P; swap; · simp
    have hy:y≠[]:= List.length_pos_iff.mp (by omega); have p:y.getLast?=some a:=by simpa [List.getLast?_cons_of_ne_nil,hy] using P
    obtain ⟨x,X⟩:=List.getLast?_eq_some_iff.mp p; have h:x.length=k:=by simpa [X] using v
    rw [show a::y=(a::x)++ [a] by rw [X]; rfl, circShift' (a::x) [a] k (by simp [h]), ih ([a]++a::x) (by simp [h]) (fun g=>g [] x a rfl)]; ring
lemma circ_pos (x:Word)(k:ℕ)(p:x.length=k+2):0 ≤ C k x:=by
 induction k generalizing x with
 | zero=> exact chain_pos _ p
 | succ k ih=>
    cases x with
    | nil=> simp at p
    | cons a x=>
      by_cases P:x.getLast?=some a
      · obtain ⟨z,rfl⟩:= List.getLast?_eq_some_iff.mp P; rw [←List.cons_append, circShift' _ [a] _ (by simp at *; omega),circ_zero ([a]++a::z) _ (by simp at *; omega) (fun g=>g [] z a rfl)]
      by_cases Q:Diverse (a::x); swap; · rw [circ_zero _ _ p Q]
      rw [circle, CD, if_neg P,sub_zero]; exact D_nonneg _ _ Q (fun z u=>ih _ (by omega))
lemma circ_pay(k:ℕ)(x:Word)(p:x.length=k+1): ∑a:ℙ,C k (a::x)=6*chain (k+1) x:=by
 induction k generalizing x with
 | zero=> obtain ⟨b,rfl⟩:=List.length_eq_one_iff.mp p; rw [chainD]; simp only [pair_pay,D_cons];
          fin_cases b <;> norm_num [Fin.sum_univ_succ] <;> decide
 | succ k ih=>
    have h:= D_ext (fun z=>∑a:ℙ,C k (a::z)) (fun z=>6*chain (k+1) z) x (fun z v=> ih _ (by omega)); simp_rw [circle, CD, D_cons (C k)]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]; rw [lost,lost, ← D_sum (fun a:ℙ => fun z=> C k (a::z)), h,D_const,chainD (k+1)]; have u:x≠[]:= by simp only [← List.length_pos_iff,p]; omega
    simp [loss,u]; ring
end YM.CF.VolumeCape.Paint
