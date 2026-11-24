import YM.CF.Vp929.Paint.Deriv
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
local notation "ℙ" => Fin 4
def chain (k:ℕ): Bill := Nat.rec (fun _ : Word => 1) (fun _ f=> D f) k
@[simp] lemma chain_nil(x): chain 0 x=1:= rfl
lemma chainD(n):chain (n+1)=D (chain n):=rfl
lemma chain_zero {x:Word}(n:ℕ) (v:x.length=n)(h:¬ Diverse x): chain n x=0:=by
 induction n generalizing x with
 | zero=>
   apply False.elim (h fun i j a p=>?_); simp [p] at v
 | succ n ih=>
   unfold Diverse at h; push_neg at h; obtain ⟨i,j,a,rfl⟩:=h; rw [chainD,D_eq_zero]; intro I J b H; apply ih ; simp at *; omega
   exact fun u=>u I J b rfl
lemma chain_pos {x:Word}(n:ℕ)(v:x.length=n):0 ≤ chain n x:=by
 induction n generalizing x with
 | zero=> simp
 | succ n ih=>
   by_cases p:Diverse x; exact D_nonneg _ x p (fun i h=> ih (by omega))
   rw [chain_zero _ v p]
abbrev Splits(m n:ℕ)(c:ℤ):Prop:=∀ x y : Word,x.length=m→y.length=n → ∑ a:ℙ,chain (m+n+1) (x++a::y) = c * chain m x * chain n y
def loss(p:Option ℙ):ℤ:= if p=none then 0 else 2
lemma lost(p:Option ℙ)(v:ℤ):∑a:ℙ,(if p=some a then 2*v else 0)= loss p * v:=by cases p <;> simp [loss]
lemma gap(m n:ℕ)(x y:Word): ∑a:ℙ,chain (m+n+1) (x++a::y) = D (fun z=>∑a:ℙ,chain (m+n) (z++a::y)) x + D (fun z=>∑a:ℙ,chain (m+n) (x++a::z)) y + (4-loss x.getLast?-loss y.head?) * chain (m+n) (x++y) :=by
 rw [chainD]; simp_rw [D_append, D_cons,Finset.sum_sub_distrib,Finset.sum_add_distrib]; simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]; rw [D_sum,D_sum,lost,lost]; simp; ring
lemma charge(m n:ℕ):∃ c:ℤ,0<c ∧ Splits m n c:=by
 have h{k}(ih:∀ m n :ℕ, m+n < k → ∃ c:ℤ,0<c∧Splits m n c) (m n:ℕ)(hm:m+n=k): ∃ c:ℤ,0<c∧Splits m n c :=by
  have J{m n c} (p:Splits m n c)(x:Word)(hx:x.length=m+1)(y:Word)(v:y.length=n): D (fun z=>∑a:ℙ, chain (m+1+n) (z++a::y)) x = c*chain (m+1) x*chain n y:=by
     rw [D_ext _ (fun z=> (c*chain n y)*chain m z) x (fun z u=>by rw [show m+1+n=m+n+1 by omega,p z y (by omega) v]; ring),D_const,chainD]; ring
  have P{m n c}(p:Splits m n c)(x:Word)(hx:x.length=m)(y:Word)(v:y.length=n+1):D (fun z=>∑a:ℙ,chain (m+(n+1)) (x++a::z)) y =c*chain m x * chain (n+1) y:=by
     rw [D_ext _ (fun z=> c*chain m x*chain n z) y (fun z u=>by rw [show m+(n+1)=m+n+1 by omega,p x z hx (by omega)]),D_const,chainD]
  have w{x:Word}(p:0<x.length): loss x.getLast?=2 ∧ loss x.head?=2:= ⟨by simp [loss,List.length_pos_iff.mp p],by simp [loss,List.length_pos_iff.mp p]⟩
  match m,n with
  |0,0=> refine ⟨4,by norm_num,fun x y h k=>?_⟩; rw [gap 0 0 x y]; simp at h k; subst x y; simp [loss]
  |m+1,0=>
      obtain ⟨c,p,g⟩:= ih m 0 (by omega); refine ⟨c+2,by omega,fun x y V W=>?_⟩; rw [gap,J g x V y W,(w (V ▸ by omega)).1]; simp_all [loss]; ring
  |0,n+1 => obtain ⟨c,p,g⟩:= ih 0 n (by omega); refine ⟨c+2,by omega,fun x y V W=>?_⟩; rw [gap,P g x V y W,(w (W ▸ by omega)).2]; simp_all [loss]; ring
  |m+1,n+1=>
     obtain ⟨a,p,z⟩:=ih m (n+1) (by omega); obtain ⟨b,q,w'⟩:= ih (m+1) n (by omega); refine ⟨a+b,by omega,fun x y V W=>?_⟩; rw [gap,J z x V y W,P w' x V y W,(w (by omega : 0<x.length)).1,(w (by omega : 0<y.length)).2]; ring
 suffices ∀ k m n : ℕ,m+n=k → ∃ c:ℤ,0<c∧Splits m n c from this _ m n rfl
 intro k; induction k using Nat.strong_induction_on with | h k ih=> exact h (fun m n H=> ih (m+n) H _ _ rfl)
end YM.CF.VolumeCape.Paint
