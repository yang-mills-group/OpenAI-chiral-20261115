import YM.Next.STATIONARY.Lift.ManyLegs
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators Classical
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A B : ℝ}{M N R:ℕ}
-- finite list certificate
structure Pond (M:ℕ)(A:ℝ)(f:Phase α→ℂ):Prop where
 there: ∃ (S:Finset (Shift α))(v:Shift α→ℂ), (∀ i∈S,Laurent.size i ≤ M) ∧ (∑ i∈S,‖v i‖) ≤ A ∧ ∀ p,f p=∑ i∈S, Laurent.mode p i * v i
variable {f g:Phase α→ℂ}
lemma Pond.mono (h:Pond M A f)(hp:A≤ B)(he:M ≤ N):Pond N B f:=⟨by obtain ⟨S,v,hs,ht,h⟩:=h.there; exact ⟨S,v,fun i hi=> (hs i hi).trans he,ht.trans hp,h⟩⟩
lemma Pond.analytic (hp:Pond M A f): Firm 1 (Real.exp M*A) f:=by
 obtain ⟨S,v,hs,ht,h⟩:=hp.there; rw [funext h]; apply (Firm.sum (σ:=1) S _ (fun i=>Real.exp M * ‖v i‖) zero_lt_one (fun i hi=>?_)).mono zero_lt_one le_rfl
 · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
 exact (((Firm.mode i (σ:=1) zero_lt_one).mul (Firm.const zero_lt_one (v i))).mono zero_lt_one le_rfl (by rw [one_mul]; gcongr; exact hs i hi))
lemma Pond.zeros : Pond M 0 (α:=α) 0:= ⟨∅,0,by simp,by simp,by simp⟩
lemma Pond.modes (A:ℂ)(x:Shift α) : Pond (size x) ‖A‖ (fun p=>mode p x*A):=⟨{x},fun _=>A,by simp,by simp,by simp⟩
private def widen (S:Finset (Shift α))(f:Shift α→ℂ)(i:Shift α):= if i∈S then f i else 0
open Finset
private lemma wider {S U:Finset (Shift α)}(h:S⊆U)(v:Shift α→ℂ): (∑ i∈S, ‖v i‖)=(∑ i∈U, ‖widen S v i‖) ∧ ∀ p:Phase α, (∑ i∈S, mode p i*v i)= ∑ i∈U, mode p i*widen S v i:=by
 constructor
 · rw [← sum_subset h (show ∀ j∈U,j∉S→ ‖widen S v j‖=0 from fun j hj he=>by simp [widen,he])]; exact sum_congr rfl fun i hi=>by rw [widen,if_pos hi]
 intro p; rw [← sum_subset h (show ∀ j∈U,j∉S→ mode p j*widen S v j=0 from fun j hj he=>by simp [widen,he])]; exact sum_congr rfl fun i hi=>by rw [widen,if_pos hi]
lemma Pond.add(h:Pond M A f)(he:Pond M B g):Pond M (A+B) (f+g):=by
 obtain ⟨X,u,hx,hX,h1⟩:= h.there; obtain ⟨Y,v,hy,hY,h2⟩:= he.there
 let a:=widen X u; let b:=widen Y v; let z:=X∪Y
 obtain ⟨H1,T⟩:=wider (show X⊆z from subset_union_left) u; obtain ⟨H2,P⟩:=wider (show Y⊆z from subset_union_right) v
 refine ⟨z,a+b, fun i hi=> (mem_union.mp hi).elim (hx i) (hy i), (sum_le_sum (g:=fun i=> ‖a i‖+‖b i‖) (fun i _=> norm_add_le ..)).trans ?_,?_⟩
 · unfold a b; rw [sum_add_distrib,←H1,←H2]; exact add_le_add hX hY
 intro p; simp_rw [Pi.add_apply,h1,h2,T,P,mul_add,sum_add_distrib]; rfl
lemma Pond.scal (A':ℂ)(h:Pond M A f):Pond M (‖A'‖*A) (A' • f):= by
 obtain ⟨S,v,hs,hv,h⟩:=h.there; refine ⟨S,A' • v,hs,?_,?_⟩
 · simp_rw [Pi.smul_apply,norm_smul, ← mul_sum]; exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
 intro p; simp_rw [Pi.smul_apply,h,smul_eq_mul,mul_sum]; exact sum_congr rfl fun i _=>mul_left_comm ..
lemma Pond.neg(h:Pond M A f):Pond M A (-f):= by simpa using h.scal (-1)
lemma Pond.rest(h:Pond M A f)(hp:Pond M B g):Pond M (A+B) (f-g):=by simpa only [sub_eq_add_neg] using h.add hp.neg
lemma funds {ι:Type} (X:Finset ι)(f:ι→Phase α→ℂ)(g:ι→ℝ)(h:∀ i∈X,Pond M (g i) (f i)): Pond M (∑ i∈X,g i) (∑ i∈X,f i):=by induction X using Finset.induction_on with
 | empty=>simpa using Pond.zeros (α:=α) (M:=M)
 | insert j X hp ih=>rw [sum_insert hp,sum_insert hp]; exact (h j (by simp)).add (ih (fun i hi=> h i (by simp [hi])))
lemma fundsF {ι:Type} (X:Finset ι)(f:ι→Phase α→ℂ)(g:ι→ℝ)(h:∀ i∈X,Pond M (g i) (f i)): Pond M (∑ i∈X,g i) (fun y=>∑ i∈X,f i y):=by rw [show (fun y=> _) =∑ i∈X,f i from funext fun i=> (Finset.sum_apply ..).symm]; exact funds X f g h
lemma Pond.travel {β:Type}[Fintype β][DecidableEq β](u : Phase β → Phase α)(hf:Pond M A f)(he:∀ i,Laurent.size i ≤ M→ Pond N 1 (fun v=>Laurent.mode (u v) i)) : Pond N A (f∘u):=by
 obtain ⟨S,v,hx,hp,h⟩:=hf.there; rw [show f ∘ u=(fun p=>∑ i∈S,Laurent.mode (u p) i*v i) from funext fun p=> h (u p)]
 apply (fundsF S _ (fun i=> ‖v i‖) (fun i hi=>?_)).mono hp le_rfl
 simp_rw [mul_comm _ (v i)]; exact ((he i (hx i hi)).scal (v i)).mono (mul_one _).le le_rfl
lemma Pond.mul (h:Pond M A f)(hp:Pond N B g)(he:0≤ B):Pond (M+N) (A*B) (f*g):=by
 obtain ⟨X,u,hx,hX,h1⟩:=h.there; obtain ⟨Y,v,hy,hY,h2⟩:=hp.there
 let V(i j)(p:Phase α):=mode p (i+j)*(u i*v j)
 rw [show f*g=(fun p=> ∑ i∈X,∑ j∈Y,V i j p) from ?_]
 · apply (fundsF X _ (fun i=> ‖u i‖*B) (fun i hi=>?_)).mono _ le_rfl
   · rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hX he
   apply (fundsF Y _ (fun j=> ‖u i*v j‖) (fun j hj=> ((Pond.modes _ _).mono le_rfl ((size_add ..).trans (Nat.add_le_add (hx i hi) (hy j hj)))))).mono _ le_rfl; simp_rw [norm_mul, ← mul_sum]; exact mul_le_mul_of_nonneg_left hY (norm_nonneg _)
 ext1 p; rw [Pi.mul_apply,h1,h2,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; unfold V; rw [mode_shift]; ring
-- functions wall
abbrev Board (M:ℕ)(A:ℝ)(f:SheetLeg α ξ N):Prop:=∀ i x,Pond M A (fun p=>f p i x)
end YM.CF.Braid
