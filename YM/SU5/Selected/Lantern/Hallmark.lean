import YM.SU5.Selected.Lantern.Tracery
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern.Stencil
open Function Finset
-- face variables t-choice across baryon clerks. mass may signed no approximation error here.
variable {T n:Type*} [Fintype T][Fintype n][DecidableEq n] {A:Type*}[CommRing A][Algebra ℂ A]
def tonality (w:T→ℂ) (F:T→A): A:= ∑ x, w x • F x
def pulseWeight (w:T→ℂ): (n→T)→ℂ := fun f=> ∏ i,w (f i)
def polar (w:T→ℂ) (F:n→T→A): n→A:= fun k=> tonality w (F k)
variable (w:T→ℂ)(X:n→T→A)
local notation "uv"=> pulseWeight (n:=n) w
lemma unit_cast {A:Type*}[CommRing A]{F:n→T→A} : ( ∑ s:n→T,∏ v:n,F v (s v) )= ∏ v:n, ∑ t:T, F v t := by rw [prod_univ_sum]; rfl
lemma unit_vote (p:∑ i,w i=1): ∑ s, uv s=1:=by unfold pulseWeight; rw [unit_cast (A:=ℂ)]; simp_rw [p,prod_const_one]
lemma unit_toll :∑ s, ‖uv s‖=(∑ i, ‖w i‖)^Fintype.card n:=by -- unit_cast requires Algebra ℂ for ℝ? omit
 unfold pulseWeight; simp_rw [norm_prod]; rw [unit_cast (F:=fun (_:n) (i:T)=> ‖w i‖),prod_const,card_univ]
private lemma weigh (f:n→A)(S:Finset n): (∏ t:n,(if t∈S then f t else 1))=∏ t∈S,f t:=by rw [← Finset.prod_filter]; simp
lemma unit_scores (p:∑ i,w i=1) (S:Finset n): ∑ f:n→T, uv f • ∏ i∈ S,X i (f i)=∏ i∈S,polar w X i:=by
 let F(t:n)(s):= if t∈ S then X t s else 1
 have he(f:n→T):uv f • (∏ i∈ S,X i (f i))=∏ i, (w (f i)) • F i (f i):=by rw [←weigh _ S]; unfold F pulseWeight; simp_rw [Algebra.smul_def]; rw [prod_mul_distrib,map_prod]
 simp_rw [he]; rw [unit_cast (F:=fun k i=> (w i) • F k i),←weigh (polar w X)]; refine prod_congr rfl (fun i _=>?_); by_cases g:i∈S; · unfold polar tonality F; simp [g]
 simp only [F, if_neg g,←Finset.sum_smul,p,one_smul]
lemma cue_m (p:∑ i,w i=1) (S:Finset n)(r:ℕ) : ballet r S (polar w X)=∑ f:n→T, uv f • ballet r S (fun i=> X i (f i)):=by
 unfold ballet; simp_rw [smul_sub,sum_sub_distrib]; rw [←Finset.sum_smul,unit_vote w p,one_smul]; congr 1; rw [show (∑ f:n→T, _) = ∑ i∈ range r, label S.card r i • ∑ v∈ S.powersetCard (load i), ∑ f:n→T, uv f • ∏ j∈ v,X j (f j) from ?_]
 · simp_rw [unit_scores w X p]
 simp_rw [smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]; simp_rw [smul_comm (uv _) (label S.card _ _)]; -- tune

variable {V B:Type*}[DecidableEq V][Ring B] [Algebra ℂ B](φ:A→ₐ[ℂ] B) (H:(n→T) → V→B) (v:n→ Finset V)
lemma monthly (P:B→ Prop)(r:ℕ)(R W:ℝ) (hw:∑ i,w i=1)(h:0<r)(v':Fintype.card n=10*r)(u: Pairwise (Disjoint on v))
    (Q:∀ t:n→T,∀ i, Blend (spool (H t) (v i) 1) R (φ (X i (t i)-1)))(e:∀ t:n→T,∀ Y, spool (H t) (univ.biUnion v) r Y → P Y) (hp:1 ≤R)(ht:∑ i, ‖w i‖≤ W):
    Blend P ((2^(22:ℕ)*R^(10:ℕ)* W^(10:ℕ))^r) (φ (ballet r univ (polar w X))) := by
 classical
 let F(i:n→T):= fun j=>X j (i j); let G(t):=φ (ballet r univ (F t)); let B:=(2^(22:ℕ)*R^(10:ℕ)); let b:=B^r; have hh:0≤b:=by unfold b B; positivity
 have hv(t): Blend P b (G t):= (loads_clean φ (F t) univ v (H t) r R (card_univ.trans v') (fun i _=> Q _ i) u h hp).mono (fun i=>e t i)
 rw [cue_m w X hw,map_sum]; simp_rw [map_smul]; apply (Blend.sum univ _ _ (fun i _=> (hv i).smul (uv i))).extendsTo; rw [←sum_mul,unit_toll, v']; refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg (fun i _=> norm_nonneg _)) ht (10*r)) hh).trans_eq ?_; unfold b B; rw [mul_comm]; simp_rw [mul_pow, pow_mul W]
end YM.CF.Pannier.Chancel.Lantern.Stencil
open YM.CF.Pannier.Chancel.Lantern.Stencil
#print axioms monthly
