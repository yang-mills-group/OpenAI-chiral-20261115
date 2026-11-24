import YM.CF.Support.Grove

/-! Basic nonnegative row costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
open Finset Function Fock
attribute [local instance] opCStarAlgebra
variable {I Y : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
abbrev Toll (I : Type*) := I→I→ℝ
lemma squares {c : Toll I} {r : ℝ} (v : I→ℝ) (h : 0 ≤ r) (p : ∀ i j, 0 ≤ c i j) (e : ∀ i, ∑ j, c i j≤r) (g : ∀ j, ∑ i, c i j≤r) :
    ∑ i:I, (∑ j, c i j*v j)^2 ≤ r^2 * ∑ i:I, v i ^2 := by
  have he (i:I) : (∑ j, c i j * v j)^2 ≤ r * ∑ j, c i j * v j^2 := (sum_sq_le_sum_mul_sum_of_sq_le_mul univ (f:=c i) (g:=fun j=>c i j * (v j)^2) (fun j _=>p i j) (fun j _=>mul_nonneg (p i j) (sq_nonneg _)) (fun j _=>le_of_eq (by ring))).trans (mul_le_mul_of_nonneg_right (e i) (sum_nonneg (fun j _=>mul_nonneg (p _ _) (sq_nonneg _))))
  apply (sum_le_sum (fun i (_:i∈(univ:Finset I))=>he i)).trans
  rw [←mul_sum,pow_two, mul_assoc]; apply mul_le_mul_of_nonneg_left _ h
  rw [mul_sum,sum_comm]; apply sum_le_sum; intro j _; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (g j) (sq_nonneg _)
lemma schur (c : Toll I) (A : Op I) (r : ℝ) (h : 0≤r) (p : ∀ i j, ‖A i j‖≤c i j) (e : ∀ i, ∑ j, c i j≤r) (g : ∀ j, ∑ i, c i j≤r) : ‖A‖≤r := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ h
  intro v; change ‖acts A v‖≤r* _; rw [←sq_le_sq₀ (norm_nonneg _) (by positivity),mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine le_trans ?_ (squares (fun j:I=> ‖v.ofLp j‖) h (fun i j=>(norm_nonneg _).trans (p i j)) e g)
  apply sum_le_sum; intro i _; apply pow_le_pow_left₀ (norm_nonneg _)
  rw [act_at,Matrix.mulVec,dotProduct]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j _; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (p i j) (norm_nonneg _)

structure Stage (Y I D G : Type*) where
  F : Field Y
  home : I→Y
  drive : G→D→D
  eval : Finset Y→D→D→ℝ
  pos S x y : 0 ≤ eval S x y
  includeV {S T} : S ⊆ T → ∀ x y, eval S x y ≤ eval T x y
variable {D G : Type*} {b : Stage Y I D G}
structure Tag (b : Stage Y I D G) where
  run : G→UNI I
  keeps (g i j) : b.home i≠b.home j → (run g).val i j=0

def Tag.reverseV (s : Tag b) : Tag b := ⟨ccU ∘ s.run,fun g i j h=> by change cc (s.run g).val i j=0; simp [s.keeps _ _ _ h]⟩
def board (b : Stage Y I D G) (Y' : Finset Y) := univ.filter fun i=> b.home i∈Y'
def strip (b : Stage Y I D G) (s : Finset Y) : Op I := cutM (board b s)
lemma stripL (S : Finset Y) (A : Op I) (i j) : (strip b S * A) i j=if b.home i∈S then A i j else 0 := by
  rw [strip,cutM,Matrix.diagonal_mul]; by_cases h:b.home i∈S <;> simp [board,h]
lemma stripR (S : Finset Y) (A : Op I) (i j) : (A*strip b S) i j=if b.home j∈S then A i j else 0 := by
  rw [strip, cutM, Matrix.mul_diagonal]; by_cases h:b.home j∈S <;> simp [board,h]
lemma strip_tag (s : Tag b) (g) (S : Finset Y) : strip b S*(s.run g).val=(s.run g).val * strip b S := by
  ext i j; rw [stripL,stripR]; by_cases h:b.home i=b.home j
  · rw [h]
  rw [s.keeps _ _ _ h]; simp
lemma strip_inv (s : Tag b) (g) (S : Finset Y) : strip b S*star (s.run g).val=star (s.run g).val*strip b S := by
  have he := congrArg star (strip_tag s g S); rw [star_mul,star_mul,show star (strip b S)=strip b S from (cutM_idp _).isSelfAdjoint] at he; exact he.symm
abbrev Raw (D I : Type*) := D→Op I
def Inter (s t : Tag b) (f : Raw D I) : Prop := ∀ g x, f (b.drive g x) * (t.run g).val=(s.run g).val * f x
lemma Inter.frame {s t : Tag b} {f} (h : Inter s t f) (g x) : f (b.drive g x)=(s.run g).val*f x * star (t.run g).val := by rw [← h, mul_assoc, show (t.run g).val*_=1 from (t.run g).property.2,mul_one]
variable [TopologicalSpace D] {A : Raw D I}
/-- Certificate at one scalar block entry. Cost includes support and a domain-wise cylinder Lipschitz bound.
`eval` allowed to distinguish parameters even at the empty support. -/
structure Expo (b : Stage Y I D G) (S : Finset Y) (i j : I) (w : ℝ) (f : D→ℂ) : Prop where
  positive : 0≤w
  triggered : w≠0 → Grove b.F S ∧ b.home i∈S ∧ b.home j∈S
  bounded x : ‖f x‖≤w
  variation x y : ‖f x-f y‖≤w*b.eval S x y
  connected : Continuous f
lemma Expo.swap' {S i j c f} (h : Expo b S i j c f) : Expo b S j i c f := { h with triggered e := ⟨(h.triggered e).1,(h.triggered e).2.2, (h.triggered e).2.1⟩ }
lemma Expo.discount {S i j c f} (h : Expo b S i j c f) (y : ℂ) : Expo b S i j (‖y‖*c) (fun t=> y*f t) := by
  refine ⟨mul_nonneg (norm_nonneg _) h.positive,fun e=> h.triggered (right_ne_zero_of_mul e),fun x=>?_,fun x z=>?_,continuous_const.mul h.connected⟩
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h.bounded x) (norm_nonneg _)
  rw [←mul_sub,norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.variation x z) (norm_nonneg _)
lemma Expo.minus {S i j c f} (h : Expo b S i j c f) : Expo b S i j c (fun x=> -f x) := by simpa using h.discount (-1) -- tune
lemma Expo.dual {S i j c f} (h : Expo b S i j c f) : Expo b S i j c (fun x=>star (f x)) :=
  { h with bounded := by simpa using h.bounded
           variation x y := by rw [←star_sub,norm_star]; exact h.variation x y
           connected := h.connected.star }
lemma Expo.weaken {S T i j c f} (h : Expo b S i j c f) (he : S ⊆ T) (hg : Grove b.F T) : Expo b T i j c f :=
  { h with triggered e := ⟨hg,he (h.triggered e).2.1,he (h.triggered e).2.2⟩
           variation x y := (h.variation x y).trans (mul_le_mul_of_nonneg_left (b.includeV he x y) h.positive) }
lemma Expo.add {S i j c d f g} (h : Expo b S i j c f) (he : Expo b S i j d g) : Expo b S i j (c+d) (fun x=>f x+g x) := by
  refine ⟨add_nonneg h.positive he.positive,fun e=>?_,fun x=>(norm_add_le ..).trans (add_le_add (h.bounded x) (he.bounded x)),fun x y=>?_,h.connected.add he.connected⟩
  · by_cases p:c=0
    · rw [p,zero_add] at e; exact he.triggered e
    exact h.triggered p
  rw [add_sub_add_comm, add_mul]; exact (norm_add_le ..).trans (add_le_add (h.variation x y) (he.variation x y))
lemma nothing (S : Finset Y) (i j) : Expo b S i j 0 (fun _=>0) := ⟨le_rfl,by simp,by simp,by simp,continuous_const⟩
lemma Expo.fuse {S T i j k c d f g} (h : Expo b S i j c f) (he : Expo b T j k d g) : Expo b (S∪T) i k (2*(c*d)) (fun x=>f x*g x) := by
  have pc := h.positive; have pd := he.positive
  refine ⟨by positivity,fun p=>?_,fun x=>?_,fun x y=>?_, h.connected.mul he.connected⟩
  · obtain ⟨p₁,o,u⟩ := h.triggered (left_ne_zero_of_mul (right_ne_zero_of_mul p)); obtain ⟨p₂,v,t⟩ := he.triggered (right_ne_zero_of_mul (right_ne_zero_of_mul p)); exact ⟨p₁.unite p₂ u v, mem_union_left T o, mem_union_right S t⟩
  · rw [norm_mul]; exact ((mul_le_mul (h.bounded _) (he.bounded _) (norm_nonneg _) pc).trans (le_mul_of_one_le_left (mul_nonneg pc pd) (by norm_num)))
  let r := b.eval (S∪T) x y; have hp : ‖f x-f y‖≤c*r := (h.variation x y).trans (mul_le_mul_of_nonneg_left (b.includeV subset_union_left x y) pc)
  have hq : ‖g x-g y‖ ≤ d*r := (he.variation x y).trans (mul_le_mul_of_nonneg_left (b.includeV subset_union_right x y) pd)
  rw [show f x*g x-f y*g y = (f x-f y)*g y+f x*(g x-g y) by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact (add_le_add (mul_le_mul hp (he.bounded _) (norm_nonneg _) ((norm_nonneg _).trans hp)) (mul_le_mul (h.bounded _) hq (norm_nonneg _) pc)).trans (le_of_eq (by unfold r; ring))
lemma Expo.sumK {S i j J} (t : Finset J) (c : J→ℝ) (f : J→ D→ℂ) (h : ∀ a∈t, Expo b S i j (c a) (f a)) : Expo b S i j (∑ a∈t,c a) (fun x=> ∑ a∈t,f a x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [sum_empty]; exact nothing ..
  | @insert k t e ih => simp only [sum_insert e]; exact (h k (mem_insert_self k t)).add (ih (fun i hi=>h i (mem_insert_of_mem hi)))
end YM.CF.Branch
