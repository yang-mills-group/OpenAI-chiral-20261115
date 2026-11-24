import YM.CF.Phase.Rays

/-! Relative additive logarithm, with exact integer part controlled. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Finset
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U : Skin m B}
abbrev Cue (m : Side) := Cube.Field m
def slot (m : Side) (v : Cue m) : ArrayF m := fun t=> v t.1
def ZeroF (m B : Side) (U : Skin m B) (x : Cue m) := Verified m B margin U (slot m x) {0}
def twin (m : Side) (x y : Cue m) := capRow (slot m x) 1 y
def EdgeP (m B : Side) (U : Skin m B) (x y : Cue m) := Verified m B margin U (twin m x y) (insert 1 {0})
def amount (m B : Side) (c : Part m B) (U : Skin m B) (x y : Cue m) := ray m B c U (twin m x y) (stick 0) (stick 1)
def Arch (m B : Side) (U : Skin m B) (x y t : Cue m) := EdgeP m B U x t ∧ EdgeP m B U y t
lemma inherited {x y} (g : EdgeP m B U x y) : ZeroF m B U x := verified_restrict g (subset_insert 1 {0}) (fun i hi=> by
  have H : i.2≠1 := by simp [(mem_singleton.mp hi)]
  simp [twin,capRow,H])
lemma cue_from (U : Skin m B) : ∃ x, ZeroF m B U x := by
  let y := Classical.arbitrary (Cue m)
  obtain ⟨v,h⟩ := extensions m B U (univ:Finset Unit) (fun _=>slot m y) (fun _=>∅) 0 (by simp) (by intro; simp [ending]) (fun _ _ a h=> by simp at h)
  have ht := h () (mem_univ ()); rw [insert_empty] at ht
  exact ⟨v, verified_restrict ht (subset_refl _) fun i g=> by simp [slot,capRow,mem_singleton.mp g]⟩
lemma ties {I : Type} [DecidableEq I] {S : Finset I} (h : S.card≤6) (f : I→Cue m) (g : ∀ i∈S, ZeroF m B U (f i)) :
    ∃ z, ∀ i∈S, EdgeP m B U (f i) z := extensions m B U S (fun i=>slot m (f i)) (fun _=>{0}) 1 h (by intro i hi; simp [ending]) g
lemma arches {x y} (h : ZeroF m B U x) (g : ZeroF m B U y) : ∃ t, Arch m B U x y t := by
  classical
  obtain ⟨z,h⟩ := ties (U:=U) (show ({x,y}:Finset (Cue m)).card≤6 from (card_insert_le ..).trans (by simp)) id (by simp [h,g])
  exact ⟨z, h _ (mem_insert_self ..), h _ (mem_insert_of_mem (mem_singleton_self _))⟩ -- tune
lemma over (r : Zone) (s t : ArrayF m) (q : Sq) (h : ∀ i : Spot m, i.2∈r→s i=t i) (hz : q∈zone r) (U : Skin m B) :
    bow m B U s q=bow m B U t q := by rw [bow,bow,grain,grain,paintV_agree s t q (fun i e=> h i (by by_contra g; exact e (hz.2 _ g))) U]
lemma shadow (r : Zone) (s t : ArrayF m) (x y : Sq) (h : ∀ i : Spot m,i.2∈r → s i=t i)
    (hz : x∈zone r) (he : y∈zone r) (c : Part m B) (U : Skin m B) : ray m B c U s x y=ray m B c U t x y := by
  unfold ray; apply sum_congr rfl; intro i hi; rw [rad,over r s t _ h (inc_in hz he B (mem_range.mp hi).le),over r s t _ h (inc_in hz he B (mem_range.mp hi))]; rfl
lemma spotFrame {x : Cue m} (i : Row) (y : ArrayF m) -- remove
    (u : ∀ j : Index m, y (j,i)=x j) (U : Skin m B) : bow m B U y (stick i) = bow m B U (slot m x) (stick i) := by
  apply over {i} _ _ _ _ (stick_in _ (mem_singleton_self _))
  rintro ⟨j,k⟩ hk; have he : k=i := mem_singleton.mp hk; subst k; exact u j
def pair (m B : Side) (U : Skin m B) (x : Cue m) := bow m B U (slot m x) (stick 0)
-- same vertex realized on any row
lemma spot_pair {x : Cue m} (i : Row) (s : ArrayF m) (u : ∀ j : Index m, s (j,i)=x j) (U : Skin m B) : bow m B U s (stick i)=pair m B U x := by
  have h (i) (z) : paint m B U (slot m x) (stick i) z=∑ a, weight m B z a • freight m B U z a (x a) := by
    rw [paint,Fintype.sum_prod_type]; apply sum_congr rfl; intro a _; rw [sum_eq_single_of_mem _ (mem_univ i),stick,dirac_cash]; rfl
    intro b _ hb; rw [empty_cash (show stick i b=0 from by simp [stick, hb]),zero_smul]
  have H : paintV m B U (slot m x) (stick i)=paintV m B U (slot m x) (stick 0) := by funext y; unfold paintV; rw [h,h]
  rw [spotFrame i _ u,pair,bow,bow,grain,grain,H]
section
variable (c : Part m B) {e : ℝ} (b : Room B e) (g : Guard U e)
include b g
def bill (m B : Side) (c : Part m B) (U : Skin m B) (x y z : Cue m) := amount m B c U x z-amount m B c U y z
lemma elevate (x y z v : Cue m) (h : Verified m B margin U (capRow (twin m x z) 2 v) (insert 2 (insert 1 {0}))) (H : Verified m B margin U (capRow (twin m y z) 2 v) (insert 2 (insert 1 {0}))) :
    bill m B c U x y z = ray m B c U (capRow (slot m x) 2 v) (stick 0) (stick 2) -
                          ray m B c U (capRow (slot m y) 2 v) (stick 0) (stick 2) := by
  let D (x) := capRow (twin m x z) 2 v
  let r : Zone := insert 2 (insert 1 {0}); let F := ray m B c U
  have main (x) (h : Verified m B margin U (D x) r) :
      F (capRow (slot m x) 2 v) (stick 0) (stick 2)=amount m B c U x z+ F (capRow (slot m z) 2 v) (stick 1) (stick 2) := by
    let X := D x
    have h₁ : F X (stick 0) (stick 2)=F (capRow (slot m x) 2 v) (stick 0) (stick 2) := by
      apply shadow {0,2} _ _ _ _ _ (stick_in _ (by simp)) (stick_in _ (by simp)); rintro ⟨a,i⟩ hx; simp only [mem_insert,mem_singleton] at hx; rcases (show i=0 ∨ i=2 from hx) with H|H <;> subst i <;> simp [X,D,twin,capRow,slot]
    have h₂ : F X (stick 0) (stick 1)=amount m B c U x z := by
      apply shadow {0,1} _ _ _ _ _ (stick_in _ (by simp)) (stick_in _ (by simp)); rintro ⟨a,i⟩ hx; simp only [mem_insert,mem_singleton] at hx; rcases (show i=0 ∨ i=1 from hx) with H|H <;> subst i <;> simp [X,D,twin,capRow,slot]
    have h₃ : F X (stick 1) (stick 2)=F (capRow (slot m z) 2 v) (stick 1) (stick 2) := by
      apply shadow {1,2} _ _ _ _ _ (stick_in _ (by simp)) (stick_in _ (by simp)); rintro ⟨a,i⟩ hx; simp only [mem_insert,mem_singleton] at hx; rcases (show i=1 ∨ i=2 from hx) with H|H <;> subst i <;> simp [X,D,twin,capRow,slot]
    rw [←h₁,←h₂,←h₃]; exact ray_add c b g h (stick_in _ (by simp [r])) (stick_in _ (by simp [r])) (stick_in _ (by simp [r]))
  change _=F _ _ _-F _ _ _; rw [main x h, main y H,add_sub_add_right_eq_sub]; rfl
lemma voice (x y a v : Cue m) (h : Arch m B U x y a) (H : Arch m B U x y v) : bill m B c U x y a=bill m B c U x y v := by
  let f : Fin 4 → ArrayF m := ![twin m x a,twin m y a,twin m x v,twin m y v]
  obtain ⟨w,G⟩ := extensions m B U (univ:Finset (Fin 4)) f (fun _=> insert 1 {0}) 2 (by simp) (by intro i hi; simp [ending]) (by
    intro i _; fin_cases i; exact h.1; exact h.2; exact H.1; exact H.2)
  rw [elevate c b g x y a w (G 0 (by simp)) (G 1 (by simp)), elevate c b g x y v w (G 2 (by simp)) (G 3 (by simp))]
end
end YM.CF.Phase
