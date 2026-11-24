import YM.SU5.FiniteGaugeData.Tapestry.Colonnade

/-!
# At presenting height in the resolution-polynomial algebra

The Decking reading is on whole words. We can multiply freely *at*
the presenting slot, before any further ascent. Zeros there (not
modulo reflected Gram, but in the level algebra) can be retested
by any further pure product, even with no separations, provided
it doesn't use earlier slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter Finset TensorProduct
open scoped BigOperators Classical
open Buffered.Afterglow.Tapestry.Altitude
open PiTensorProduct (tprod)
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {E : ℕ → Type*} [∀ i, CommRing (E i)] [∀ i, Algebra ℂ (E i)]
variable (D : Decking A E) (v : Pad A)

lemma stone_height {x : ℕ → A} {n : ℕ} (p : Enough n x) : tprod ℂ x ∈ shorter A n :=
  board (P:={f|Enough n f}) p

private lemma multiply_last (n : ℕ) (f : ℕ → A) (y : A) :
    D.finish n (f * update (1:ℕ→A) n y) = D.finish n f * D.perceive n y := by
  let g := f * update (1:ℕ→A) n y
  have he : g n = f n * y := by simp [g]
  have hv (i : ℕ) (p : i < n) : g i = f i := by simp [g,update_of_ne p.ne]
  change D.finish n g = _
  cases n with
  | zero => rw [Decking.finish, Decking.finish, he, map_mul]
  | succ n => rw [Decking.finish, Decking.finish, he, map_mul,
      D.finish_agrees n (g:=f) (fun i h => hv i (by omega)), mul_assoc]

lemma crown_last (n : ℕ) (x : Cloud A) (p : x ∈ shorter A n) (y : A) :
    D.crown v n (x * pinhole A n y) = D.crown v n x * D.perceive n y := by
  apply boarded (P:={f|Enough n f}) (M:=fun x => _) ?_ ?_ ?_ ?_ p
  · intro f h
    rw [pinhole_apply, PiTensorProduct.tprod_mul_tprod, D.reckon_paid n v (f:=f) h]
    change D.crown v n (tprod ℂ (f * update (1:ℕ→A) n y)) = _
    rw [D.reckon_paid n v (Enough.together h (enough_slot n y)), multiply_last]
    -- `pinhole_apply` uses eta-unit function
  · simp
  · intro a b _ _ h t
    rw [add_mul,map_add,map_add,h,t,add_mul]
  intro r a _ h
  rw [Algebra.smul_mul_assoc, map_smul, map_smul, h, Algebra.smul_mul_assoc]

/-- Factor the slot away when ending a later-only test product. -/
lemma last_only (n : ℕ) (f : ℕ → A) (p : Enough n f) (q : ∀ i < n, f i = 1) :
    tprod ℂ f = pinhole A n (f n) := by
  rw [pinhole_apply]; apply congrArg (tprod ℂ)
  funext i
  rcases lt_trichotomy i n with u|rfl|u
  · rw [update_of_ne u.ne]; exact q i u
  · rw [update_self]
  rw [update_of_ne u.ne']; exact p i u

lemma crown_later (x : Cloud A) {n : ℕ} (a : x ∈ shorter A n) (h : D.crown v n x = 0)
    (f : ℕ → A) (q : ∀ i < n, f i = 1) (m : ℕ) (s : n ≤ m) (w : Enough m f) :
    D.crown v m (x * tprod ℂ f) = 0 := by
  induction m, s using Nat.le_induction generalizing f with
  | base => rw [last_only n f w q, crown_last D v n x a, h, zero_mul]
  | succ t e ih =>
    let g := update f (t+1) 1
    have H : Enough t g := by
      intro j hj
      unfold g
      rcases Nat.eq_or_lt_of_le (show t+1 ≤ j by omega) with b|b
      · rw [← b, update_self]
      rw [update_of_ne b.ne']; exact w j b
    have hmul : tprod ℂ f = tprod ℂ g * pinhole A (t+1) (f (t+1)) := by
      rw [pinhole_apply, PiTensorProduct.tprod_mul_tprod]
      apply congrArg (tprod ℂ)
      funext j
      by_cases b : j = t+1
      · simp [g,b]
      simp [g,b]
    have hu := ih g (fun j hj => by
      have h' : j ≠ t+1 := by omega
      simp [g,h', q _ hj]) H
    have hv : x * tprod ℂ g ∈ shorter A t := (shorter ..).mul_mem (climbs A e a) (stone_height H)
    rw [hmul, ← mul_assoc, crown_last D v (t+1) _ (climbs A (Nat.le_succ t) hv),
      D.joins t _ v hv, hu, map_zero, zero_mul]

lemma crown_later_poly (x : Cloud A) {n : ℕ} (a : x ∈ shorter A n) (h : D.crown v n x = 0)
    (m : ℕ) (s : n ≤ m) (S : Set ℕ) (b : S ⊆ Set.Ici n) (w : S ⊆ Set.Iic m)
    (F : ℕ → Subalgebra ℂ A) {y : Cloud A} (p : y ∈ colonnade S F) :
    D.crown v m (x*y) = 0 := by
  apply boarded (P:={f|Officer S F f}) (M:=fun y => _) ?_ ?_ ?_ ?_ p
  · intro f hf
    have z : Officer S F f := hf
    exact crown_later D v x a h f (fun i t => z.forbids i fun u => t.not_ge (b u)) m s (z.visible _ _ w)
  · simp
  · intro c d _ _ ih jh
    rw [mul_add, map_add, ih, jh, zero_add]
  intro z c _ ih
  rw [Algebra.mul_smul_comm, map_smul, ih, smul_zero]

end YM.CF.SatinRotation
#print axioms YM.CF.SatinRotation.crown_later_poly
