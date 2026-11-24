import GaugeFieldConstruction.Labels
import Mathlib.Analysis.Complex.Basic

/-!
# Orbit calculation for U1: picking columns before testing
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function Set
open scoped BigOperators
namespace Labels
variable {α β : Type*} (A : Labels α)
/-- Array of raw component coefficients with the indicated transformation laws. -/
def fixed (K : Type*) [Field K] : Submodule K (α → K) where
  carrier := {z | ∀ g i, z (A.move g i) = pay (A.cost g i) (z i)}
  add_mem' := by
    intro a b ha hb g i
    simp only [Pi.add_apply, ha g i, hb g i, pay_add]
  smul_mem' := by
    intro c a ha g i
    simp only [Pi.smul_apply, ha g i]; cases A.cost g i <;> simp
  zero_mem' := by intros g i; simp

lemma fixed_def {K : Type*} [Field K] (z : α → K) : z ∈ A.fixed K ↔
    ∀ g i, z (A.move g i) = pay (A.cost g i) (z i) := Iff.rfl

/-- Motion of raw array. -/
def transport (K : Type*) [Field K] (g : Signed) : Module.End K (α → K) where
  toFun z i := pay (A.cost g⁻¹ i) (z (A.move g⁻¹ i))
  map_add' := by intro a b; ext1 j; exact pay_add ..
  map_smul' := by
    intro c a; ext1 j
    dsimp only [Pi.smul_apply, RingHom.id_apply]; cases A.cost g⁻¹ j <;> simp

@[simp] lemma transport_value {K : Type*} [Field K] (g : Signed) (z : α → K) (i : α) :
    A.transport K g z (A.move g i) = pay (A.cost g i) (z i) := by
  change pay (A.cost g⁻¹ _) (z (A.move g⁻¹ _)) = _; simp

theorem group (K : Type*) [Field K] (g h : Signed) :
    A.transport K g * A.transport K h = A.transport K (g*h) := by
  ext1 z
  ext1 j
  obtain ⟨i,rfl⟩ := (A.equivMove (g*h)).surjective j
  change A.transport K g (A.transport K h z) (A.move _ _) = A.transport K (g*h) z (A.move _ _)
  rw [transport_value, move_mul, transport_value, transport_value, pay_comp, cost_mul]

lemma fixe_iff {K : Type*} [Field K] (z : α → K) : z ∈ A.fixed K ↔ ∀ g, A.transport K g z = z := by
  constructor
  · intro h g; ext1 j
    obtain ⟨i,rfl⟩ := (A.equivMove g).surjective j
    change A.transport K g z (A.move g i) = z (A.move g i)
    rw [transport_value]; exact (h g i).symm
  intro h g i; rw [← transport_value, h]

variable [DecidableEq α]

lemma one_impulse (K : Type*) [Field K] (g : Signed) (i : α) :
    A.transport K g (Pi.single i 1) = Pi.single (A.move g i) (pay (A.cost g i) 1) := by
  ext1 j
  obtain ⟨k,rfl⟩ := (A.equivMove g).surjective j
  change A.transport K g (Pi.single i 1) (A.move g k) = Pi.single (M:=fun _ => K) _ _ (A.move g k)
  rw [transport_value]
  by_cases h : k=i
  · subst k; simp
  simp [Pi.single_eq_of_ne, h, (A.inj g).ne h]

/-- Permutation sum of one column. As soon as the stabilizer is positive this
multiplies the Orbit column of RankSupplement by a nonzero integer. -/
def orbit (K : Type*) [Field K] (i : α) : α → K :=
  ∑ p : Equiv.Perm Axis, A.transport K (unsigned p) (Pi.single i 1)

lemma fixes_perms (K : Type*) [Field K] (i : α) (p : Equiv.Perm Axis) :
    A.transport K (unsigned p) (A.orbit K i) = A.orbit K i := by
  rw [orbit, map_sum]
  have he (q) (z : α → K) : A.transport K (unsigned p) (A.transport K (unsigned q) z) =
      A.transport K (unsigned (p*q)) z := by
    rw [unsigned_mul, ← A.group]; rfl
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.mulLeft p)  (fun q => A.transport K (unsigned q) (Pi.single i 1))
lemma fixes_change (K : Type*) [Field K] (i : α) (p : Equiv.Perm Axis) :
    A.orbit K i = pay (A.cost (unsigned p) i) (A.orbit K (A.move (unsigned p) i)) := by
  have hv : Pi.single (A.move (unsigned p) i) (pay (A.cost (unsigned p) i) (1:K)) =
      pay (A.cost (unsigned p) i) (Pi.single (M:=fun _ => K) (A.move (unsigned p) i) (1:K)) := by
    cases A.cost (unsigned p) i <;> simp
    ext1 j; simp [Pi.single_apply]; split_ifs <;> simp
  have he (q) : A.transport K (unsigned (q*p)) (Pi.single i 1) =
      pay (A.cost (unsigned p) i)
        (A.transport K (unsigned q) (Pi.single (A.move (unsigned p) i) 1)) := by
    rw [unsigned_mul, ← A.group, Module.End.mul_apply, A.one_impulse, hv]
    cases A.cost (unsigned p) i <;> simp
  unfold orbit
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight p)]
  change ∑ q : Equiv.Perm Axis, A.transport K (unsigned (q*p)) (Pi.single i 1) = _
  simp_rw [he]
  cases A.cost (unsigned p) i <;> simp

/-- Admits the diagonal sign-flip subgroup (the parity filter of the construction notes). -/
def evenAt (i : α) := ∀ a, A.move (Signed.mirror a) i=i ∧ A.cost (Signed.mirror a) i=false

theorem orbit_mem {K : Type*} [Field K] (i : α) (h : A.evenAt i) : A.orbit K i ∈ A.fixed K := by
  refine (A.fixe_iff _).mpr (fun g => signed_induction (P:=fun g =>
    A.transport K g (A.orbit K i) = A.orbit K i) (A.fixes_perms K i) ?_ ?_ g)
  · intro a; rw [orbit, map_sum]
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨b,rfl⟩ := p.surjective a
    have hv : A.transport K (Signed.mirror b) (Pi.single i 1) = Pi.single i 1 := by
      rw [one_impulse,(h b).1,(h b).2,pay_false]
    change (A.transport K (Signed.mirror _) * A.transport K (unsigned p)) _ = _
    rw [A.group, ← unsigned_mirror p b, ← A.group, Module.End.mul_apply, hv]
  intro x y hx hy
  rw [← A.group, Module.End.mul_apply, hy, hx]

/-- Good permutation stabilizer. -/
def coheres (i : α) := ∀ p, A.move (unsigned p) i=i → A.cost (unsigned p) i=false

lemma orbit_value (K : Type*) [Field K] (i j : α) :
    A.orbit K i j = ∑ p : Equiv.Perm Axis,
      if j=A.move (unsigned p) i then pay (A.cost (unsigned p) i) (1:K) else 0 := by
  simp [orbit, Finset.sum_apply, A.one_impulse, Pi.single_apply]

lemma not_zero_self {K : Type*} [Field K] [CharZero K] (i : α) (hh : A.coheres i) :
    A.orbit K i i ≠ 0 := by
  rw [orbit_value]
  let Q := Finset.univ.filter (fun p => i = A.move (unsigned p) i)
  rw [← Finset.sum_filter]
  change ∑ p∈Q, _ ≠ (0:K)
  have hv (p) (h : p∈Q) : pay (A.cost (unsigned p) i) (1:K) = 1 := by
    rw [hh p ((mem_filter.mp h).2).symm]; rfl
  rw [Finset.sum_congr rfl hv]
  have hc : Q.Nonempty := ⟨1, by simp [Q]⟩
  simpa using (show (Q.card:K) ≠ 0 by exact_mod_cast hc.card_pos.ne')

omit [DecidableEq α] in
lemma cannot {K : Type*} [Field K] [CharZero K] (z : α → K) (hz : z ∈ A.fixed K)
    (i : α) (g : Signed) (h₁ : A.move g i=i) (h₂ : A.cost g i=true) : z i = 0 := by
  have he := (A.fixed_def z).mp hz g i
  rw [h₁,h₂,pay_true] at he
  by_contra hv
  exact mul_ne_zero (by norm_num : (2:K)≠0) hv (by rw [two_mul]; exact eq_neg_iff_add_eq_zero.mp he)

/-- An orbit basis criteria. The disjunction may omit indices only by a
 *negative* motion fixing the index. -/
theorem basis_criterion [Fintype α] (K : Type*) [Field K] [CharZero K] (I : Finset α)
    (good : ∀ i∈I, A.evenAt i ∧ A.coheres i)
    (unique : ∀ i∈I, ∀ j∈I, ∀ p, A.move (unsigned p) i=j → i=j)
    (covered : ∀ i, (∃ g, A.move g i=i ∧ A.cost g i=true) ∨
      ∃ j∈I, ∃ p, A.move (unsigned p) j=i) :
    A.fixed K = Submodule.span K (A.orbit K '' (I:Set α)) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · intro f hf
    let z := fun i => f i / A.orbit K i i
    let w := ∑ i∈I, z i • A.orbit K i
    have hu : w∈A.fixed K := Submodule.sum_mem _ (fun i hi => (A.fixed K).smul_mem _ (A.orbit_mem i (good i hi).1))
    have ht (i : α) (hi : i ∈ I) : w i=f i := by
      simp only [w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_eq_single_of_mem i (by assumption)]
      · exact div_mul_cancel₀ _ (A.not_zero_self i (good i (by assumption)).2)
      intro j hj hji
      rw [A.orbit_value, Finset.sum_eq_zero]; exact mul_zero _
      intro p _
      rw [if_neg (fun h => hji (unique j hj i (by assumption) p h.symm))]
    have h : f=w := by
      funext i; symm
      rcases covered i with ⟨g,h₁,h₂⟩|⟨j,hj,p,rfl⟩
      · rw [A.cannot f hf i g h₁ h₂, A.cannot w hu i g h₁ h₂]
      rw [(A.fixed_def _).mp hf (unsigned p) j,(A.fixed_def _).mp hu (unsigned p) j,ht j hj]
    have hw : w∈Submodule.span K (A.orbit K '' (I:Set α)) :=
      Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩))
    rwa [← h] at hw
  rintro y ⟨i,hi,rfl⟩; exact A.orbit_mem i (good i hi).1

/-- Component restriction for arbitrary positive or omittable checks. -/
def coveredBy (r : List α) (x : α) := (∃ g, A.move g x=x ∧ A.cost g x=true) ∨
      ∃ j∈r, ∃ p, A.move (unsigned p) j=x

omit [DecidableEq α] in
theorem cover_expand (B : Labels β) (q : List (α × β)) (test : List β)
    (suffices' : ∀ j, ∃ i ∈ test, ∃ p, B.move (unsigned p) i = j)
    (passes : ∀ i∈test, ∀ a, (A.tensorProd B).coveredBy q (a,i)) (k : α × β) :
    (A.tensorProd B).coveredBy q k := by
  obtain ⟨a,j⟩ := k
  obtain ⟨i,hi,p,rfl⟩ := suffices' j
  obtain ⟨b,rfl⟩ := (A.equivMove (unsigned p)).surjective a
  let D := A.tensorProd B
  let g := unsigned p; let x := (b,i)
  change D.coveredBy q (D.move g x)
  rcases passes i hi b with ⟨w,h₁,h₂⟩|⟨c,hc,s,h⟩
  · left
    change D.move w x=x at h₁; change D.cost w x=true at h₂
    exact ⟨g*w*g⁻¹, by rw [move_mul,inv_move,move_mul,h₁], by
      rw [cost_mul,inv_cost,inv_move,cost_mul,h₁,h₂]; cases D.cost g x <;> decide⟩
  right; change D.move (unsigned s) _ = x at h
  exact ⟨c,hc,p*s,by rw [unsigned_mul, D.move_mul,h]⟩
end Labels
end YM.GaugeFieldConstruction
