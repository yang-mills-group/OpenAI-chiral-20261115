import ExactRunning.Scenes.Pairs
import ExactRunning.Thermo.Probe

/-!
# Kinetic scenes

A kinetic scene unfolded in the internal momentum, retaining ordinary
matrix indices in the two external legs. Limits at fixed regulator by
Riemann integration, independently for every entry.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α : Type}

abbrev Scene (ι : Type) := Momentum → Momentum → CompM ι ι

namespace Latitude
variable (D : Latitude)

/-- First external (positive: second slot frequency), then internal.
All momenta in radians. Per site at that scale. -/
def run (X : Scene α) : Kin α :=
  fun p => of fun i j => D.mean (fun r => X p r i j)
def play (m : Side) (X : Scene α) : Kin α :=
  fun p => of fun i j => D.mesh m (fun r => X p r i j)

variable {p : Momentum}
lemma play_add (X Y : Scene α) (m : Side) : D.play m (X+Y) = D.play m X + D.play m Y := by
  ext p i j
  simp only [play, Pi.add_apply, Matrix.of_apply,Matrix.add_apply,mesh,mask,shop]

  rw [← mul_add, ← sum_add_distrib]; congr 1
  refine sum_congr rfl fun x _ => ?_; split <;> simp
lemma play_smul (X : Scene α) (c : ℂ) (m : Side) : D.play m (c•X) = c • D.play m X := by
  ext p i j
  simp only [play, Pi.smul_apply, Matrix.of_apply,Matrix.smul_apply,mesh,mask,shop,smul_eq_mul]
  conv_rhs => rw [mul_left_comm, Finset.mul_sum]
  congr 1; refine sum_congr rfl fun x _ => ?_; split <;> simp

lemma play_sub (X Y : Scene α) (m : Side) : D.play m (X-Y) = D.play m X - D.play m Y := by
  rw [sub_eq_add_neg,play_add, ← neg_one_smul ℂ Y,play_smul,neg_one_smul,
      sub_eq_add_neg]

/-- Joint p,q regularity for safe internal and quiet external. -/
def Medium (X : Scene α) :=
  ∀ (i j : α), ∀ {p q}, star p = p → D.quiet p → star q = q → D.safe q →
    ContDiffAt ℝ ω (fun z : Momentum × Momentum => X z.1 z.2 i j) (p,q)

namespace Medium
variable {D X Y}
lemma add (h : D.Medium (α:=α) X) (k : D.Medium Y) :
    D.Medium (X+Y) := fun i j _ _ a b c d => (h i j a b c d).add (k i j a b c d)
lemma sub (h : D.Medium (α:=α) X) (k : D.Medium Y) :
    D.Medium (X-Y) := fun i j _ _ a b c d => (h i j a b c d).sub (k i j a b c d)
lemma smul (h : D.Medium (α:=α) X) (e : ℂ) :
    D.Medium (e • X) := fun i j _ _ a b c d => (h i j a b c d).const_smul e

variable (h : D.Medium (α:=α) X)
include h
lemma line {g : ℝ → Momentum} (hg : ContDiff ℝ ω g)
    (hr : ∀ t, star (g t) = g t) (hq : ∀ t, D.quiet (g t)) (i j) :
    D.Regular (fun t r => X (g t) r i j) :=
  fun z hz => (h i j (hr z.1) (hq _) (tap_real z.2) hz).comp (g:=fun w : Momentum × Momentum => X w.1 w.2 i j) z
    ((hg.contDiffAt.comp z contDiffAt_fst).prodMk (tap_smooth.contDiffAt.comp z contDiffAt_snd))

lemma ingredient (hp : star p=p) (hq : D.quiet p) (i j) :
    ∀ y, D.safe (tap y) → ContinuousAt (fun x => X p (tap x) i j) y :=
  (h.line (contDiff_const (c:=p)) (fun _ => hp) (fun _ => hq) i j).fixed 0

/-- Entries jointly, with the product topology. -/
lemma plays (hp : star p=p) (hq : D.quiet p) {m : ℕ → Side}
    (hm : Tendsto (fun n => (m n).val) atTop atTop) :
    Tendsto (fun n => D.play (m n) X p) atTop (𝓝 (D.run X p)) :=
  tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
    D.tendsto_mesh hm (h.ingredient hp hq i j)

lemma smooth {g : ℝ → Momentum} (hg : ContDiff ℝ ω g)
    (hr : ∀ t, star (g t)=g t) (hq : ∀ t,D.quiet (g t)) (i j) :
    ContDiff ℝ ∞ (fun t => D.run X (g t) i j) :=
  (h.line hg hr hq i j).smooth

lemma peel {g : ℝ → Momentum} (hg : ContDiff ℝ ω g)
    (hr : ∀ t, star (g t)=g t) (hq : ∀ t,D.quiet (g t)) (i j) :
    quad (fun t => D.run X (g t) i j) =
      D.mean (fun r => quad (fun t=> X (g t) r i j)) :=
  (h.line hg hr hq i j).quad_mean
end Medium
end Latitude
end ExactRunning
