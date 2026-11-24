import ExactRunning.Finite.Polar
import YM.Next.STATIONARY.Loops.Fourier

/-!
# Momentum statement for a Hessian (including no-mixing)

`Resonance D K f`: two quiet momenta inserted in the Hessian of f
give 0 unless opposite, in which case K describes the result (per
site, argument = second-slot momentum). No conjugation; real f,
complex derivatives in the sense of `beat` (complexified Hessian).
No reflection assumptions.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

abbrev Kin (α : Type) := Momentum → CompM α α

variable {α : Type} [Fintype α] [DecidableEq α] {m : Side}
variable {D : Latitude} {F G : Kin α} {f g : Corn (Co m α) → ℝ}

structure Resonance (D : Latitude) (F : Kin α) (f : Corn (Co m α) → ℝ) : Prop where
  reg : ContDiffAt ℝ ω f 0
  on_relays {a b : Site m} {p : Momentum} (i j) (ha : D.quiet (mon a))
    (hb : D.quiet (mon b)) (hp : rolls (mon b) p) :
    beat f 0 2 ![relay a i,relay b j] =
      if a+b=0 then (cents m:ℂ) * F p i j else 0

namespace Resonance

lemma add (h : Resonance D F f) (i : Resonance D G g) : Resonance D (F+G) (f+g) := by
  refine ⟨h.reg.add i.reg, fun {a b p} x y ha hb hp => ?_⟩
  rw [beat_as_cost,note_add h.reg.analyticAt i.reg.analyticAt,smul_add, ← beat_as_cost,
      ← beat_as_cost,_root_.add_apply,h.on_relays x y ha hb hp,i.on_relays x y ha hb hp]
  split <;> simp [mul_add]

lemma weight (h : Resonance D F f) (c : ℝ) : Resonance D ((c:ℂ) • F) (c • f) := by
  refine ⟨h.reg.const_smul c, fun {a b p} x y ha hb hp => ?_⟩
  rw [beat_as_cost,note_bill c h.reg.analyticAt _,smul_comm, ← beat_as_cost,_root_.smul_apply,
      h.on_relays x y ha hb hp]
  split <;> simp [mul_left_comm]
lemma sub (h : Resonance D F f) (i : Resonance D G g) : Resonance D (F-G) (f-g) := by
  simpa [sub_eq_add_neg] using h.add (i.weight (-1))

lemma const (D : Latitude) (c : ℝ) : Resonance D 0 (fun _ : Corn (Co m α) => c) := by
  refine ⟨contDiffAt_const,fun i j _ _ _ => ?_⟩
  unfold beat enlarge
  simp [recording_apply,iteratedFDeriv_const_of_ne (by decide : 2≠0)]

lemma viaBeat (h : Resonance D F f) (hg : ContDiffAt ℝ ω g 0)
    (he : ∀ u v, D.repeats u → D.repeats v → beat f 0 2 ![u,v] = beat g 0 2 ![u,v]) :
    Resonance D F g := by
  refine ⟨hg, fun i j ha hb hp => ?_⟩
  refine Eq.trans (he _ _ (Latitude.repeats.wave ha (Pi.single i 1)) (Latitude.repeats.wave hb (Pi.single j 1))).symm ?_
  exact h.on_relays i j ha hb hp

lemma viaHessian (h : Resonance D F f) (hg : ContDiffAt ℝ ω g 0)
    (he : iteratedFDeriv ℝ 2 f 0 = iteratedFDeriv ℝ 2 g 0) : Resonance D F g :=
  h.viaBeat hg (fun _ _ _ _ => by unfold beat;rw [he])

lemma viaTouch (h : Resonance D F f) (hg : ContDiffAt ℝ ω g 0)
    (he : ∀ v : Corn (Co m α), D.repeats v →
      Touch (fun t => f (t • v)) (fun t => g (t • v))) : Resonance D F g :=
  h.viaBeat hg (fun _ _ hu hv => D.beat_of_touch h.reg hg he hu hv)

end Resonance
/-- Complex bilinear Hessian -/
def beatL (f : Corn α → ℝ) : Phase α →ₗ[ℂ] Phase α →ₗ[ℂ] ℂ where
  toFun u :=
  { toFun := fun v => beat f 0 2 ![u,v]
    map_add' := by
      intro v w
      have he (v) : (![u,v]:Fin 2 → Phase α) = update ![u,0] 1 v := by ext i; fin_cases i <;> simp
      rw [he,he v,he w,MultilinearMap.map_update_add]
    map_smul' := by
      intro c v
      have he (v) : (![u,v]:Fin 2 → Phase α) = update ![u,0] 1 v := by ext i; fin_cases i <;> simp
      rw [he,he v,MultilinearMap.map_update_smul]; rfl }
  map_add' := by
    intro u w; apply LinearMap.ext; intro v
    have he (u) : (![u,v]:Fin 2 → Phase α) = update ![0,v] 0 u := by ext i; fin_cases i <;> simp
    change beat f 0 2 ![u+w,v] = beat f 0 2 ![u,v] + beat f 0 2 ![w,v]
    rw [he,he u,he w,MultilinearMap.map_update_add]
  map_smul' := by
    intro c u
    apply LinearMap.ext; intro v

    have he (u) : (![u,v]:Fin 2 → Phase α) = update ![0,v] 0 u := by ext i; fin_cases i <;> simp
    change beat f 0 2 ![c•u,v] = c • beat f 0 2 ![u,v]
    rw [he,he u,MultilinearMap.map_update_smul]

def tuneL (p : Site m) : Phase α →ₗ[ℂ] Phase (Co m α) where
  toFun := tune p
  map_add' := by intro u v; ext i; simp [tune,mul_add]
  map_smul' := fun z v => tune_smul p v z

lemma phase_ext {X : Type} [AddCommMonoid X] [Module ℂ X] {f g : Phase α →ₗ[ℂ] X}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearMap.pi_ext; intro i v
  rw [show Pi.single i v = v • Pi.single i 1 by ext k; simp [Pi.single_apply],
      map_smul,map_smul,h]

lemma toBilin'_dot (A : CompM α α) (u v : Phase α) :
    Matrix.toBilin' A u v = dotProduct u (A *ᵥ v) := by
  rw [Matrix.toBilin'_apply]
  simp [Matrix.mulVec,dotProduct, Finset.mul_sum,mul_assoc]

lemma toBilin'_single (A : CompM α α) (i j) :
    Matrix.toBilin' A (Pi.single i 1) (Pi.single j 1) = A i j := by
  rw [toBilin'_dot]
  simp

namespace Resonance

lemma wavesM (h : Resonance D F f) {a b : Site m} {p : Momentum}
    (ha : D.quiet (mon a)) (hb : D.quiet (mon b)) (hp : rolls (mon b) p) :
    (beatL f).compl₁₂ (tuneL a) (tuneL b) =
    if a+b=0 then (cents m:ℂ) • Matrix.toBilin' (F p) else 0 := by
  apply phase_ext; intro i; apply phase_ext; intro j
  let he := h.on_relays i j ha hb hp
  refine he.trans ?_
  split <;> simp

lemma waves (h : Resonance D F f) {a b : Site m} {p : Momentum}
    (ha : D.quiet (mon a)) (hb : D.quiet (mon b)) (hp : rolls (mon b) p) (u v : Phase α) :
    beat f 0 2 ![tune a u,tune b v] =
    if a+b=0 then (cents m:ℂ) * dotProduct u (F p *ᵥ v) else 0 := by
  change (beatL f).compl₁₂ (tuneL a) (tuneL b) u v = _
  rw [h.wavesM ha hb hp]; split <;> simp [toBilin'_dot]

lemma pair (h : Resonance D F f) {b : Site m} {p : Momentum}
    (i : rolls (mon b) p) (j : D.quiet p) (u v : Phase α) :
    (↑(cents m))⁻¹ * beat f 0 2 ![tune (-b) u,tune b v] =
    dotProduct u (F p *ᵥ v) := by
  rw [h.waves (j.neg.rolls i.flip_sign.symm) (j.rolls i.symm) i,
    if_pos (neg_add_cancel b), inv_mul_cancel_left₀ (by exact_mod_cast cents_pos.ne')]
end Resonance
end ExactRunning
