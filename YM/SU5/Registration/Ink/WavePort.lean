/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Shift.Ridge
import YM.Shift.Sol
/-!
 General module version for the actual G in M4; adapting YM pinned contour chain.
 Adapted from  YM/Boundary/Contour, Shift/Ridge and Shift/Sol.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Boundary Mink Function Set Filter MeasureTheory Complex LinearMap Probe LineDeriv Distribution
open scoped Topology BigOperators ContDiff InnerProductSpace Interval ENNReal
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

structure WView (V : Type*) [AddCommGroup V] [Module ℂ V] where
  W (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => V) (Distn (Points n))

structure InkWaves (V : Type*) [AddCommGroup V] [Module ℂ V] where
  F (n : ℕ) : Times n → SpacePoints n → MultilinearMap ℂ (fun _ : Fin n => V) ℂ

namespace InkWaves
variable (P : InkWaves V)

def restricted (v : Fin n → V) (y : Heights n) (p : Points n) := P.F n (shift p y) (trace p) v

def atSlopes (v : Fin n → V) (h : Heights n) (ε : ℝ) (f : Joint n) :=
    ∫ x, P.restricted v (ε • h) x * f x

/-- need only regularity of reads; matching to Eu prices handled separately below -/
structure Region : Prop where
  together (n : ℕ) (v : Fin n → V) : ContinuousOn (fun p : Times n × SpacePoints n =>
    P.F n p.1 p.2 v) (strict n ×ˢ univ)
  hol (n : ℕ) (v : Fin n → V) (x : SpacePoints n) :
    DifferentiableOn ℂ (fun z => P.F n z x v) (strict n)
/-- s-order, Lebesgue dt d³ x in `Points.volume_product,volume_divide`.
One limit positive profile `u` for every test, each *ordered* u. -/
structure Opens (F : WView V) : Prop where
  int (n : ℕ) (v : Fin n → V) (y : Heights n) (h : y ∈ east n) (f : Joint n) :
    Integrable (fun x => P.restricted v y x * f x)
  profile (n : ℕ) (v : Fin n → V) (y : Heights n) (hy : y ∈ east n) (f : Joint n) :
    Tendsto (fun ε => atSlopes P v y ε f) (𝓝[>] (0:ℝ)) (𝓝 (F.W n v f))

/-- Stronger all-ordered-heights form, useful for Gram limits. -/
structure NonTangentialFree (F : WView V) : Prop where
  int (n : ℕ) (v : Fin n → V) (y : Heights n) (h : y ∈ east n) (f : Joint n) :
    Integrable (fun x => P.restricted v y x * f x)
  corner (n : ℕ) (v : Fin n → V) (f : Joint n) :
    Tendsto (fun u => ∫ x, P.restricted v u x*f x) (𝓝[east n] (0:Heights n)) (𝓝 (F.W n v f))

lemma exposed (F : WView V) (h : P.NonTangentialFree F) : P.Opens F := by
  refine ⟨h.int,fun i v y hy f => ?_⟩
  have he : Tendsto (fun ε : ℝ => ε • y) (𝓝[>] (0:ℝ)) (𝓝[east i] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,?_⟩
    · have hc := (continuous_id.smul (continuous_const (y := y))).continuousAt (x := (0:ℝ)) |>.tendsto
      change Tendsto (fun x : ℝ => x • y) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) • y)) at hc
      rw [show (0:ℝ) • y=0 from zero_smul ..] at hc; exact hc.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun a b hb => mul_lt_mul_of_pos_left (hy hb) (show 0 < x from hx)
  exact (h.corner i v f).comp he
end InkWaves

namespace InkWaves
variable (F : InkWaves V)

/-- Germ independent of a on contour not assumed here. -/
def Breathes : Prop := ∀ n (v : Fin n → V), ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m

def psi (v : Fin n → V) (y : Heights n) (f : Joint n) :=
    ∫ x, F.restricted v y x * f x

def Lines : Prop := ∀ n (v : Fin n → V) (f : Joint n) (y a : Heights n) (i : ℝ), y+i • a∈east n →
    HasDerivAt (fun t : ℝ => F.psi v (y+t • a) f) (F.psi v (y+i • a) (Waves.clock a f)) i

def Bounds : Prop := ∀ n (v : Fin n → V) (y : Heights n) (hy : y∈east n) (f : Joint n),
    Integrable (fun x => F.restricted v y x * f x)

def Along : Prop := ∀ n (v : Fin n → V) f, ContinuousOn (fun y => F.psi v y f) (east n)

variable {v : Fin n → V}
lemma beam (m : ℕ) (C : ℝ) (p : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x,
    ‖F.restricted v y x‖ ≤ C*k⁻¹^m) {y : Heights n} (h : y∈sunrise n) (f : Joint n) {k : ℝ} (hh : k ∈ Ioc 0 1) :
    k^m*‖F.psi v (y+k • rate n) f‖ ≤ C * weight f := by
  have he := hh.1
  refine (mul_le_mul_of_nonneg_left (compromise f _ _ (p _ _ hh (begins h _ hh.1.le))) (pow_nonneg he.le m)).trans_eq ?_
  rw [← mul_assoc, mul_left_comm, ← mul_pow,mul_inv_cancel₀ he.ne',one_pow,mul_one]
end InkWaves

namespace InkWaves
/-- eq:oscfft on compact tests only. -/
def during (F : InkWaves V) (W : WView V) := ∀ (n : ℕ) (v : Fin n → V) (y : Heights n), y∈east n→ ∀ f : Joint n, ∀ h : HasCompactSupport ⇑f,
    Distn.fourier (W.W n v) f=F.psi v y (Probe.hat (lifts (dawn y) f h))
end InkWaves
namespace WView

def cone_tests (W : WView V) := ∀ n (v : Fin n → V), dsupport (Distn.fourier (W.W n v)) ⊆ half n

end WView
end YM.SatinWFixed
