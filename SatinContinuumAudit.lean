import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Criteria used in the audit of the two written constructions. -/
namespace SatinContinuumAudit

open Filter
open scoped Topology InnerProductSpace

/-- The finite-batch estimate yields the same terminal limit along any choice of
    volume in each batch. The hypothesis is uniform only on the designated sets. -/
theorem terminal_of_uniform_on_batches {V : Type*}
    (batch : ℕ → Set V) (terminal : ℕ → V → ℝ) (pivot : ℝ)
    (uniform : ∀ ε > 0, ∀ᶠ k in atTop, ∀ t ∈ batch k, dist (terminal k t) pivot < ε)
    (pick : ℕ → V) (belongs : ∀ᶠ k in atTop, pick k ∈ batch k) :
    Tendsto (fun k => terminal k (pick k)) atTop (𝓝 pivot) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [uniform ε hε, belongs] with k hk hmem
  exact hk (pick k) hmem

/-- Exact error between two marked readings with their own signed (complex)
    partition functions. The variation of a bare parameter by itself does not
    control the cross-product on the right. -/
theorem signed_reading_distance (N Z N' Z' : ℂ) (hz : Z ≠ 0) (hz' : Z' ≠ 0) :
    ‖N / Z - N' / Z'‖ = ‖N * Z' - N' * Z‖ / (‖Z‖ * ‖Z'‖) := by
  rw [div_sub_div _ _ hz hz', norm_div, norm_mul, mul_comm Z N']

/-- Intertwining the elected vacuum and the three vectors needed by its two
    one-point functions and one ordered joint correlator preserves the complex
    connected reading exactly, with the original probe orientations. -/
theorem connected_preserved
    {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (incl : H →ₗᵢ[ℂ] H') (ω : H) (ω' : H')
    (a b ab : H) (a' b' ab' : H')
    (vacuum : incl ω = ω') (first : incl a = a')
    (second : incl b = b') (both : incl ab = ab') :
    inner ℂ ω' ab' - inner ℂ ω' a' * inner ℂ ω' b' =
      inner ℂ ω ab - inner ℂ ω a * inner ℂ ω b := by
  rw [← vacuum, ← first, ← second, ← both]
  simp only [LinearIsometry.inner_map_map]

/-- The transfer preserves a genuine nonproduct reading even when its sign is
    unknown. To use this on a specific reconstruction one must supply this
    very vacuum, orientation and ordered two-field vector. -/
theorem nonproduct_preserved
    {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (incl : H →ₗᵢ[ℂ] H') (ω : H) (ω' : H')
    (a b ab : H) (a' b' ab' : H')
    (vacuum : incl ω = ω') (first : incl a = a')
    (second : incl b = b') (both : incl ab = ab')
    (contrast : inner ℂ ω ab ≠ inner ℂ ω a * inner ℂ ω b) :
    inner ℂ ω' ab' ≠ inner ℂ ω' a' * inner ℂ ω' b' := by
  apply sub_ne_zero.mp
  rw [connected_preserved incl ω ω' a b ab a' b' ab' vacuum first second both]
  exact sub_ne_zero.mpr contrast

end SatinContinuumAudit
