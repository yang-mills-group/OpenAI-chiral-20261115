import SU5ExactJointTarget
import SU5RelativisticProof
import GaugeFieldConstruction.SeasonReport
import SU5ExactRunningProof

set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxSize 28000
set_option maxRecDepth 12000

open YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ContinuumConstruction

/-- The three coefficient limits and the spacelike connected correlation hold
on the common history and reconstructed vacuum. -/
theorem ChiralSU5.exists_interacting_three_generation_theory_with_exact_running :
    ChiralSU5.InteractingThreeGenerationTheoryWithExactRunning := by
  intro b
  obtain ⟨n, y, above, prod, growth, roles, axes, comp, appr, stress, a, _, cost,
    c, collars, layers, resp, cont, model, screens, cert, τ, ε, β, calendar, findings⟩ :=
    GaugeLimitJoint.common_witness_season_st b 0 1 (by norm_num)
  have one := findings.chapter.legacy_statement
  obtain ⟨r, prescription, follow⟩ := findings.follow
  refine ⟨n, y, above, prod, growth, roles, axes, comp, appr, stress, a, cost,
    c, collars, layers, resp, cont, model, screens, cert, one,
    relativisticClauses_of_oneTheory cert one, findings.chapter.handed_prices,
    ChiralSU5.exactUltravioletRunning y.P, τ, ε, β, calendar, findings.months, findings.large_volume,
    findings.before, r, prescription, ?_⟩
  apply follow.mono
  intro k hk
  obtain ⟨t, X, F, W, u, PCI, Ψ, mixed⟩ := hk
  have price := mixed.at_player.realSt
  exact ⟨t, X, F, W, u, PCI, Ψ, mixed, (price.not_empty _ (Or.inl rfl)).2.1,
    (price.not_empty _ (Or.inr rfl)).2.1, fun x hx z hz => (price.region.2 x hx z hz).2.2,
    price.right_eq.1.trans price.right_eq.2, price.tape⟩
