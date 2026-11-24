import SatinStress.U2.Fit
/-!
# Converging frames for the subspaces (U3, U4)

Extract a limit basis of subspaces of fixed dimension. Present the linear
maps and convergence, no abstract topology assumption on any
`Grassmannian` nor requiring the bases chosen by the given preparations already converge.
-/
namespace SatinStress.U2.Coord
open Filter Function Set Metric
open scoped Topology
open Module (finrank)
variable {S T I : Type*} {L : Filter I}

section IPS
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]

omit [FiniteDimensional ℝ T] in
private lemma unit_choice (p : S →ₗ[ℝ] T) (h : Injective p) : ∃ A : S ≃ₗ[ℝ] S,
    ∀ x, ‖p (A x)‖ = ‖x‖ := by
  let ei := finCongr (LinearMap.finrank_range_of_inj h)
  let v := (stdOrthonormalBasis ℝ S).equiv ((stdOrthonormalBasis ℝ p.range).reindex ei) (Equiv.refl _)
  let X := LinearEquiv.ofInjective p h
  exact ⟨v.toLinearEquiv.trans X.symm,fun x => (show ‖X (X.symm (v x))‖=‖x‖ by rw [X.apply_symm_apply,v.norm_map])⟩

private lemma clipped_norm (p : ℕ → S →ₗ[ℝ] T) (h : ∀ j, Injective (p j)) :
    ∃ c : ℕ → ℕ, StrictMono c ∧ ∃ g : ℕ → S ≃ₗ[ℝ] S,
      ∃ A : S →L[ℝ] T, Injective A ∧ ∀ x, Tendsto (fun j => p (c j) (g j x)) atTop (𝓝 (A x)) := by
  choose G hG using fun j => unit_choice (p j) (h j)
  let f (j) := LinearMap.toContinuousLinearMap ((p j).comp (G j).toLinearMap)
  have hu : ∀ j, f j ∈ closedBall 0 1 := fun j => by
    rw [mem_closedBall,dist_zero_right]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      rw [one_mul]; exact (hG _ _).le)
  obtain ⟨D, -, c, hM, hD⟩ := (isCompact_closedBall ..).tendsto_subseq hu
  have hd (x : S) : Tendsto (fun j => (p (c j) (G (c j) x))) atTop (𝓝 (D x)) := joint hD tendsto_const_nhds
  refine ⟨c,hM,(fun i=>G (c i)),D,?_,hd⟩
  have hN (x : S) : ‖D x‖=‖x‖ := tendsto_nhds_unique_of_eventuallyEq (hd x).norm tendsto_const_nhds (Eventually.of_forall fun j => hG (c j) x)
  intro x y hxy; apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← hN, map_sub,hxy,sub_self,norm_zero]
end IPS
variable [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
  [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T]

theorem clipped (p : ℕ → S →ₗ[ℝ] T) (h : ∀ j, Injective (p j)) :
    ∃ c : ℕ → ℕ, StrictMono c ∧ ∃ g : ℕ → S ≃ₗ[ℝ] S,
      ∃ A : S →ₗ[ℝ] T, Injective A ∧ Entries atTop (fun j => p (c j) ∘ₗ (g j).toLinearMap) A := by
  letI := norms S; letI := inner S
  letI := norms T; letI := inner T
  obtain ⟨c,hc,g,A,hi,he⟩ := clipped_norm p h
  exact ⟨c,hc,g,A.toLinearMap,hi,fun x => iff_norm.mpr (he x)⟩

-- limits characterized without prior convergence of domain values
lemma remains [L.NeBot] {f : I → S →ₗ[ℝ] T} {F : S →ₗ[ℝ] T}
    (p : Entries L f F) (h : Injective F) {y : I → T} {x : T}
    (a : Tends L y x) (g : ∀ᶠ i in L, y i ∈ (f i).range) : x ∈ F.range := by
  classical
  let u (i) : S := if e : ∃ s, f i s = y i then e.choose else 0
  have t : Tends L (fun i => f i (u i)) x := a.congr' (by
    filter_upwards [g] with i hi; exact (show f i (u i)=y i by
      unfold u; rw [dif_pos (show ∃ s, f i s=y i from hi)]; exact Exists.choose_spec (show ∃ s, f i s = y i from hi)).symm)
  obtain ⟨s,_,e⟩ := recover_exists p t h; exact ⟨s,e⟩
end SatinStress.U2.Coord
