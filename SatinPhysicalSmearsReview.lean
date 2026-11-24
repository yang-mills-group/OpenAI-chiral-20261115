import SatinFrontValueReview
import SatinThinSweep
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six

/-- Actual readings and the product of the same character's pure marginals.
Widths shrink along (c,r), while quadrature may follow any cofinal finer grid. -/
def ThinFrontReadings (P : Spine) (x : P.Spectrum0 3) (c r : ℕ → ℕ)
    (F G : SampleDose) : Prop := ∀ (Z W : Lead.Clan) (t : ℕ → ℕ),
  Tendsto t atTop atTop → (∀ i, c i ≤ t i) →
  let U := fun i => P.thinIncoming Z (c i) (r i) (t i) F
  let V := fun i => P.thinOutgoing W (c i) (r i) (t i) G
  (purePrice Z : ℂ) * (purePrice W : ℂ) ≠ 0 ∧
  Tendsto (fun i => P.singleState 3 (t i) x (U i * V i)) atTop
    (𝓝 ((purePrice Z : ℂ) * (purePrice W : ℂ))) ∧
  Tendsto (fun i => P.singleState 3 (t i) x (U i)) atTop (𝓝 (purePrice Z : ℂ)) ∧
  Tendsto (fun i => P.singleState 3 (t i) x (V i)) atTop (𝓝 (purePrice W : ℂ)) ∧
  ∀ᶠ i : ℕ in atTop, ∀ X : P.Test →ₗ[ℂ] ℂ, P.SameRawProduct (t i) x X →
    X (U i) = 0 ∧ X (V i) = 0 ∧ X (U i * V i) = 0

theorem reviewThinSmears {P : Spine} {x : P.Spectrum0 3} {c r : ℕ → ℕ}
    {K : P.Register} {J : P.Ellis 3 x} (B : Experiment P K c r x J) (T : P.Transmission x c r) (grow : ∀ i, i ≤ r i)
    (F G : SampleDose) (hF : F.Normalized) (hG : G.Normalized)
    (neg : thinNegative F 1) (pos : thinPositive G 1) : P.ThinFrontReadings x c r F G := by
  intro Z W t ht fine
  let A := fun i => P.thinString Z (c i) (r i)
  let D := fun i => P.thinString W (c i) (r i)
  let a := fun i => P.thinString_birth Z (c i) (r i)
  let d := fun i => P.thinString_birth W (c i) (r i)
  let ω := P.colorZero 3 (P.advocate 3 x 3)
  have exposure := thin_compare_dew B (a := (1 : ℝ≥0)) (by norm_num)
    (t := fun _ => 1) (Eventually.of_forall fun _ => le_rfl)
  have eu := thin_grid_ket_tendsto (flipDose F 3) (thin_flip_positive F 1 neg)
    (purePrice Z : ℂ) A a (thin_front_shard_tendsto Z B (fun _ => 1) exposure) t ht
  have ev := thin_grid_ket_tendsto G pos (purePrice W : ℂ) D d
    (thin_front_shard_tendsto W B (fun _ => 1) exposure) t ht
  have hu : Tendsto (fun i => P.thinGridKet x (t i) (A i) (a i) (flipDose F 3)) atTop
      (𝓝 ((purePrice Z : ℂ) • ω)) := by simpa [thin_flip_mass, hF.2, ω] using eu
  have hv : Tendsto (fun i => P.thinGridKet x (t i) (D i) (d i) G) atTop
      (𝓝 ((purePrice W : ℂ) • ω)) := by simpa [hG.2, ω] using ev
  have walls : ∀ᶠ i : ℕ in atTop, P.WallBefore (A i) F 0 ∧ P.WallAfter (D i) G 0 := by
    filter_upwards [(T.widths 3).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with i hi
    constructor
    · intro p h
      change p (3 : Axis) + P.probeWidth (c i) (r i) 3 < 0
      have q := neg p h
      norm_num at q
      linarith only [q, hi]
    · intro p h
      change 0 + P.probeWidth (c i) (r i) 3 < p (3 : Axis)
      have q := pos p h
      norm_num at q
      linarith only [q, hi]
  have const : Tendsto (fun _ : ℕ => ω) atTop (𝓝 ω) := tendsto_const_nhds
  refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.mpr (purePrice_p Z).ne')
    (Complex.ofReal_ne_zero.mpr (purePrice_p W).ne'), ?_, ?_, ?_, ?_⟩
  · have pair := (hu.inner (𝕜 := ℂ) hv).congr' (walls.mono fun i hw =>
      (P.thin_pair_grid x (t i) (A i) (a i) F (D i) (d i) G hw.1 hw.2 (fine i) (fine i)).symm)
    simpa [thinIncoming, thinOutgoing, A, D, ω, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, P.norms_color, mul_comm] using pair
  · have early := ((const.inner (𝕜 := ℂ) hu).star).congr' (walls.mono fun i hw =>
      (P.thin_early_single_grid x (t i) (A i) (a i) F hw.1 (fine i)).symm)
    simpa [thinIncoming, A, ω, inner_smul_right, inner_self_eq_norm_sq_to_K, P.norms_color] using early
  · have late := (const.inner (𝕜 := ℂ) hv).congr' (walls.mono fun i hw =>
      (P.thin_late_single_grid x (t i) (D i) (d i) G hw.2 (fine i)).symm)
    simpa [thinOutgoing, D, ω, inner_smul_right, inner_self_eq_norm_sq_to_K, P.norms_color] using late
  · filter_upwards [walls, eventually_ge_atTop (P.calibration.ℓ + 1)] with i hw hi
    have nr : P.calibration.ℓ < r i := lt_of_lt_of_le (by omega) (grow i)
    have earlier : P.WallBefore ((A i).kiss P 3) F 0 := by
      intro p hp
      change p (3 : Axis) + P.probeWidth (c i) (r i) 3 < 0
      exact hw.1 p hp
    intro X hX
    exact P.thin_factor_pays Z W (c i) (r i) (t i) F G (c i) (r i) (fine i) (fine i) nr nr
      (P.test_apart ((A i).kiss P 3) F 0 (D i) G earlier hw.2) X hX.marginal.factors (Or.inl hX.matter)

/-- Unconditional same-election application. The two fixed external smears also
realize the previously checked full-rank measurement at its original width. -/
theorem reviewElectedThinSmears :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (i : ℕ) (a : ℝ) (F G : SampleDose),
      F.Normalized ∧ G.Normalized ∧ tsupport F.val ⊆ reviewEarlierBox.invites ∧
      tsupport G.val ⊆ reviewLaterBox.invites ∧ P.ReturnsSix x (c i) (r i) a F G ∧
      P.FixedSatinReadings K x (c i) (r i) a F G ∧
      (∀ ε > 0, ∀ᶠ j : ℕ in atTop, ∀ Z : Lead.Clan,
        P.ThinIntrinsic (P.thinString Z (c j) (r j)) ε ∧
        P.ThinIntrinsic ((P.thinString Z (c j) (r j)).kiss P 3) ε) ∧
      P.ThinFrontReadings x c r F G := by
  let request : Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
  obtain ⟨P, K, _uniform, c, r, x, hr, _J, B, T⟩ := macroscopicSatin request 1 1 (by norm_num) id
  let order : Orders := ⟨fun _ => true, rfl⟩
  have sep : reviewEarlierBox.Later reviewLaterBox order 0 := by
    intro j
    norm_num [Doorway.Later, reviewEarlierBox, reviewLaterBox, order]
  let b : Fin 3 → Bool := fun _ => false
  obtain ⟨p, e, _he, _inside, cost⟩ := authorize b
  obtain ⟨i, hi⟩ :=
    (packs_within_rectangles T (Metric.ball p e) b cost reviewEarlierBox reviewLaterBox order sep).exists
  obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2
  have neg : thinNegative F 1 := by
    intro z hz
    exact ((hU hz) 3 (Set.mem_univ _)).2.le
  have pos : thinPositive G 1 := by
    intro z hz
    exact ((hV hz) 3 (Set.mem_univ _)).1.le
  exact ⟨P, K, c, r, x, i, a, F, G, hF, hG, hU, hV, hR,
    P.reviewWardContrast K x _ _ a F G hR, thin_widths T,
    reviewThinSmears B T hr F G hF hG neg pos⟩

#print axioms reviewThinSmears
#print axioms reviewElectedThinSmears
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
