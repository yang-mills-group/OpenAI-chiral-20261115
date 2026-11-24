import YM.SU5.MacroSix.MixedUV
import YM.SU5.Cheer.Verse

/-!
# Centered *mixed* estimate on the selected continuous-translation sector

Extends `Cordial/Horizon` and `Cheer/{Verse,Chapel}` to cross-pairings, using
`penetrationCross`. In particular handles *moving* zoomed positions/gaps
(limits specified in rescaled coordinates). The projection and all rounding
and transport estimates are on the same elected Spine.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
variable (P : Spine) (x : P.Spectrum0 3) (Z W : Lead.Clan) (c r : ℕ → ℕ)
local notation "M" => timeMesh P.par
local notation "β" => P.otherSpectrum 3 3 x
local notation "V" => P.ColorHil 3 (β)
local notation "S'" => P.physicalEnergy 3 (β)
local notation "G" => P.ManyF 3 (β)
local notation "ψ" => P.voyageF 3 (β)
local notation "S" => P.seasons 3 (β)
local notation "π" => P.wealth 3 (β)
local notation "Φ" i:max => P.shard x Z (c i) (r i)
local notation "Φ'" i:max => P.shard x W (c i) (r i)
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "φ" i:max => P.lucid x Z (c i) (r i)
local notation "φ'" i:max => P.lucid x W (c i) (r i)
local notation "η" i:max => P.birthCloud x Z (c i) (r i)
local notation "η'" i:max => P.birthCloud x W (c i) (r i)
local notation "ξ" i:max => P.allowance x Z (c i) (r i)
local notation "ξ'" i:max => P.allowance x W (c i) (r i)
local notation "Δ" => ((purePrice Z:ℂ)*(purePrice W:ℂ))

-- From Horizon.
private lemma manyF_payment (X Y : V) : inner ℂ ((π) X) ((π) Y) =
    inner ℂ (P.visitors 3 (β) X) Y := by
  let g := P.visitors 3 (β); change inner ℂ (g X) (g Y) = _
  have hc : g.adjoint = g := Alliance.symmetricstack ..
  have he : g (g X) = g X := Alliance.grounded _ _ ((ψ).planted (look 3) X)
  exact (ContinuousLinearMap.adjoint_inner_left g Y (g X)).symm.trans
    (congrArg (inner ℂ · Y) ((DFunLike.congr_fun hc _).trans he))

variable {P x c r} (A : Launch P c r) {d : ℕ → ℝ}
  (Y : readyUV P c r x d) (p : Tendsto d atTop (𝓝 0))
include A Y p

lemma shardLimited : Limited V (fun i ↦ Φ i) :=
  OS.Semigroup.Balloon.hasLimit (H:=V) (horn_norm Z A Y p)

lemma lucidLimited : Limited G (fun i ↦ φ i) :=
  OS.Semigroup.Balloon.hasLimit (H:=G) (eyes_norm Z A Y p)

private lemma highBeamCross (hn : Z ≠ W) (v : Bank) {z : ℝ} (q : 0 ≤ z) (D : ℕ → ℕ)
    (w : P.bargain r (fun i ↦ (D i:ℤ)) z) :
    let T i := whenly M (c i) (D i)
    Tendsto (fun i ↦ inner ℂ (φ i)
      ((S).U (P.horizon c r v i) ((S).E (T i) (φ' i)))) atTop (𝓝 (Δ)) := by
  let g (i : Street) := v.val i.val
  let f (i : Street) (n : ℕ) := P.pan r v n i
  let X (i) := P.pit c r v i
  let SP := S
  let J := look (3:Axis)
  intro T
  have h : ∀ i : Street, P.bargain r (f i) (g i) := fun i ↦ P.intendR r (g i) A.eager
  let qX (i : ℕ) := (ψ).raw J (X i) ((S').E (T i) (Φ' i))
  have he : Tendsto (fun i ↦ inner ℂ (Φ i) (qX i)) atTop (𝓝 (Δ)) :=
    penetrationCross Z W A Y p hn J D z q (fun i n ↦ f i n) g (fun i _ ↦ h i) w
  let K (i : ℕ) := φ i
  have hh (i : ℕ) : SP.U (P.horizon c r v i) (SP.E (T i) (φ' i)) = (π) (qX i) :=
    (congrArg (SP.U (P.horizon c r v i) : (P.ManyF 3 (β)).space → _)
      (P.bankHeat 3 (β) (T i) (Φ' i)).symm).trans
        (P.roll_motion 3 (β) (X i) ((S').E (T i) (Φ' i)))
  have hp : Limited V qX := le_seam (fun i ↦ Φ' i) (shardLimited W A Y p)
    fun i ↦ ((ψ).raw_isometry J (X i) ((S').E (T i) (Φ' i))).le.trans
      (heatedLim (S') (T i) (Φ' i))
  have hv : Tendsto (fun i ↦ inner ℂ (P.visitors 3 (β) (Φ i)) (qX i) -
      inner ℂ (Φ i) (qX i)) atTop (𝓝 0) :=
    (aura' V qX _ hp (whole_sky Z A Y p)).congr fun i ↦
      inner_sub_left (𝕜:=ℂ) (P.visitors 3 (β) (Φ i)) (Φ i) (qX i)
  exact (unifier hv he).congr fun i ↦ ((congrArg (inner ℂ (K i)) (hh i)).trans
    (P.manyF_payment x (Φ i) (qX i))).symm

private lemma raysCross (hn : Z ≠ W) (v : Bank) {z : ℝ} (q : 0 ≤ z) (D : ℕ → ℕ)
    (w : P.bargain r (fun i ↦ (D i:ℤ)) z) (F : ℕ → Bank)
    (h : Tendsto (fun i ↦ (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i ↦ inner ℂ (φ i) ((S).U (F i) ((S).E (whenly M (c i) (D i)) (φ' i))))
      atTop (𝓝 (Δ)) := by
  let t (i) := whenly M (c i) (D i)
  let x' (i : ℕ) := φ' i
  let S₁ := S
  let g := P.horizon c r v
  let E i := S₁.E (t i) (x' i)
  have hv : Tendsto (fun i ↦ S₁.U (F i) (x' i) - S₁.U (g i) (x' i)) atTop (𝓝 0) :=
    neighbor W A Y p v (P.pan r v) F (fun i ↦ P.intendR r (reveal i v) A.eager) h
  have hw : Tendsto (fun i ↦ inner ℂ (φ i) (S₁.U (F i) (E i)) -
      inner ℂ (φ i) (S₁.U (g i) (E i))) atTop (𝓝 0) :=
    (aura G _ _ (lucidLimited Z A Y p) (realize_shim (S) x' t F g hv)).congr
      fun i ↦ inner_sub_right (𝕜:=ℂ) (φ i) (S₁.U (F i) (E i)) (S₁.U (g i) (E i))
  exact unifier hw (highBeamCross Z W A Y p hn v q D w)

omit A Y p in
private lemma heatZero (G' : Hilbert) {j : Axis} (T : OS.Semigroup G' j)
    (E : ℕ → ℝ≥0) (u : ℕ → G') (p : ℝ)
    (hx : Tendsto (fun i ↦ ‖u i‖^2) atTop (𝓝 p))
    (ht : Tendsto (fun i ↦ (inner ℂ (u i) (T.E (E i) (u i))).re) atTop (𝓝 p)) :
    Tendsto (fun i ↦ T.E (E i) (u i) - u i) atTop (𝓝 0) := by
  let D i := T.E (E i) (u i)
  have hk : Tendsto (fun i ↦ ‖D i - u i‖^2) atTop (𝓝 0) := by
    have he := (hx.sub ht).const_mul 2; rw [sub_self, mul_zero] at he
    exact squeeze_zero (fun i ↦ sq_nonneg _) (fun i ↦ capture T (E i) (E i) (u i) le_rfl) he
  have hp := Real.continuous_sqrt.continuousAt.tendsto.comp hk
  rw [Real.sqrt_zero] at hp
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (hp.congr fun i ↦
    Real.sqrt_sq (norm_nonneg (D i - u i)))

private lemma heatInitial (E : ℕ → ℝ≥0) (h : P.dimensionS c r E 0) :
    Tendsto (fun i ↦ (S).E (E i) (φ i) - (φ i)) atTop (𝓝 0) := by
  let u (i : ℕ) := φ i
  let D i := (S).E (E i) (u i)
  have ht : Tendsto (fun i ↦ (inner ℂ (u i) (D i)).re) atTop (𝓝 (ovoid Z 0 0).re) := by
    have he := EuclidAll Z A Y p 0 0 le_rfl E h (fun _ ↦ 0) (by simp)
    apply Complex.continuous_re.continuousAt.tendsto.comp (?_ : Tendsto (fun i ↦
      inner ℂ (u i) (D i)) atTop (𝓝 (ovoid Z 0 0)))
    exact he.congr fun i ↦ congrArg (inner ℂ (u i))
      (show (S).U 0 (D i) = D i from DFunLike.congr_fun (S).uZero _)
  have hx := eyes_norm Z A Y p
  exact heatZero G S E u _ hx ht

private lemma compareBeam (z : ℝ) (q : 0 ≤ z) (E L : ℕ → ℝ≥0)
    (w : P.dimensionS c r E z) (v : P.dimensionS c r L z) :
    Tendsto (fun i ↦ (S).E (E i) (φ i) - (S).E (L i) (φ i)) atTop (𝓝 0) := by
  by_cases e : z = 0
  · have he := (heatInitial Z A Y p E (Eq.mp (congrArg (P.dimensionS c r E) e) w)).sub
      (heatInitial Z A Y p L (Eq.mp (congrArg (P.dimensionS c r L) e) v))
    simp only [sub_zero] at he
    exact he.congr fun i ↦ sub_sub_sub_cancel_right ((S).E (E i) (φ i)) ((S).E (L i) (φ i)) (φ i)
  exact uniform_zoom (S) (fun i ↦ φ i) (fun i ↦ P.dew_pos _ (A.unitSize i))
    w v (lt_of_le_of_ne q (Ne.symm e)) (lucidLimited Z A Y p)

/-- Off-diagonal analogue of `EuclidAll`: arbitrary approximants in space and positive
(time ≥ 0) heat with the specified scaled limits. -/
theorem euclidCross (hn : Z ≠ W) (v : Bank) (z : ℝ) (q : 0 ≤ z) (E : ℕ → ℝ≥0)
    (w : P.dimensionS c r E z) (F : ℕ → Bank)
    (h : Tendsto (fun i ↦ (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i ↦ inner ℂ (φ i) ((S).U (F i) ((S).E (E i) (φ' i)))) atTop (𝓝 (Δ)) := by
  let D := (grantR A z q).choose
  have hp := (grantR A z q).choose_spec
  let L i := whenly M (c i) (D i)
  let X (i : ℕ) := (S).E (E i) (φ' i)
  let Y' (i : ℕ) := (S).E (L i) (φ' i)
  let U i := (S).U (F i)
  have ht : Tendsto (fun i ↦ U i (X i) - U i (Y' i)) atTop (𝓝 0) :=
    (soarE (S) F _ (compareBeam W A Y p z q E L w hp.2)).congr fun i ↦
      map_sub (U i) (X i) (Y' i)
  have hk : Tendsto (fun i ↦ inner ℂ (φ i) (U i (X i)) -
      inner ℂ (φ i) (U i (Y' i))) atTop (𝓝 0) :=
    (aura G _ _ (lucidLimited Z A Y p) ht).congr fun i ↦
      inner_sub_right (𝕜:=ℂ) (φ i) (U i (X i)) (U i (Y' i))
  exact unifier hk (raysCross Z W A Y p hn v q D hp.1 F h)

omit A Y p in
private lemma centered_mix_eq (G' : Hilbert) {j : Axis} (T : OS.Semigroup G' j)
    (Ω U V' W W' : G') (a : OS.Cross j) (c d : ℂ) (t : ℝ≥0)
    (h : W = U + c • Ω) (h' : W' = V' + d • Ω)
    (hU : inner ℂ Ω U = 0) (hV : inner ℂ Ω V' = 0)
    (hy : ‖Ω‖=1) (hp : T.U a Ω=Ω) (hu : T.E t Ω=Ω) :
    inner ℂ U (T.U a (T.E t V')) = inner ℂ W (T.U a (T.E t W')) - star c * d := by
  have hv : inner ℂ Ω (T.U a (T.E t V')) = 0 := by
    nth_rw 1 [← hp]; rw [minted,← T.swing, hu, hV]
  have hUV : inner ℂ U Ω = 0 := by rw [← inner_conj_symm (𝕜:=ℂ) U Ω, hU]; simp
  rw [h,h',map_add,map_add,map_smul,map_smul,hu,hp]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,hUV,hv,
    inner_self_eq_norm_sq_to_K]
  simp [hy]
  ring

variable (u : P.lodestarHere 3 (P.otherSpectrum 3 3 x))
include u

omit A Y p in
lemma centered_lucid_mix (s n : ℕ) (a : Bank) (t : ℝ≥0) :
    inner ℂ (P.birthCloud x Z s n) ((S).U a ((S).E t (P.birthCloud x W s n))) =
      inner ℂ (P.lucid x Z s n) ((S).U a ((S).E t (P.lucid x W s n))) -
        star (P.allowance x Z s n) * (P.allowance x W s n) := by
  let Ω := P.heaven 3 β
  have he : (S).E t Ω=Ω := by
    apply (heat_iff_edge (3:Axis) S _).mpr _ t
    exact ((P.heavenRank 3 β u _).1 (Submodule.subset_span (Set.mem_singleton _))).1
  exact centered_mix_eq G S Ω _ _ _ _ a _ _ t (P.halo_split ..) (P.halo_split ..)
    (P.halo_zero ..) (P.halo_zero ..) (P.stone_norm ..) (P.stone_warm 3 β u a) he

omit u A Y p in
private lemma tendstoRewrite (g : Lead.Clan → ℕ → ℂ) (Z W : Lead.Clan) (a b : ℂ) (e : Z=W)
    (q : b=a) (h : Tendsto (g Z) atTop (𝓝 a)) : Tendsto (g W) atTop (𝓝 b) := by
  rwa [← e, q]

omit u A Y p in
private lemma tendstoSubtract (g h f : ℕ → ℂ) (K c : ℂ) (t : Tendsto g atTop (𝓝 (K+c)))
    (w : Tendsto h atTop (𝓝 c)) (v : ∀ i, g i - h i = f i) : Tendsto f atTop (𝓝 K) := by
  have he := t.sub w; rw [add_sub_cancel_right] at he; exact he.congr v

/-- Matrix kernel convergence after centering, in the rescaled variables. -/
theorem centeredMatrixZoom (v : Bank) (z : ℝ) (q : 0 ≤ z) (E : ℕ → ℝ≥0)
    (w : P.dimensionS c r E z) (F : ℕ → Bank)
    (h : Tendsto (fun i ↦ (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i ↦ inner ℂ (η i) ((S).U (F i) ((S).E (E i) (η' i)))) atTop
      (𝓝 (if Z = W then ovoid Z z v - (purePrice Z:ℂ)^2 else 0)) := by
  -- First specify the uncentered family abstractly to keep the Hilbert implementation sealed.
  let g (W : Lead.Clan) (i : ℕ) := inner ℂ (φ i) ((S).U (F i)
    ((S).E (E i) (P.lucid x W (c i) (r i))))
  let a : ℂ := purePrice Z
  let b : ℂ := purePrice W
  let K : ℂ := if Z = W then ovoid Z z v - a^2 else 0
  have hl : Tendsto (g W) atTop (𝓝 (K + star a * b)) := by
    by_cases e : Z = W
    · have hK : K + star a * b = ovoid Z z v := by simp [K,a,b,← e,pow_two]
      exact tendstoRewrite g Z W (ovoid Z z v) (K+star a*b) e hK
        (EuclidAll Z A Y p v z q E w F h)
    have hk : K + star a * b = a*b := by simp [K,e,a]
    -- avoid matching in Hilbert expression
    rw [hk]; exact euclidCross Z W A Y p e v z q E w F h
  let f (i : ℕ) := inner ℂ (η i) ((S).U (F i) ((S).E (E i) (η' i)))
  have he (i : ℕ) : g W i - star (ξ i) * (ξ' i) = f i :=
    (centered_lucid_mix Z W u (c i) (r i) (F i) (E i)).symm
  exact tendstoSubtract (g W) (fun i ↦ star (ξ i) * (ξ' i)) f K (star a * b) hl
    ((refreshing Z A Y p).star.mul (refreshing W A Y p)) he

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.centeredMatrixZoom
