import YM.SU5.Six.CrossHorizon

/-!
# Towards the matrix zoom: narrowed pair *positive* measures

We work through heat & space Euclidean cross prices, not complex-measure
weak convergence as an input. Use complex polarization but take narrow
limits of genuine finite **positive** measures, via `YM.Cheer.Lyrical`.
Cf `Cheer/{Pavilion,Chapel,Verse}.lean` (including for extracting the
vacuum component) for the diagonal/one-vector arguments.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section

namespace YM.Cheer
open MeasureTheory Filter Complex
open scoped InnerProductSpace Topology

variable {μ ν : Narrow}
lemma Brilliant.add (h : Brilliant μ) (k : Brilliant ν) : Brilliant (μ+ν) :=
  ae_add_measure_iff.mpr ⟨h,k⟩

lemma FLap_add (h : Brilliant μ) (k : Brilliant ν) (v : Space3) (u : ℂ) (e : 0 ≤ u.re) :
    FLap (μ+ν) v u = FLap μ v u + FLap ν v u :=
  integral_add_measure (destined μ _ _ h e) (destined ν _ _ k e)

-- Abstract inner-product expansion for the sums of vectors
lemma inner_augment {H : Hilbert} (T : H.Op) (x y : H) (a : ℂ) (ha : ‖a‖=1) :
    inner ℂ (x+a•y) (T (x+a•y)) =
    inner ℂ x (T x) + inner ℂ y (T y) +
      a * inner ℂ x (T y) + star a * inner ℂ y (T x) := by
  rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      inner_smul_right, inner_smul_left, inner_smul_left, inner_smul_right]
  have hz : a * star a = 1 := by
    rw [star_def, mul_conj, normSq_eq_norm_sq, ha, one_pow, ofReal_one]
  change _ + _ + (star a * _ + star a * (a * inner ℂ y (T y))) = _
  linear_combination (inner ℂ y (T y)) * hz

end YM.Cheer
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine
open OS.Semigroup.Balloon Cheer

/-- Generalization to mixed vectors of the `allowance_sub` step of Cheer/Chapel.lean. -/
lemma split_inner_vac {H : Hilbert} {j : Axis} (G' : OS.Semigroup H j)
    (x y Ω x' y' : H) (v : OS.Cross j) (t : ℝ≥0) (a b : ℂ)
    (hx : x' = x + a • Ω) (hy : y' = y + b • Ω)
    (hz : inner ℂ Ω x = 0) (hz' : inner ℂ Ω y = 0)
    (hs : ‖Ω‖ = 1) (hp : G'.U v Ω = Ω) (hu : G'.E t Ω = Ω) :
    inner ℂ x (G'.U v (G'.E t y)) =
    inner ℂ x' (G'.U v (G'.E t y')) - star a * b := by
  have hv : inner ℂ Ω (G'.U v (G'.E t y)) = 0 := by
    nth_rw 1 [← hp]; rw [minted,← G'.swing,hu,hz']
  rw [hx,hy,map_add,map_add,map_smul,map_smul,hu,hp,inner_add_left,
      inner_add_right,inner_add_right,inner_smul_left (y:=G'.U v _),hv,
      inner_smul_right (x:=x),←inner_conj_symm (𝕜:=ℂ) x Ω,hz,
      inner_smul_left,inner_smul_right,inner_self_eq_norm_sq_to_K]
  simp [hs]

variable {P : Spine} {x : P.Spectrum0 3} {c r : ℕ → ℕ} (Z Z' : Lead.Clan)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "φ" X:max i:max => P.lucid x X (c i) (r i)
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "η" X:max i:max => P.birthCloud x X (c i) (r i)
local notation "z" X:max i:max => P.allowance x X (c i) (r i)
local notation "C" X:max => (purePrice X : ℂ)

lemma background_zeroed_any (s n : ℕ) (v : OS.Cross (3:Axis)) (t : ℝ≥0)
    (u : P.lodestarHere 3 ξ) :
    inner ℂ (P.birthCloud x Z s n) ((S).U v ((S).E t (P.birthCloud x Z' s n))) =
      inner ℂ (P.lucid x Z s n) ((S).U v ((S).E t (P.lucid x Z' s n))) -
        star (P.allowance x Z s n) * P.allowance x Z' s n := by
  have he : (S).E t Ω = Ω := by
    apply (heat_iff_edge (3:Axis) S _).mpr _ t
    exact ((P.heavenRank 3 ξ u _).1 (Submodule.subset_span (Set.mem_singleton _))).1
  exact split_inner_vac S _ _ Ω _ _ v t _ _ (P.halo_split ..) (P.halo_split ..)
    (P.halo_zero ..) (P.halo_zero ..) (P.stone_norm ..) (P.stone_warm 3 ξ u v) he

variable (A : Launch P c r) {q : ℕ → ℝ} (Y : readyUV P c r x q)
         (e : Tendsto q atTop (𝓝 0)) (u : P.lodestarHere 3 (P.otherSpectrum 3 3 x)) (hZZ : Z ≠ Z')

def dewN (i : ℕ) : ℝ≥0 := ⟨ρ i,(P.dew_pos _ (A.unitSize i)).le⟩

include A Y e u hZZ
-- generic helper
omit A Y e u hZZ in
private lemma cross_case {H : Hilbert} {j : Axis} (G' : OS.Semigroup H j)
    (L : ℂ) (b y : ℕ → H) (t : ℝ≥0) (F : ℕ → OS.Cross j) (T : ℕ → ℝ≥0)
    (hw : t = 0 → ∀ i, T i = 0)
    (hv : Tendsto (fun i : ℕ => inner ℂ (b i) (G'.U (F i) (y i))) atTop (𝓝 L))
    (he : (0 : ℝ) < (t:ℝ) → Tendsto (fun i : ℕ => inner ℂ (b i)
       (G'.U (F i) (G'.E (T i) (y i)))) atTop (𝓝 L)) :
    Tendsto (fun i : ℕ => inner ℂ (b i) (G'.U (F i) (G'.E (T i) (y i)))) atTop (𝓝 L) := by
  by_cases ht0 : t = 0
  · exact hv.congr fun i => by rw [hw ht0 i,G'.eZero]; rfl
  exact he (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0))

omit u in
lemma crossing_main (v : Bank) (t : ℝ≥0) :
    Tendsto (fun i : ℕ => inner ℂ (φ Z i) ((S).U ((ρ i) • v)
      ((S).E ((dewN A i)*t) (φ Z' i)))) atTop (𝓝 (C Z*C Z')) := by
  let T i := (dewN A i)*t; let F i := (ρ i) • v
  have hv : Tendsto (fun i => (ρ i)⁻¹ • F i) atTop (𝓝 v) :=
    tendsto_const_nhds.congr fun i => (inv_smul_smul₀ (P.dew_pos _ (A.unitSize i)).ne' v).symm
  have ht : P.dimensionS c r T (t:ℝ) := tendsto_const_nhds.congr fun i => by
    rw [show (T i:ℝ) = ρ i * (t:ℝ) from rfl]; rw [mul_comm (ρ i),mul_div_cancel_right₀ _ (P.dew_pos _ (A.unitSize i)).ne']
  have hx : Tendsto (fun i : ℕ => inner ℂ (φ Z i) ((S).U (F i) ((S).E (T i) (φ Z' i))))
      atTop (𝓝 (C Z*C Z')):=
    cross_case S (C Z*C Z') (fun i => φ Z i) (fun i => φ Z' i) t F T
      (fun h i => by unfold T; rw [h,mul_zero])
      (initialPoint_cross Z Z' A Y e hZZ v F hv)
      (fun h => evenlater_cross Z Z' A Y e hZZ v h T ht F hv)
  exact hx

omit A e Y u hZZ in
private lemma tenderSub (f g l : ℕ → ℂ) (s t : ℝ)
    (hf : Tendsto f atTop (𝓝 ((s:ℂ)*(t:ℂ))))
    (hg : Tendsto g atTop (𝓝 (s:ℂ)))
    (hl : Tendsto l atTop (𝓝 (t:ℂ))) :
    Tendsto (fun i => f i - star (g i) * l i) atTop (𝓝 0) := by
  have h := hf.sub (hg.star.mul hl)
  rw [Complex.star_def,Complex.conj_ofReal,sub_self] at h
  exact h

/-- Off diagonal crossing for zoom heat & space. Use exactly the
projection of the elected GNS space to `ManyF` at `\xi`. -/
lemma crossing_centered (v : Bank) (t : ℝ≥0) :
    Tendsto (fun i : ℕ => inner ℂ (η Z i) ((S).U ((ρ i) • v)
      ((S).E ((dewN A i)*t) (η Z' i)))) atTop (𝓝 0) := by
  let T i := (dewN A i)*t; let F i := (ρ i) • v
  have hx := crossing_main Z Z' A Y e hZZ v t
  have h := tenderSub _ _ _ _ _ hx (refreshing Z A Y e) (refreshing Z' A Y e)
  exact h.congr fun i => (background_zeroed_any (P:=P) (x:=x) Z Z' (c i) (r i) (F i) (T i) u).symm
local notation "H" => P.ManyF 3 ξ

/-- The positive outlay used to read the cross integrals by polarization. -/
def mixOutlay (P : Spine) (x : P.Spectrum0 3) (c r : ℕ → ℕ) (X X' : Lead.Clan)
    (a : ℂ) (i : ℕ) : Cheer.Narrow :=
  Cheer.outlay (P.seasons 3 (P.otherSpectrum 3 3 x))
    (P.birthCloud x X (c i) (r i) + a • P.birthCloud x X' (c i) (r i))
    (P.dew (c i) (r i))

lemma lyrical_mix (a : ℂ) (ha : ‖a‖=1) :
    Cheer.Lyrical (promenade Z + promenade Z') (P.mixOutlay x c r Z Z' a) := by
  refine ⟨fun i => Cheer.radiant S _ _ (dewN A i).property,
      (home_bright Z).add (home_bright Z'), ?_⟩
  intro v t
  let W (i) : (H).Op :=
    ((S).U ((ρ i) • shore v)).comp ((S).E (dewN A i*t))
  let B (i) (X X') := inner ℂ (η X i) (W i (η X' i))
  let L X := FLap (promenade X) v ↑(t:ℝ)
  have h1 X : Tendsto (fun i => B i X X) atTop (𝓝 (L X)) :=
    ((lyricalCloud X A Y e u).meets v t).congr
      fun i => Cheer.back S (η X i) (dewN A i) t v
  have h2 X X' (h : X ≠ X') : Tendsto (fun i => B i X X') atTop (𝓝 0) :=
    crossing_centered X X' A Y e u h (shore v) t
  rw [FLap_add (home_bright Z) (home_bright Z') v _ t.property]
  have h3 := (((h1 Z).add (h1 Z')).add ((h2 Z Z' hZZ).const_mul a)).add
    ((h2 Z' Z hZZ.symm).const_mul (star a))
  rw [mul_zero,mul_zero,add_zero,add_zero] at h3
  exact h3.congr fun i => (inner_augment (W i) (η Z i) (η Z' i) a ha).symm.trans
    (Cheer.back S _ (dewN A i) t v).symm

omit A Y e u hZZ in
lemma promenade_add_ne : ((promenade Z + promenade Z' : Cheer.Narrow) : Measure E4) ≠ 0 := by
  rw [FiniteMeasure.toMeasure_add]
  exact fun h => promenade_ne Z (le_antisymm (Measure.le_add_right le_rfl |>.trans h.le) bot_le)

/-- Weak convergence of the positive outlays used to read the cross integrals. -/
lemma weak_mix (a : ℂ) (ha : ‖a‖=1) :
    Tendsto (P.mixOutlay x c r Z Z' a) atTop (𝓝 (promenade Z + promenade Z')) :=
  (lyrical_mix Z Z' A Y e u hZZ a ha).march (promenade_add_ne Z Z')

#print axioms weak_mix
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
