import YM.SU5.Six.CrossHeat
set_option maxHeartbeats 250000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Cheer
open Cheer (Narrow)
/-!
Matrix-valued weak convergence in quadratic form formulation. Since costs on
Borel sets are sesquilinear, controls the off-diagonal measures too (both
real and imaginary parts). Uses Lyrical's *diagonal* measure machinery, now
on arbitrary mixtures of the six fields thanks to CrossHeat.
-/
abbrev SixCoefficients := Lead.Clan → ℂ
variable (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(c r:ℕ→ℕ)(z:SixCoefficients)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
def superposed : H := ∑ Z:Lead.Clan, z Z • P.birthCloud x Z s n
def zoomMatrix  : Narrow :=
  Cheer.outlay (S) (P.superposed x s n z) (P.dew s n)
def diagonalLimit : Narrow := ∑ Z:Lead.Clan, (‖z Z‖₊^2) • promenade Z
-- matrix measure interpretation on Borel sets
private lemma mapped (G:Hilbert) (a:Lead.Clan→G) (f:G.Op) :
    f (∑ i:Lead.Clan,z i • a i)=∑ i:Lead.Clan, z i • f (a i):= by rw [map_sum]; simp only [map_smul]
lemma zoom_matrix_event (V:Set E4)(h:MeasurableSet V) :
    ((P.zoomMatrix x s n z): Measure E4).real V =
      ‖∑ Z:Lead.Clan, z Z • ((S).ℚmeasure.region (press (P.dew s n) V) (P.birthCloud x Z s n))‖ ^ 2 := by
  unfold zoomMatrix
  let Q:=(S).ℚmeasure.region (Cheer.press (P.dew s n) V)
  have he: Q (P.superposed x s n z)=∑ Z:Lead.Clan, z Z • Q (P.birthCloud x Z s n):= by
    exact mapped z H (fun i=>P.birthCloud x i s n) Q
  exact ((Cheer.norm_region (S) (P.superposed x s n z) (P.dew s n) V h).symm).trans (congrArg (fun v:H=> ‖v‖^2) he)

private lemma brilliant_term (Z:Lead.Clan) : Brilliant (‖z Z‖₊^2 • promenade Z) :=
  Measure.ae_smul_measure (home_bright Z) _
lemma brilliant_limit : Brilliant (diagonalLimit z) := by
  unfold diagonalLimit Brilliant
  rw [FiniteMeasure.toMeasure_sum,ae_finsetSum_measure_iff]
  exact fun Z _ => brilliant_term z Z
private lemma weightC (a:ℂ) : ((↑(‖a‖₊^2):ℝ):ℂ) = star a * a:=by
  rw [NNReal.coe_pow, coe_nnnorm, ← Complex.normSq_eq_norm_sq]
  exact Complex.normSq_eq_conj_mul_self
lemma FLap_diagonalLimit (a:Space3)(t:ℝ≥0) :
    FLap (diagonalLimit z) a (↑(t:ℝ)) =
      ∑ Z:Lead.Clan, star (z Z) * (z Z) * FLap (promenade Z) a (↑(t:ℝ)) := by
  unfold diagonalLimit FLap
  rw [FiniteMeasure.toMeasure_sum, integral_finsetSum_measure
    (fun Z _=> Cheer.destined _ a ((↑(t:ℝ)):ℂ) (brilliant_term z Z) (show 0≤(↑(t:ℝ):ℂ).re from t.property))]
  apply sum_congr rfl
  intro Z _
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul, weightC]
variable {P x r c} {q:ℕ→ℝ}
  (A:Launch P c r)(Y:readyUV P c r x q)(hq:Tendsto q atTop (𝓝 0))(u:P.lodestarHere 3 (P.otherSpectrum 3 3 x))
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "χ" Z:max i:max => P.birthCloud x Z (c i) (r i)
private lemma sum_heat (G':Hilbert) (z':SixCoefficients)(v:Lead.Clan→ℕ→G')
    (K:ℕ→G'.Op) (L:Lead.Clan→ℂ)
    (he:∀ Z W, Tendsto (fun i=>inner ℂ (v Z i) (K i (v W i))) atTop
      (𝓝 (if Z=W then L Z else 0))) :
    let V(i:ℕ):=∑ Z:Lead.Clan, z' Z • (v Z i)
    Tendsto (fun i=> inner ℂ (V i) (K i (V i))) atTop
      (𝓝 (∑ Z:Lead.Clan, star (z' Z)*z' Z*L Z)) := by
  intro V
  let h(i:ℕ)(Z W:Lead.Clan):=inner ℂ (v Z i) (K i (v W i))
  have hx : Tendsto (fun i=> ∑ Z:Lead.Clan,∑ W:Lead.Clan, star (z' Z) * z' W * h i Z W)
      atTop (𝓝 (∑ Z:Lead.Clan,∑ W:Lead.Clan, star (z' Z) * z' W * (if Z=W then L Z else 0))) :=
    tendsto_finsetSum _ fun Z _=> tendsto_finsetSum _ fun W _=>(he Z W).const_mul _
  simp only [mul_ite,mul_zero,sum_ite_eq,mem_univ,↓reduceIte] at hx
  exact hx.congr fun i=>by
    unfold V h; simp_rw [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,mul_assoc]
    rfl
include A Y hq u
lemma FLap_zoomMatrix : Lyrical (diagonalLimit z) (fun i=> P.zoomMatrix x (c i) (r i) z):= by
  let R(i:ℕ):ℝ≥0:= ⟨ρ i,(P.dew_pos _ (A.unitSize i)).le⟩
  refine ⟨fun i => radiant (S) _ _ (R i).property, brilliant_limit z,fun a t=>?_⟩
  let E(i:ℕ):= R i*t
  let G(i:ℕ):= ρ i • cutPulse a
  let h(i:ℕ)(v w:H):= inner ℂ v ((S).U (G i) ((S).E (E i) w))
  let L(Z:Lead.Clan):= FLap (promenade Z) a ((↑(t:ℝ)):ℂ)
  have he:P.dimensionS c r E (t:ℝ):= tendsto_const_nhds.congr fun i=> by
    rw [show (E i :ℝ)= ρ i*(t:ℝ) from rfl]; field_simp [(P.dew_pos _ (A.unitSize i)).ne']
  have hv:Tendsto (fun i=> (ρ i)⁻¹ • G i) atTop (𝓝 (cutPulse a)):=
    tendsto_const_nhds.congr fun i=> (inv_smul_smul₀ (P.dew_pos _ (A.unitSize i)).ne' _).symm
  have Hc (Z W : Lead.Clan) : Tendsto (fun i=> h i (χ Z i) (χ W i)) atTop
      (𝓝 (if Z=W then L Z else 0)) := by
    split_ifs with e
    · subst W; exact zoom_diagonal Z A Y hq u a t E he G hv
    by_cases p:t=0
    · refine (zoom_other_zero Z W A Y hq e u _ G hv).congr fun i=> ?_
      have hy': E i=0:=by rw [show E i=R i*t from rfl,p,mul_zero]
      exact congrArg (fun (T:ℝ≥0) => inner ℂ (χ Z i) ((S).U (G i) ((S).E T (χ W i)))) hy'.symm
    exact zoom_other_pos Z W A Y hq e u _ (show 0 < (t:ℝ) from
      NNReal.coe_pos.mpr (lt_of_le_of_ne bot_le (Ne.symm p))) E he G hv
  let K(i):=( (S).U (G i)).comp ((S).E (E i))
  let w(i:ℕ):=P.superposed x (c i) (r i) z
  let F'(i:ℕ):=P.zoomMatrix x (c i) (r i) z
  let Q':=FLap (diagonalLimit z) a (↑(t:ℝ))
  have hm:Tendsto (fun i=>inner ℂ (w i) (K i (w i))) atTop (𝓝 Q') := by
    have hv : Q'=∑ Z:Lead.Clan,star (z Z)*z Z*L Z:= FLap_diagonalLimit z a t
    let f(i):=inner ℂ (w i) (K i (w i))
    change Tendsto f _ _; rw [hv]
    exact sum_heat H z (fun Z i=>χ Z i) K L Hc
  exact hm.congr fun i=> (Cheer.back (S) (w i) (R i) t a).symm
lemma zoomMatrix_limit : Tendsto (fun i=> P.zoomMatrix x (c i) (r i) z) atTop (𝓝 (diagonalLimit z)):= by
  have hp := FLap_zoomMatrix z A Y hq u
  by_cases h:(diagonalLimit z:Measure E4)=0
  · have he:diagonalLimit z=0:=FiniteMeasure.toMeasure_injective h
    rw [he] at hp ⊢
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    apply tendsto_subtype_rng.mpr
    exact hp.massR
  exact hp.march h
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
