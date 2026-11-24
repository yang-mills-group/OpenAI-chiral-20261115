import YM.SU5.Six.ZoomPair
import YM.SU5.Six.Interior
import YM.SU5.Six.Prism

/-!
# Six-clan zoom matrix: positive interior-band gap

Through a minorant, without restrictions on the boundary measure.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.Six
open Filter MeasureTheory Cheer
open scoped MatrixOrder
lemma charge_bridge {H : Hilbert} (S : OS.Semigroup H timeAxis) {ι : Type*} [Fintype ι]
    (v : ι → H) (z : ℝ) (hz : 0 ≤ z) {V : Set E4} (h : MeasurableSet V) {f : E4 → ℂ}
    (hf : Continuous f) (hb : ∀ p, ‖f p‖ ≤ 1) (hs : ∀ p ∉ V, f p = 0) :
    let X := S.ℚmeasure.bill v (fun w => ↑(‖f (zoom z w)‖^2))
    0 ≤ X ∧ X ≤ S.ℚmeasure.bill v ((press z V).indicator (fun _ => 1)) := by
  let B := press z V
  let hi : HalfTest f := ⟨hf.measurable.comp measurable_subtype_coe,1,fun p _ => hb p⟩
  obtain ⟨T,hT⟩ := ((hi.zoom hz).adm S).exists_represents
  dsimp only
  rw [Spectral.PVM.bill_ind _ _ (pressured _ h), ← hT.gram v]
  refine ⟨(Matrix.posSemidef_gram _ _).nonneg,
      hT.gram_le v (S.ℚmeasure.represents_indicator B (pressured _ h)) fun x => ae_of_all _ fun w => ?_⟩
  by_cases hw:w∈B
  · simpa [hw] using hb (zoom z w)
  rw [show f _ = _ from hs _ hw,norm_zero]; exact norm_nonneg _
end YM.Six
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
open Cheer YM.Six

variable {P : Spine} {x : P.Spectrum0 3} {c r : ℕ → ℕ} (Z Z' : Lead.Clan)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 ξ
local notation "Q" => YM.OS.Semigroup.ℚmeasure S
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "η" X:max i:max => P.birthCloud x X (c i) (r i)

variable (A : Launch P c r) {q : ℕ → ℝ} (Y : readyUV P c r x q)
         (e : Tendsto q atTop (𝓝 0)) (u : P.lodestarHere 3 (P.otherSpectrum 3 3 x))

/-- The matrix on frequency scale `ρ`, via polarized positive measures. -/
def zoomBill (P : Spine) (x : P.Spectrum0 3) (s n : ℕ) (f : E4 → ℂ) :
    Matrix Lead.Clan Lead.Clan ℂ :=
  (OS.Semigroup.ℚmeasure (P.seasons 3 (P.otherSpectrum 3 3 x))).bill
    (fun i => P.birthCloud x i s n) (fun p => f (Cheer.zoom (P.dew s n) p))

/-- The actual zoom window charge on the centered Six, for measurable V. -/
def windowCharge (P : Spine) (x : P.Spectrum0 3) (s n : ℕ) (V : Set E4) :
    Matrix Lead.Clan Lead.Clan ℂ :=
  (OS.Semigroup.ℚmeasure (P.seasons 3 (P.otherSpectrum 3 3 x))).bill
    (fun i => P.birthCloud x i s n) ((press (P.dew s n) V).indicator (fun _ => 1))

lemma window_eq (s n) {V} (hv : MeasurableSet V) :
    P.windowCharge x s n V = Matrix.gram ℂ
      (fun Z => (Q).region (press (P.dew s n) V) (P.birthCloud x Z s n)) :=
  Spectral.PVM.bill_ind _ _ (pressured _ hv)

include A Y e u

theorem zoom_matrix {F : ℕ → E4 → ℂ} {f : E4 → ℂ} (h : HalfLimit F f) :
    Tendsto (fun i => P.zoomBill x (c i) (r i) (F i)) atTop
      (𝓝 (Matrix.diagonal fun Z => ∫ p, f p ∂(promenade Z:Measure E4))) := by
  refine tendsto_pi_nhds.mpr fun Z => tendsto_pi_nhds.mpr fun Z' => ?_
  rw [Matrix.diagonal_apply]
  exact zoom_pair Z Z' A Y e u h

omit Y e u in
lemma charge_minorant (i : ℕ) {V : Set E4} (h : MeasurableSet V) {f : E4 → ℂ}
    (hf : Continuous f) (hb : ∀ p, ‖f p‖ ≤ 1) (hs : ∀ p ∉ V, f p = 0) :
    let X := P.zoomBill x (c i) (r i) (fun p => ↑(‖f p‖^2))
    0 ≤ X ∧ X ≤ P.windowCharge x (c i) (r i) V := by
  exact charge_bridge S _ (ρ i) (P.dew_pos _ (A.unitSize i)).le h hf hb hs

/-- Interior window spectral uniform lower bound. Use in particular on
any fixed ball specified in `l:zoommat`, before freezing `i`. -/
theorem uniform_charge {V : Set E4} (h : IsOpen V) (hv : (Mink.inside ∩ V).Nonempty) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in atTop, d • (1 : Matrix Lead.Clan Lead.Clan ℂ) ≤
      P.windowCharge x (c i) (r i) V := by
  obtain ⟨p,hp,hpv⟩ := hv
  obtain ⟨f,hf,he,hb,hs⟩ := minorant h p hpv
  let g (q : E4) := ‖f q‖^2
  have hc : Continuous g := hf.norm.pow _
  have hn : ∀ q, g q ≤ 1 := fun q => pow_le_one₀ (norm_nonneg _) (hb q)
  have htest : HalfLimit (fun _ q => ↑(g q)) (fun q => ↑(g q)) := HalfLimit.fixed
    (Complex.continuous_ofReal.comp hc).continuousOn ⟨1,fun q _ => by
      rw [Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ g q from sq_nonneg _)]; exact hn q⟩
  let X (i) := P.zoomBill x (c i) (r i) (fun q => ↑(g q))
  have hpd : (Matrix.diagonal fun Z => ∫ q, (↑(g q) : ℂ) ∂(promenade Z:Measure E4)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun Z =>
      interior_positive (home_bright Z) (fun {_} => importance Z) g hc
        (fun q _ => sq_nonneg _) _ (fun q _ => hn q) _ hp (by simp [g,he])
  have hcc (i) := charge_minorant (P:=P) (x:=x) A i h.measurableSet hf hb hs
  obtain ⟨d,hd,hX⟩ := eventually_gap (M:=X) hpd (zoom_matrix A Y e u htest)
    (.of_forall fun i => (Matrix.nonneg_iff_posSemidef.mp (hcc i).1).isHermitian)
  exact ⟨d,hd,hX.mono fun i hi => le_trans hi (hcc i).2⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
