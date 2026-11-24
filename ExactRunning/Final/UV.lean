import GaugeFieldConstructionDesiderata.WilsonianUV
import ExactRunning.Final.Gold

noncomputable section
set_option maxRecDepth 3000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Wilsonian
variable (P : Spine)

def bGauge (N j k : ℕ) : ℝ := 55/3 * G P N j k / (k*ℓg P)

theorem uniform_gauge (ε : ℝ) (hε : 0 < ε) :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ (_i : ℕ) (N : ℕ), j+k ≤ N → |bGauge P N j k - 55/3| < ε := by
  obtain ⟨K,h,g⟩ :=
    ExactRunning.gold_ratio P.par.V.L P.par.chart (ℓg_pos P) ε hε
  exact ⟨1,K, le_rfl, h,fun j k _ hk i N=> g N j k hk⟩

def ExactLimits : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ i N : ℕ, j+k ≤ N →
          |bGauge P N j k - 55/3| < ε ∧
          |bEff P i N j k - 43/3| < ε ∧
          |screening P i N j k - 4| < ε

lemma bEff_eq (i N j k : ℕ) :
    bEff P i N j k = bGauge P N j k - screening P i N j k := by
  unfold bGauge screening bEff
  ring

private lemma combine {g s ε : ℝ} (h : |g - 55/3| < ε/2) (p : |s-4| < ε/2) :
    |g - s - 43/3| < ε := by
  rw [abs_lt] at *
  constructor <;> linarith

theorem uniform_exact_running : ExactLimits P := by
  intro ε hε
  obtain ⟨J, K, hJ, hK, hs⟩ := uniform_screening P _ (half_pos hε)
  obtain ⟨j, k, _, _, hg⟩ := uniform_gauge P _ (half_pos hε)
  refine ⟨max J j, max K k, hJ.trans (le_max_left ..), hK.trans (le_max_left ..),?_⟩
  intro x y h h' i N hy
  have s := hs _ _ ((le_max_left ..).trans h) ((le_max_left ..).trans h') i N hy
  have g := hg _ _ ((le_max_right ..).trans h) ((le_max_right ..).trans h') i N hy
  rw [bEff_eq]
  exact ⟨g.trans (half_lt_self hε), combine g s, s.trans (half_lt_self hε)⟩

open Filter in
theorem exact_joint_diagonal (ε : ℝ) (h : 0 < ε) :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ᶠ r in atTop,
          (P.run.voyage (volSeq P r)).kick ≤ cutSeq P r ∧
          j+k ≤ uvSeq P r ∧
          |bGauge P (uvSeq P r) j k - 55/3| < ε ∧
          |bEff P (volSeq P r) (uvSeq P r) j k - 43/3| < ε ∧
          |screening P (volSeq P r) (uvSeq P r) j k - 4| < ε := by
  obtain ⟨J, K, hJ, hK, p⟩ := uniform_exact_running P ε h
  exact ⟨J,K,hJ,hK,fun j k hj hk =>
    (diagonal_coverage P j k).mono fun r w => ⟨w.1,w.2,p j k hj hk _ _ w.2⟩⟩

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Wilsonian
end
