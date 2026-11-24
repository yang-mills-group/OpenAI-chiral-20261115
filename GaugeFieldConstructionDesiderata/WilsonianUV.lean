import YM.SU5.Selected.Vacuum

/-!
# Running and screening on the selected finite Wilsonian histories

Uniform in the tape index `i` and depth `N`, even before imposing
the diagonal and kick conditions. These estimates are on the histories,
not a claim about normalized correlators at arbitrary period/depth pairs.
In GaugeFieldConstructionDesiderata.Wilsonian, `satin_theory_with_running` gives the tests together with the original
existence conclusion.
-/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Wilsonian
open Finset

/-! ### Scalar helpers -/

private lemma scatter (k : ℕ) (a : ℕ → ℝ) (x r : ℝ)
    (h : ∀ d ∈ range k, |a d - x| ≤ r) :
    |(∑ d ∈ range k, a d) - (k : ℝ) * x| ≤ k * r := by
  calc
    _ = |∑ d ∈ range k, (a d - x)| := by rw [sum_sub_distrib]; simp
    _ ≤ ∑ d ∈ range k, |a d - x| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _d ∈ range k, r := sum_le_sum h
    _ = _ := by simp

private lemma sum_split (q f z β : ℕ → ℝ) (N j k : ℕ)
    (step : ∀ s, s < N → β (s+1) - β s = -q s - f s + z s)
    (hw : j+k ≤ N) :
    β (j+k) - β j =
      -(∑ d ∈ range k, q (j+d)) - (∑ d ∈ range k, f (j+d)) +
        ∑ d ∈ range k, z (j+d) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ, sum_range_succ, Nat.add_succ]
    linarith only [step (j+k) (by omega), ih (by omega)]

-- Clear positive denominators; keep all constants rational.
private lemma clear_ratio {a d x ε : ℝ} (hd : 0 < d) :
    |a / d - x| < ε ↔ (-ε + x) * d < a ∧ a < (ε + x) * d := by
  rw [abs_lt, lt_sub_iff_add_lt, lt_div_iff₀ hd, sub_lt_iff_lt_add, div_lt_iff₀ hd]

private lemma screening_calc {G₀ b k g S R Z ε : ℝ} (hd : 0 < k * g)
    (hb : b = G₀ - S + R)
    (hS : |S - k * (12/55 * g)| ≤ Z)
    (hR : |R| ≤ k * (3/110 * g * ε))
    (hZ : Z < k * (3/110 * g * ε)) :
    |55/3 * (G₀ - b) / (k * g) - 4| < ε := by
  rw [clear_ratio hd]
  rw [abs_le] at hS hR
  constructor
  · linarith only [hb, hS.1, hR.2, hZ]
  · linarith only [hb, hS.2, hR.1, hZ]

private lemma running_calc {G₀ b k g : ℝ} (hd : 0 < k * g)
    (hG : |G₀ - k * g| ≤ k * (7/220 * g))
    (hS : |55/3 * (G₀ - b) / (k * g) - 4| < 2/15) :
    |55/3 * b / (k * g) - 43/3| < 43/60 := by
  rw [clear_ratio hd] at hS ⊢
  rw [abs_le] at hG
  constructor
  · linarith only [hS.2, hG.1]
  · linarith only [hS.1, hG.2]

open Filter
open scoped Topology

/-! ### Actual tape data -/

variable (P : Spine)

/-- `i` indexes the period, `N` is the actual depth (not a cutoff-subsequence index). -/
abbrev runRow (i N : ℕ) := (P.run.voyage i).X N

/-- Actual fitted inverse coupling on the row. Only used within its depth. -/
def B (i N s : ℕ) : ℝ := ((runRow P i N).gram s).beta

/-- The stationary Gold charge in that history, in the coarse-going sign.
For common depth this function does not need the volume index. -/
def coarseGauge (N s : ℕ) : ℝ := P.par.V.L.charge (N-1-s)

/-- Accumulated gauge variation in the opposite (fine-going) sign. -/
def G (N j k : ℕ) : ℝ := -(∑ d ∈ range k, coarseGauge P N (j+d))

/-- Leading gauge increment for the *same* block ratio. -/
def ℓg : ℝ := Vale.billX P.par.R.L

def bEff (i N j k : ℕ) : ℝ := 55/3 * (B P i N (j+k) - B P i N j) / (k * ℓg P)

def screening (i N j k : ℕ) : ℝ :=
  55/3 * (G P N j k - (B P i N (j+k) - B P i N j)) / (k * ℓg P)

theorem ℓg_pos : 0 < ℓg P := by
  have h : 0 < ℓg P / 4 := Py.billx_T P.par.V
  linarith only [h]

theorem billC_eq : Vale.billC P.par.R.L = 12/55 * ℓg P := by
  unfold ℓg Vale.billX Vale.billC Gauge.slopeConstant Cascade.spiceM
  rw [Thera.hut_k]
  ring

theorem reference (i N : ℕ) : B P i N 0 = P.par.x :=
  (runRow P i N).pull.color.trans (runRow P i N).due.unit

theorem B_pos (i N s : ℕ) (h : s ≤ N) : 0 < B P i N s :=
  lt_of_lt_of_le
    (half_pos (((Real.exp_pos 1).trans_le P.large).trans_le (Vale.crown P.par.R.L P.par.x s)))
    ((runRow P i N).pull.sift s h).1

abbrev stationaryLast (i N : ℕ) :=
  P.par.W.arm (m := P.run.ir i) (P.run.meter.large.trans (P.run.voyage i).funds) N

/-- Actual Gram entries carry these same stationary data
(the charge also appears with this gauge path in `P.par.V.L.sold`). -/
theorem carried (i N s : ℕ) (hs : s ≤ N) :
    P.par.V.L.path (N-s) = ((runRow P i N).gram s).path ∧
    (stationaryLast P i N).Q s = ((runRow P i N).gram s).J :=
  ⟨((runRow P i N).pull.owns s hs).path, ((runRow P i N).pull.owns s hs).taste⟩

theorem actual_step (i N s : ℕ) (hs : s < N) :
    B P i N (s+1) - B P i N s =
      - coarseGauge P N s - (stationaryLast P i N).shift s + (runRow P i N).fee s := by
  have h : (runRow P i N).pilot s = (runRow P i N).pilot (s+1) +
      (coarseGauge P N s + (stationaryLast P i N).shift s) :=
    (runRow P i N).due.fee s hs
  unfold B
  linarith only [h, (runRow P i N).pull.shift s hs]

def shifts (i N j k : ℕ) : ℝ :=
  ∑ d ∈ range k, (stationaryLast P i N).shift (j+d)
def fees (i N j k : ℕ) : ℝ :=
  ∑ d ∈ range k, (runRow P i N).fee (j+d)

theorem split_window (i N j k : ℕ) (hw : j+k ≤ N) :
    B P i N (j+k) - B P i N j = G P N j k - shifts P i N j k + fees P i N j k :=
  sum_split (coarseGauge P N) (stationaryLast P i N).shift (runRow P i N).fee
    (B P i N) N j k (actual_step P i N) hw

/-! ### Errors -/

theorem gauge_step (N s : ℕ) :
    |coarseGauge P N s + ℓg P| ≤ 7/220 * ℓg P := by
  have t : ℓg P * (3/4) ≤ (ℓg P - Vale.billC P.par.R.L) - P.par.K.top.drift :=
    P.par.V.roomZ.1
  rw [billC_eq P] at t
  have h : |coarseGauge P N s + ℓg P| + 1 ≤ P.par.K.top.drift :=
    P.par.V.L.bound (N-1-s)
  linarith only [h, t]

theorem gauge_window (N j k : ℕ) :
    |G P N j k - k * ℓg P| ≤ k * (7/220 * ℓg P) := by
  unfold G
  rw [← sum_neg_distrib]
  apply scatter
  intro d _
  change |-coarseGauge P N (j+d) - ℓg P| ≤ _
  rw [show -coarseGauge P N (j+d) - ℓg P =
        -(coarseGauge P N (j+d) + ℓg P) by ring, abs_neg]
  exact gauge_step P N (j+d)

theorem shifts_paid (i N j k : ℕ) (hw : j+k ≤ N) :
    |shifts P i N j k - k * (12/55 * ℓg P)| ≤ P.par.W.z := by
  rw [← billC_eq P]
  have h : (stationaryLast P i N).music P.par.W.z :=
    P.par.W.pose (P.run.meter.large.trans (P.run.voyage i).funds) N
  exact h j k hw

/-- In a sufficiently fine window the summed fit errors cost ≤ k*t,
uniformly in the tapes and depths. -/
theorem fees_paid (t : ℝ) (ht : 0 < t) :
    ∃ J, ∀ j k : ℕ, J ≤ j → ∀ i N : ℕ, j+k ≤ N → |fees P i N j k| ≤ k * t := by
  have h : Tendsto (Vale.hat P.par.R.L P.par.x) atTop atTop :=
    tendsto_atTop_add_const_left atTop _
      (tendsto_natCast_atTop_atTop.atTop_mul_const (ℓg_pos P))
  obtain ⟨J, hJ⟩ :=
    eventually_atTop.mp (((Py.Chill_v.spine_a P.par.app.post).comp h).eventually
      (ge_mem_nhds ht))

  refine ⟨J, fun j k hj i N hw => ?_⟩
  let a (d : ℕ) := (runRow P i N).fee (j+d)
  have hp (d : ℕ) (hd : d ∈ range k) : |a d - 0| ≤ t := by
    have hd' := mem_range.mp hd
    rw [sub_zero]
    exact ((runRow P i N).pull.price (j+d) (by omega)).trans (hJ (j+d) (by omega))
  simpa only [a, fees, mul_zero, sub_zero] using scatter k a 0 t hp

/-! ### Uniform tests -/

theorem uniform_screening (ε : ℝ) (hε : 0 < ε) :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ i N : ℕ, j+k ≤ N → |screening P i N j k - 4| < ε := by
  let t := 3/110 * ℓg P * ε
  have ht : 0 < t :=
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 3/110) (ℓg_pos P)) hε
  obtain ⟨J, hJ⟩ := fees_paid P t ht
  obtain ⟨K, hK⟩ := exists_nat_gt (P.par.W.z / t)
  refine ⟨max 1 J, max 1 K, le_max_left .., le_max_left .., ?_⟩
  intro j k hj hk i N hw
  have hZ : P.par.W.z < k * t :=
    (div_lt_iff₀ ht).mp (hK.trans_le (Nat.cast_le.mpr ((le_max_right 1 K).trans hk)))
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr (by omega)
  exact screening_calc (mul_pos hk' (ℓg_pos P))
    (split_window P i N j k hw)
    (shifts_paid P i N j k hw)
    (hJ j k ((le_max_right 1 J).trans hj) i N hw)
    hZ

theorem uniform_running :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ i N : ℕ, j+k ≤ N → |bEff P i N j k - 43/3| < 43/60 := by
  obtain ⟨J, K, hJ, hK, h⟩ := uniform_screening P (2/15) (by norm_num)
  refine ⟨J, K, hJ, hK, ?_⟩
  intro j k hj hk i N hw
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr (by omega)
  exact running_calc (b := B P i N (j+k) - B P i N j)
    (mul_pos hk' (ℓg_pos P)) (gauge_window P N j k)
    (h j k hj hk i N hw)

/-- The window increases resolution by a fixed factor for fixed k:
here expressed by the side (at the same period). -/
theorem scale_ratio (i j k : ℕ) :
    P.par.Ctor (P.run.ir i) (j+k) = P.par.Ctor (P.run.ir i) j * P.par.R.L ^ k := by
  induction k with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ← ih, Nat.add_succ]
    exact Vale.grows _ _ _ _

-- Defeq the corresponding abbreviations in GaugeFieldConstruction.Trajectory; use the
-- same regulator subsequences without pulling in other imports here.
abbrev volSeq := P.period ∘ P.projection.rows
abbrev cutSeq := P.cutoff ∘ P.projection.columns
abbrev uvSeq := P.run.uv ∘ cutSeq P

theorem diagonal_coverage (j k : ℕ) :
    ∀ᶠ r in atTop,
      (P.run.voyage (volSeq P r)).kick ≤ cutSeq P r ∧ j+k ≤ uvSeq P r :=
  (P.history.finance (j+k)).mono fun _ p => ⟨p.depth,p.enters⟩

/-- In particular one may take k = K here for every j ≥ J. -/
theorem joint_diagonal (ε : ℝ) (hε : 0 < ε) :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ᶠ r in atTop,
          (P.run.voyage (volSeq P r)).kick ≤ cutSeq P r ∧
          j+k ≤ uvSeq P r ∧
          |bEff P (volSeq P r) (uvSeq P r) j k - 43/3| < 43/60 ∧
          |screening P (volSeq P r) (uvSeq P r) j k - 4| < ε := by
  obtain ⟨J₁, K₁, hJ, hK, h⟩ := uniform_running P
  obtain ⟨J₂, K₂, -, -, h'⟩ := uniform_screening P ε hε
  refine ⟨max J₁ J₂, max K₁ K₂, hJ.trans (le_max_left ..), hK.trans (le_max_left ..), ?_⟩
  intro j k hj hk
  exact (diagonal_coverage P j k).mono fun r w => ⟨w.1, w.2,
    h j k ((le_max_left ..).trans hj) ((le_max_left ..).trans hk) _ _ w.2,
    h' j k ((le_max_right ..).trans hj) ((le_max_right ..).trans hk) _ _ w.2⟩

/-- Package for the existence statement. Uniform tests include every
diagonal row reaching j+k, without needing even the kick condition. -/
structure UVTests : Prop where
  full :
    ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
      ∀ j k : ℕ, J ≤ j → K ≤ k →
        ∀ i N : ℕ, j+k ≤ N → |bEff P i N j k - 43/3| < 43/60
  screened :
    ∀ ε : ℝ, 0 < ε →
      ∃ J K : ℕ, 1 ≤ J ∧ 1 ≤ K ∧
        ∀ j k : ℕ, J ≤ j → K ≤ k →
          ∀ i N : ℕ, j+k ≤ N → |screening P i N j k - 4| < ε
  window (j k : ℕ) :
    ∀ᶠ r in atTop,
      (P.run.voyage (volSeq P r)).kick ≤ cutSeq P r ∧ j+k ≤ uvSeq P r
  fixed_ref (i N : ℕ) : B P i N 0 = P.par.x

theorem tests : UVTests P :=
  ⟨uniform_running P, uniform_screening P, diagonal_coverage P, reference P⟩

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Wilsonian

end
