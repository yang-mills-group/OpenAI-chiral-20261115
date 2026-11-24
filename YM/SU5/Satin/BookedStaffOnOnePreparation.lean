import YM.SU5.LoomForce.StaffLimit

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
universe u

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)
open scoped Topology Classical
open LoomForce

/-- The centered reading on the averaged physical functional, with the exact
staff, funding, ordered limits and two geometric displacements of the source. -/
def PaidStaffCovarianceAt (P : Spine) (β : ℕ → ℝ) : Prop :=
  ∀ (A I : ℝ) (W V : ℕ → Staff) (r : ℕ → ℕ)
    (F D : PlaqAxes) (L G : Twah.DirSpin) (x y : Gaia),
    0 < A → PaidPair P I W V r →
    (∀ s, (W s).face.2 = F) → (∀ s, (V s).face.2 = D) →
    Tendsto (fun s => riseX (sPow P.par s A) ((W s).face.1 - (V s).face.1)) atTop (𝓝 x) →
    x ≠ 0 → (∀ s, (W s).spin = L) → (∀ s, (V s).spin = G) →
    Tendsto (fun s => riseX (zoomR P.par A s) ((W s).u - (V s).u)) atTop (𝓝 y) →
    y ≠ 0 →
    let first := fun s => weaving P A (W s) (r s) s β
    let second := fun s => weaving P A (V s) (r s) s β
    Tendsto (fun s => infiniteE P s (first s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (second s)) atTop (𝓝 0) ∧
    Tendsto (fun s => infiniteE P s (first s * second s) -
      infiniteE P s (first s) * infiniteE P s (second s)) atTop (𝓝 (wakeFee F D L G x y))

def PaidStaffCovariance (P : Spine) : Prop :=
  ∀ (f : ℕ → ℕ) (β : ℕ → ℝ),
    Pooling P.run (takenVolume P) (takenCutoff P) f β → PaidStaffCovarianceAt P β

theorem physicalGramPaysStaffCovariance (P : Spine) (gram : P.PhysicalWakeGram) :
    PaidStaffCovariance P := by
  intro f β pool A I W V r F D L G x y hA paid hF hD hx hx0 hL hG hy hy0
  exact booked_ledger P hA gram pool paid hF hD hx hx0 hL hG hy hy0

/-- A further strict thinning keeps every rung's calibrated coupling and its
limit on the same period and cutoff trajectory. -/
theorem poolingOnFurtherThinning (P : Spine) (f c : ℕ → ℕ) (β : ℕ → ℝ)
    (pool : Pooling P.run (takenVolume P) (takenCutoff P) f β) (hc : StrictMono c) :
    Pooling P.run (takenVolume P) (takenCutoff P) (f ∘ c) β := by
  refine ⟨pool.up.comp hc, pool.issue, pool.positive, ?_⟩
  intro s
  exact (pool.received s).comp hc.tendsto_atTop

/-- The Gram hypothesis in the new reading comes from this very preparation
and register. Each given thinning admits one common coupling subsequence for
all qualifying staff pairs. The mean uses `P.E` before vacuum selection. -/
theorem wakeElectionWithPaidStaffCovariance (X : TintDemand) (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ),
      PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      QualifiedWakeReadout.{u} P K ∧ PhysicalWakeGram P ∧ PaidStaffCovariance P ∧
      ∀ f : ℕ → ℕ, StrictMono f → ∃ (c : ℕ → ℕ) (β : ℕ → ℝ), StrictMono c ∧
        Pooling P.run (takenVolume P) (takenCutoff P) (f ∘ c) β ∧
        PaidStaffCovarianceAt P β := by
  obtain ⟨P, K, E, investment, pose, readout, gram⟩ := wakeElectionWithPhysicalGram.{u} X Mc
  have covariance := physicalGramPaysStaffCovariance P gram
  refine ⟨P, K, E, investment, pose, readout, gram, covariance, ?_⟩
  intro f hf
  obtain ⟨c, β, hc, pool⟩ := Pooling.fettle P.run P.history hf
  exact ⟨c, β, hc, pool, covariance (f ∘ c) β pool⟩

/-- The actual woven staff as a registered test. A paid pair agrees with its
raw physical household on every sufficiently late rung. -/
def bookedStaffTest (P : Spine) (A : ℝ) (W : ℕ → Staff) (r : ℕ → ℕ) (β : ℕ → ℝ)
    (s : ℕ) : P.Test := by
  classical
  let field := Papal.household P.calibration (weaving P A (W s) (r s) s β)
  exact if admitted : TestFamily P.calibration true field then ⟨field, admitted⟩ else 0

theorem paidStaffTestsAgree (P : Spine) (A I : ℝ) (W V : ℕ → Staff) (r : ℕ → ℕ)
    (β : ℕ → ℝ) (paid : PaidPair P I W V r) :
    ∀ᶠ s : ℕ in atTop,
      (bookedStaffTest P A W r β s).val =
        Papal.household P.calibration (weaving P A (W s) (r s) s β) ∧
      (bookedStaffTest P A V r β s).val =
        Papal.household P.calibration (weaving P A (V s) (r s) s β) := by
  classical
  filter_upwards [paid.rents] with s rented
  obtain ⟨n, e, w, o, _, _, first, second, _⟩ := rented.exists
  have firstAdmitted := aux_test (weaving_ok P (W s) A (r s) w s β first)
  have secondAdmitted := aux_test (weaving_ok P (V s) A (r s) w s β second)
  simp [bookedStaffTest, firstAdmitted, secondAdmitted]

/-- All three averaged readings in the staff limit use the character measure
of the same preparation, including the joint physical household. -/
theorem paidStaffCharacterMeansAgree (P : Spine) (A I : ℝ) (W V : ℕ → Staff)
    (r : ℕ → ℕ) (β : ℕ → ℝ) (paid : PaidPair P I W V r) :
    ∀ᶠ s : ℕ in atTop,
      let first := bookedStaffTest P A W r β s
      let second := bookedStaffTest P A V r β s
      let firstWeave := weaving P A (W s) (r s) s β
      let secondWeave := weaving P A (V s) (r s) s β
      (∫ x, P.singleState 3 s x first ∂P.pillars 3) = infiniteE P s firstWeave ∧
      (∫ x, P.singleState 3 s x second ∂P.pillars 3) = infiniteE P s secondWeave ∧
      (∫ x, P.singleState 3 s x (first * second) ∂P.pillars 3) =
        infiniteE P s (firstWeave * secondWeave) := by
  filter_upwards [paidStaffTestsAgree P A I W V r β paid] with s agrees
  have mean (field : P.Test) :
      (∫ x, P.singleState 3 s x field ∂P.pillars 3) = P.E s field.val :=
    (P.recovery 3 (P.reading 3 s field)).trans (P.occupied 3 s field)
  dsimp only
  rw [mean, mean, mean]
  change P.E s (bookedStaffTest P A W r β s).val = _ ∧
    P.E s (bookedStaffTest P A V r β s).val = _ ∧
    P.E s ((bookedStaffTest P A W r β s).val * (bookedStaffTest P A V r β s).val) = _
  rw [agrees.1, agrees.2]
  exact ⟨rfl, rfl, rfl⟩

/-- A concrete sufficient estimate for each required poll. For a product
reading the reflected norm here involves four staff insertions. -/
theorem wakePollOfReflectedCenteredNorm (P : Spine) (field : ℕ → P.Test) (z : ℂ)
    (registered : ∀ᶠ s : ℕ in atTop, ∃ v : P.Vox 3 s,
      P.voxTest 3 s v = field s - z • (1 : P.Test))
    (small : Tendsto (fun s =>
      let centered := field s - z • (1 : P.Test)
      ‖P.E s (P.reflectTest 3 centered * centered).val‖) atTop (𝓝 0)) :
    WakePoll P field z := by
  constructor
  intro tolerance positive
  have below := (tendsto_order.1 small).2 tolerance positive
  filter_upwards [registered, below] with s represented bound
  let centered := field s - z • (1 : P.Test)
  have value (x : P.Spectrum0 3) :
      P.singleState 3 s x centered = P.singleState 3 s x (field s) - z := by
    have unit : P.singleState 3 s x 1 = 1 := by rw [P.single_state, P.reading_unit, map_one]
    simp [centered, map_sub, map_smul, unit]
  calc
    (∫ x, ‖P.singleState 3 s x (field s) - z‖ ^ 2 ∂P.pillars 3) =
        ∫ x, ‖P.singleState 3 s x centered‖ ^ 2 ∂P.pillars 3 := by
          apply integral_congr_ae
          filter_upwards with x
          rw [value x]
    _ ≤ ‖P.E s (P.reflectTest 3 centered * centered).val‖ :=
      P.rosaryV 3 s centered represented
    _ < tolerance := bound

/-- Three explicit squared-deviation estimates suffice for the two booked
staffs and their product to retain their centered reading on one character.
The same thinning, layout and character are used in all three limits. -/
theorem selectedBookedStaffCovarianceOfPolls (P : Spine) (K : P.Register)
    (readout : QualifiedWakeReadout.{u} P K) (A : ℝ) (hA : 0 < A) (a b : Gaia)
    (W V : ℕ → Staff) (r : ℕ → ℕ) (β : ℕ → ℝ) (I : ℝ) (paid : PaidPair P I W V r)
    (f : ℕ → ℕ) (pool : Pooling P.run (takenVolume P) (takenCutoff P) f β)
    (lease : P.PencilLease A a b (fun s => (W s).u) (fun s => (V s).u))
    (z : ℂ)
    (firstPoll : WakePoll P (bookedStaffTest P A W r β) 0)
    (secondPoll : WakePoll P (bookedStaffTest P A V r β) 0)
    (productPoll : WakePoll P (fun s =>
      bookedStaffTest P A W r β s * bookedStaffTest P A V r β s) z) :
    ∃ c : ℕ → ℕ, StrictMono c ∧
      Pooling P.run (takenVolume P) (takenCutoff P) (f ∘ c) β ∧
      (∀ᶠ n : ℕ in atTop,
        let s := f (c n)
        (bookedStaffTest P A W r β s).val =
          Papal.household P.calibration (weaving P A (W s) (r s) s β) ∧
        (bookedStaffTest P A V r β s).val =
          Papal.household P.calibration (weaving P A (V s) (r s) s β)) ∧
      ∀ U : P.Spectrum0 3 → Prop, (∀ᵐ x ∂P.pillars 3, U x) →
      ∃ x, U x ∧ JointTuple.{u} P K x ∧
        HoldRead P A (f ∘ c) x a b (fun s => (W s).u) (fun s => (V s).u) ∧
        Tendsto (fun n =>
          let s := f (c n)
          let first := bookedStaffTest P A W r β s
          let second := bookedStaffTest P A V r β s
          P.singleState 3 s x (first * second) -
            P.singleState 3 s x first * P.singleState 3 s x second) atTop (𝓝 z) := by
  let readings : Option Bool → ℕ → P.Test
    | none => bookedStaffTest P A W r β
    | some false => bookedStaffTest P A V r β
    | some true => fun s => bookedStaffTest P A W r β s * bookedStaffTest P A V r β s
  let values : Option Bool → ℂ
    | none => 0
    | some false => 0
    | some true => z
  have polls : ∀ i, WakePoll P (readings i) (values i) := by
    intro i
    cases i with
    | none => exact firstPoll
    | some flag =>
      cases flag with
      | false => exact secondPoll
      | true => exact productPoll
  obtain ⟨c, hc, select⟩ := readout A hA a b (fun s => (W s).u) (fun s => (V s).u)
    (Option Bool) f pool.up lease readings values polls
  refine ⟨c, hc, poolingOnFurtherThinning P f c β pool hc, ?_, ?_⟩
  · exact (pool.up.comp hc).tendsto_atTop.eventually (paidStaffTestsAgree P A I W V r β paid)
  intro U full
  obtain ⟨x, hx, joint, layout, limits⟩ := select U full
  refine ⟨x, hx, joint, layout, ?_⟩
  simpa [readings, values] using
    (limits (some true)).sub ((limits none).mul (limits (some false)))

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
