import SatinFixedContrastNovember4
/-!
# New, width-removing two-probe test in the SAME six-family election

Geometry, regulator inserts, and split prediction. Contrast will be against
*product of actual raw pure gauge & pure matter marginals*, the same criterion
as in `FixedSatinReadings` (specializing its universal Ward-factorized test).
We're interested in the TOTAL price discrepancy for two individually placeable,
individually stencil-gauge-invariant **mixed** observables, not separating
*their gauge from their matter legs in space*. The limit/pair experiment is in
later files; as we'll see, this channel behaves quite differently from a
propagating connected correlation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
variable (P : Spine) (Z W : Lead.Clan) (s n t : ℕ)
local notation "κ" => P.calibration

/-- Born at its OWN resolution `s` -- will be taken to infinity. On the pose grid
at `t≥s` use `P.issuing t`, for the smoothed insertion `thinOutgoing` (resp.
`thinIncoming`) below. We only use these bodies in the level (single character)
interpretation, not operations localized at zero width in a Minkowski algebra.

Keep exactly the first term of the Six experiment, **including normalization**.
Relative to Six we have changed a COUNTERTERM prescription: *don't* subtract the
positive-time shifted copy. There's no subtraction (also no vacuum subtraction).
This is a useful renormalized field with a quite accessible two-field thin limit;
we'll cost also what happens with the old cancellation. Keep the old geometric
budgets even though could make them a bit smaller. -/
def thinString : P.Apron where
  s := s
  u := P.probeClock n
  pos := P.clock_positive n
  F := P.frontMat Z n
  S := P.measureStencil n
  bay := tallerBay κ _ _ Finset.subset_union_left (P.visibility Z n)
  realM := P.front_real Z n
  shelter := P.shelters n

lemma thinString_birth : P.birthF 3 s (P.thinString Z s n).F := P.brightC Z s n

/-- On every requested `Fields` input, including both of its link arguments (uses
first), the Wilson transport in `coilFlag` on `P.flash n`, and the antiperiodic
letters, the normalization is exactly this, before posing (reflection rule `kiss`).
Changing level for finer grid quadrature uses the elected transfer, NOT applying
this constructor at that finer height; see `prepared_literal` and `thinStage_support`.
-/
lemma thinString_eval (m : Side) (X : Fields ((κ).c m)) :
    ((P.thinString Z s n).F.val m X) = (-( (n:ℂ)^3 /5)) •
      ∑ i ∈ Window.colors Z, ∑ j ∈ Window.colors Z,
        (Lamour.Bridge.Celeste.coilFlag (P.flash n) i j (onC ((κ).c m) X.1)) •
          (Fock.remove (basisC ((κ).c m) (P.flash n).death 2 j) *
           create (basisC ((κ).c m) (P.flash n).birth 0 i)) := by
  refine (P.front_read Z n m X).trans ?_
  simp only [Lead.sing, phaseF]
  simp

/-- Just to pin which geometry in `Aprons.lean` we're inheriting. -/
lemma relation_to_thick : (P.experimentBody Z s n).F =
    (P.thinString Z s n).F - P.shifts 3 (P.laterPulse n) (P.thinString Z s n).F := rfl

lemma thinString_senses (e : n > P.calibration.ℓ) : P.Sensor (P.thinString Z s n) Z.2 := by
  -- inherited endpoint and transport charges (not inferred just from being
  -- a summand of experimentBody in that submodule).
  let F:=P.flash n
  let S:= ({nodeC F.birth}:Finset Cover)
  let T:= ({nodeC F.death}:Finset Cover)
  have d:S⊆F.patio := Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchBorn F)
  have g:T⊆F.patio := Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchGone F)
  change P.frontMat Z n ∈ P.sensing (P.measureStencil n) s Z.2
  exact Submodule.subset_span (show _∈_ from
    ⟨S,T, F.patio, Finset.union_subset d g, Finset.subset_union_left,
      P.pocket_gap s n e, P.front_charge Z n, P.front_real Z n⟩)

lemma thinString_reflect_senses (e : n > (κ).ℓ) :
    P.Sensor ((P.thinString Z s n).kiss P 3) Z.2 :=
  P.sensor_mirror Z.2 3 _ (P.thinString_senses Z s n e)

variable (F G : SampleDose)

/-- Continuum samples when implementing a height `s` field. `t` always `≥s`.
Here "incoming" is the earlier insertion (support about each earlier center).
These are NOT incoming and outgoing scattering states! -/
def thinOutgoing : P.Test := P.prepared t (P.thinString Z s n) F
def thinIncoming : P.Test := P.prepared t ((P.thinString Z s n).kiss P 3) F
lemma thinGaugeInvariant : P.thinOutgoing Z s n t F ∈ enclave κ ∧
    P.thinIncoming Z s n t F ∈ enclave κ := ⟨P.prepared_color t _ F, P.prepared_color t _ F⟩

/-- The precise comparison in our engineering of this experiment. Equivalent to
`Comparison` which is the unique product from the two indicated pure marginals.
Ward and unitality kept for explicit downstream ease. -/
structure SameRawProduct (x:P.Spectrum0 3) (X:P.Test →ₗ[ℂ] ℂ) : Prop where
  marginal : Comparison P.calibration (P.singleState 3 t x) X
  one : X 1=1
  gauge : GaugeWard P.calibration X
  matter : MatterWard P.calibration X

lemma SameRawProduct_iff (x:P.Spectrum0 3) (X:P.Test →ₗ[ℂ] ℂ) :
    P.SameRawProduct t x X ↔ Comparison P.calibration (P.singleState 3 t x) X := by
  obtain ⟨Y,h,p,q,v⟩:= P.comparator t x
  exact ⟨fun g=> g.marginal, fun g=> (Comparison.unique _ _ g h) ▸ (⟨h,p,q,v⟩ : P.SameRawProduct t x Y)⟩

lemma thin_comparator (x:P.Spectrum0 3) : ∃! X:P.Test →ₗ[ℂ] ℂ, P.SameRawProduct t x X := by
  obtain ⟨X,h,p,q,v⟩ := P.comparator t x
  exact ⟨X, ⟨h,p,q,v⟩, fun Y hy=> Comparison.unique _ _ (SameRawProduct.marginal hy) h⟩

lemma thin_zero_single (X:P.Test →ₗ[ℂ] ℂ) (p:Factors κ X) (u:MatterWard κ X ∨ GaugeWard κ X)
    (B:P.Apron)(W:Bool)(h:P.Sensor B W)(e:B.s ≤ t) : X (P.prepared t B F)=0 := by
  unfold prepared
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _=> ?_
  rw [map_smul]
  have ht:= P.msplit W t p u B i h e [] (by simp)
  have hx:X (P.issuing t B i) = 0 := by simpa only [List.map_nil,List.prod_nil,mul_one] using ht
  rw [hx,smul_zero]

/-- Predict the WHOLE pair, even though each of the two cells houses a locally
contracted gauge--matter insertion. This isn't multiplying one-body forecasts!
This also works when incoming and outgoing probes come from different birth
heights and lengths; the pair prediction is made using the same two marginal
prices at *t*, guaranteed by `thin_comparator` on the same state. -/
lemma thin_factor_pays (s' n' : ℕ) (e:s ≤ t) (e':s' ≤ t) (p:n>(κ).ℓ) (p':n'>(κ).ℓ)
    (d:Disjoint (P.spacePrice ((P.thinString Z s n).kiss P 3) F) (P.spacePrice (P.thinString W s' n') G))
    (X:P.Test →ₗ[ℂ] ℂ) (v:Factors κ X) (h:MatterWard κ X ∨ GaugeWard κ X) :
    X (P.thinIncoming Z s n t F) = 0 ∧ X (P.thinOutgoing W s' n' t G) = 0 ∧
    X (P.thinIncoming Z s n t F * P.thinOutgoing W s' n' t G) = 0 :=
  ⟨P.thin_zero_single t F X v h _ _ (P.thinString_reflect_senses Z s n p) e,
   P.thin_zero_single t G X v h _ _ (P.thinString_senses W s' n' p') e',
   P.split_test t _ F _ G d e e' _ (P.thinString_reflect_senses Z s n p) X v h⟩

/-- At one `ε` budget: all pose bills on every `t≥s` for this apron honor a
box of radius `ε`, uniformly even in center. Includes the separately paid *gauge
invariance* of every insertion around a center. This is not a budget just on
support of test FUNCTIONS. Coordinates as in `Six.SupportPrice` (level-zero MATTER
spacing physical unit). -/
def ThinIntrinsic (A:P.Apron) (ε:ℝ) : Prop := ∀ t:ℕ, A.s ≤ t → ∀ i: Cover,
  P.issuing t A i ∈ enclave P.calibration ∧
  P.issuing t A i ∈ bay P.calibration (P.plotSet t A i) true ∧
  P.pinFoot t (P.plotSet t A i) ⊆ Metric.ball (P.meshPose t i) ε

-- `Vantage` distance is sup norm.
lemma thinStage_support (A:P.Apron) (ε:ℝ) (e:0<ε) (p:∀ j,A.realWidth P j<ε) :
    P.ThinIntrinsic A ε := by
  intro t ht k
  refine ⟨P.issuing_color t k A, P.issuing_support t k A, ?_⟩
  apply Set.Subset.trans (P.inside_now t k A ht)
  intro i hi
  apply (dist_pi_lt_iff e).mpr
  intro j
  exact lt_of_le_of_lt (hi j) (p j)

variable {P} {K:P.Register} {c r:ℕ→ℕ} {x:P.Spectrum0 3}
lemma thin_widths (H:P.Transmission x c r) :
    ∀ ε>0, ∀ᶠ i:ℕ in atTop, ∀ (Z:Lead.Clan),
    P.ThinIntrinsic (P.thinString Z (c i) (r i)) ε ∧
    P.ThinIntrinsic ((P.thinString Z (c i) (r i)).kiss P 3) ε := by
  intro ε e
  filter_upwards [eventually_all.mpr fun j:Axis=> (H.widths j).eventually (gt_mem_nhds e)]
    with i hi
  intro Z
  exact ⟨P.thinStage_support _ _ e hi,P.thinStage_support _ _ e hi⟩

lemma thin_inside_boxes {X Y : Doorway}
    (H:P.Transmission x c r) (p:tsupport F.val ⊆ X.spare.invites)
    (u:tsupport G.val ⊆ Y.spare.invites) :
    ∀ᶠ i:ℕ in atTop, ∀ (Z:Lead.Clan),
    (P.spacePrice ((P.thinString Z (c i) (r i)).kiss P 3) F ⊆ X.invites) ∧
    (P.spacePrice (P.thinString Z (c i) (r i)) G ⊆ Y.invites) := by
  filter_upwards [X.spareCosts (fun i=> P.probeWidth (c i) (r i)) H.widths,
     Y.spareCosts (fun i=> P.probeWidth (c i) (r i)) H.widths] with i h h'
  intro Z
  exact ⟨bounded_within _ F p h, bounded_within _ G u h'⟩
#print axioms thinString_eval
#print axioms thin_comparator
#print axioms thin_factor_pays
#print axioms thin_widths
#print axioms thin_inside_boxes
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
