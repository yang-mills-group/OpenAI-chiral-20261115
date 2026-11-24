import YM.SU5.MacroSix.Ledger
import YM.SU5.Relativistic.Preparing

/-! # Selecting *this* x with the far detector (optional ratio reading)

Although the sector readings are already defined & the question's elected regime
is to measure at *that* prescription, we verify they also price a limit of
**signed** insertions on the trajectory. This is NOT a convergence of the fixed unmodified
Satin (``many'' or ``mixed'') label's sharp answers alone to these in the one component.
Poll on P. Selector can be chosen on ANY x at the outset, here we use just the x paying
all requirements and don't assert that such a far detector belongs to some UV inventory
of fixed/even stencil tests.

We adapt the supplied `Reconstruction.prepares` (Preparing.lean)—same far detector method,
using THAT boundary apparatus, to the `Spine.Spectrum0` point (even the choice of Arena
same here). It applies to any axis, though no price to convert this detector to another
here. Limit is for every fixed label; regulator heights/prices stay inside, row and orbit
calls via Exhibition and its cone.
-/

set_option autoImplicit false
set_option maxHeartbeats 470000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Reconstruction Tapestry.Altitude Tapestry.Exhibition
open _root_.YM.OS.Ground TopologicalSpace
namespace Spine
variable (P : Spine) (R : P.Register) (j : Axis) (x : P.Spectrum0 j)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "K" => P.calibration
local notation "H" => P.large
local notation "G" => P.groundHil j
local notation "Q'" => P.projection
local notation "D" => P.talks R
local notation "ω" => P.groundZero j
local notation "φ" => (P.compressionAlgebra j).subtype
local notation "Ξ" => P.Effect
local notation "F'" => P.spirits R j x

include R
private lemma peGroundready :
    ∃ u : ℕ → P.vacuum j, (∀ i, ‖u i‖=1) ∧ (∀ a : P.Ensemble j,
      Tendsto (fun i ↦ inner ℂ (u i) (a.val (u i))) atTop (𝓝 (P.chi j x a))) := by
  letI := P.metricX j R
  letI := TopologicalSpace.metrizableSpaceMetric (P.Spectrum0 j)
  let B : Panes (P.Ensemble j) := { X := P.Spectrum0 j, μ := P.pillars j, character := P.chi j }
  have h : B.Shines G φ ω := by
    exact ⟨P.normalization _, P.pillar_support j R, OS.Ground.bij, view_cont, P.chi_joint j, P.recovery j⟩
  obtain ⟨f,v,e,t⟩ := OS.Ground.Panes.Shines.chosen_at (R:=B) («H»:=G) φ ω h (x : B.X)
  exact ⟨fun i ↦ (f i).val ω,v,t⟩

abbrev Poll := ∀ i : ℕ, Future P.run P.large j i
abbrev pollTicket (p : P.Poll j) (i : ℕ) := (p i).boundary P.run P.large j

lemma detectorChoices : ∃ c : P.Poll j, ∀ v ∈ FiniteGaugeDataPoly P.calibration,
    Tendsto (fun i ↦ vistaTake Y H (P.talks R) (v * P.pollTicket j c i)) atTop
      (𝓝 (P.spirits R j x v)) := by
  obtain ⟨y,p,e⟩:= P.peGroundready R j x
  choose F z using fun i:ℕ=>Future.record Y H P.law P.projection j (P.room j)
    (y i : Tower.Selected.groundRoom Y H (D).univ_ P.history j false (P.room j)) i
    (ε:=propeller i) (by unfold propeller; positivity)
  let ε:= propeller
  refine ⟨F,fun v t ↦ ?_⟩
  obtain ⟨s,u⟩:= curve.mp t
  let f:= vistaFinish Y H s D v
  let c:= P.reading j s f
  obtain ⟨w,r,a,u'⟩:= buys_at Y H D j v s
  let X : (P.Hil j).Op:= P.Box j s (w+w) (by omega) a
  have he:= (P.useSpirit R j x s v u)
  have hx : P.spirits R j x v=P.chi j x c := he.trans rfl
  let p' (i:ℕ): ℂ:= inner ℂ (y i) (c.val (y i))
  have h:Tendsto p' atTop (𝓝 (P.spirits R j x v)):= by rw [hx]; exact e c
  let Z:= fun i=> ε i*‖X‖*(1+ε i) + 1*‖X‖*ε i
  have h': Tendsto ε atTop (𝓝 0):= propeller_fades
  have hq:Tendsto Z atTop (𝓝 0):=by simpa only [zero_mul,zero_add,mul_zero] using (((h'.mul_const ‖X‖).mul (h'.const_add 1)).add (h'.const_mul (1*‖X‖)))
  refine transfer_price Z hq h ?_
  filter_upwards [eventually_ge_atTop w,eventually_ge_atTop s] with i b c'
  let m:= Future.wait Y H j (F i)-P.par.R.L.val^((F i).t-s)*w
  let E':P.Hil j:= P.piece j (F i).t ((F i).irradiant Y H j m)
  let A':P.Hil j:=(y i).val
  have hv: p' i= inner ℂ A' (X A'):= symmetric_box Y H D Q' j v s w r a u' (P.room j) (y i)
  have hk: vistaTake Y H D (v*P.pollTicket j F i)=inner ℂ E' (X E'):=
    Future.actualE Y H D Q' j (F i) (P.room j) r u a u' c' b
  rw [hk,hv]; exact near_inner X E' A' 1 (ε i) (p i).le ((F i).attends Y H P.law Q' j (P.room j) (y i) (z i) m)

-- ratio-level reading. Keep both numerator and denominator notation actual path before selection.
local notation "κ" => vistaTake Y H (P.talks R)
local notation "𝒦" => FiniteGaugeDataPoly P.calibration
local notation "M" a:max b:max => Reconstruction.readingAtTop Y H a b
local notation "μ" x:max => P.period (WedgeStage.vol x)
local notation "η" x:max => P.cutoff (WedgeStage.uv x)
local notation "T" s:max => shorter P.Test s
variable {n : ℕ}
lemma cone_income {s : ℕ} {v : P.Effect} (p : v∈ shorter P.Test s) :
    Tendsto (fun n ↦ Reconstruction.readingAtTop Y H (μ n) (η n) v) followStage
      (𝓝 (vistaTake P.run P.large (P.talks R) v)) :=
  (P.pe_polys R v (curve.mpr ⟨s,p⟩)).congr'
    (((P.talks R).payStage Y H s).mono fun n h ↦ (identifyRevenue Y H _ _ _ p h).2.2)

def RatioOn (c : P.Poll j) (i : ℕ) (v : P.Effect) :=
    vistaTake P.run P.large (P.talks R) (v*P.pollTicket j c i) /
      vistaTake P.run P.large (P.talks R) (P.pollTicket j c i)

-- all queries here: e.g. determine on given test at given t, may take detector to infinity with **test fixed**, inside take detector fixed, regulator purchase thresholds can depend on all those choices. eventual enough for any such v.
variable (c : P.Poll j)
structure Selects : Prop where
  denominator_tends : Tendsto (fun i ↦ vistaTake P.run P.large (P.talks R) (P.pollTicket j c i)) atTop (𝓝 1)
  poll (v : P.Effect) (s : ℕ) (h : v ∈ shorter P.Test s) :
    Tendsto (fun i ↦ P.RatioOn R j c i v) atTop (𝓝 (P.spirits R j x v)) ∧
    (∀ᶠ i : ℕ in atTop,
      -- v, and this detector. not uniformly for all i
      s≤ (c i).t ∧ vistaTake Y H (P.talks R) (P.pollTicket j c i)≠0 ∧
      (∀ᶠ n in followStage, Pay Y (c i).t (μ n) (η n) ∧
        Reconstruction.readingAtTop Y H (μ n) (η n) (P.pollTicket j c i) ≠ 0) ∧
      Tendsto (fun n ↦ (M (μ n) (η n)) (v*P.pollTicket j c i) /
        (M (μ n) (η n)) (P.pollTicket j c i)) followStage (𝓝 (P.RatioOn R j c i v)))

lemma Selects.forJourneyPath (C : P.Selects R j x c) (v : P.Effect)(s : ℕ) (p : v ∈ shorter P.Test s) :
    ∀ᶠ i : ℕ in atTop, s≤ (c i).t ∧ Tendsto (fun n:ℕ ↦ let a:= P.period (P.projection.rows n); let b:= P.cutoff (P.projection.columns n)
      (M a b) (v*P.pollTicket j c i) / (M a b) (P.pollTicket j c i)) atTop (𝓝 (P.RatioOn R j c i v)) := by
  filter_upwards [(C.poll v s p).2] with i h
  have ht := h.2.2.2.comp (P.all_heights_here R)
  refine ⟨h.1,ht.congr fun x ↦ ?_⟩
  rfl

lemma detectorSelect : ∃ c : P.Poll j, P.Selects R j x c := by
  obtain ⟨c,p⟩:= P.detectorChoices R j x
  let F i : P.Effect:= P.pollTicket j c i
  have hv: Tendsto (fun i ↦ vistaTake Y H D (P.pollTicket j c i)) atTop (𝓝 1):= by simpa only [one_mul,P.spirit_one] using p 1 (Subalgebra.one_mem _)
  refine ⟨c,hv,fun v s h ↦ ?_⟩
  constructor
  · have he:= (p v (curve.mpr ⟨s,h⟩)).div hv one_ne_zero; rw [div_one] at he; exact he
  filter_upwards [eventually_ge_atTop s,hv.eventually_ne one_ne_zero] with i t k
  have hp:s≤(c i).t:= t.trans (c i).arrival
  have he:F i ∈ shorter P.Test (c i).t:= short_pinhole _ _
  have ht:= P.cone_income R he
  exact ⟨hp,k,((D).payStage Y H (c i).t).and (ht.eventually_ne k),(P.cone_income R
    ((shorter P.Test (c i).t).mul_mem (Altitude.climbs P.Test hp h) he)).div ht k⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms detectorChoices
#print axioms detectorSelect
#print axioms Selects.forJourneyPath
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
