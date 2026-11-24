import YM.SU5.Same.PulseObstruction

/-! # On the actual probes. Wick reconstruction cannot identify the raw split prescriptions
(even when decomposing the *same* observables within their prescribed footprints)
as products of their individually registered operators. Each of the two legs is zero. The
product works BEFORE booking, as in the verified measurements. Never an algebra of
these strips with ordinary multiplication of those pieces. Statement applies also to trying
to first book those mark components in CP27 for use as physical fields.

This is one common booking width d (matching other identifications for CP18), on all heights
and apertures priced by this `HandleWith` as ordered; no positive lower bound on needed
component size assumed for these obstruction tests. -/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open Set
open FirstWindows FirstWindows.LightBudget FirstWindows.Chambers
open MacroGrid SatinNucleus SatinJets DoseTravel

variable (P : Spine) (x : P.Spectrum0 3) (A : ℕ → P.Apron) (c r n : ℕ → ℕ)
    (w : Lead.Clan → Prism) (F U : SampleDose) (T' : P.HandleWith x c r A n)
local notation "Y" => P.run
local notation "H" => P.large
local notation "u'" => P.projection
local notation "j" => (3:Axis)
local notation "ν" => P.glassAxis 3 x j
local notation "R" => P.glassSpace 3 x j
local notation "Λ" => P.calibration
local notation "Λ₀" => P.glasshouseCharacter 3 x
local notation "Ω" => P.glassVac 3 x j
local notation "γ" => P.reflectTest j
local notation "Q" a:max i:max => P.soldTrumpet A c r n w a i
local notation "P₁" a:max i:max => (Q a i).kiss P 3
local notation "s!" i:max => c (n i)
local notation "Ψ" i:max t:max a:max => P.prepared t (P₁ a i) F
local notation "Φ" i:max t:max a:max => P.prepared t (Q a i) U
local notation "L" a:max i:max => P.spacePrice (P₁ a i) F
local notation "G" a:max i:max => P.spacePrice (Q a i) U
local notation "N" => timeMesh P.par
variable (d : marks (timeMesh P.par))
local notation "X" => Follows Y H P.law u' j (P.room j) ν
local notation "I" => Chambers.strip j 0 (d:ℝ)
local notation "Λt" t:max => FirstWindows.ticket Y H u' t

variable (i t : ℕ) (a : Lead.Clan)
local notation "L₁" => P.PulseComponent t (L a i)
local notation "L₂" => P.PulseComponent t (G a i)

structure PulseNullBudget (i t : ℕ) (a : Lead.Clan) : Prop where
 planL : ∃ f, P.stitchPlan t (L a i) f (Ψ i t a)
 planR : ∃ f, P.stitchPlan t (G a i) f (Φ i t a)
 earlier (f : P.PulseComponent t (L a i)) : X ((Λt t) (γ f.link)) d 0 ∧ X ((Λt t) (γ f.matter)) d 0
 later (f : P.PulseComponent t (G a i)) : X ((Λt t) f.link) d 0 ∧ X ((Λt t) f.matter) d 0
 total : ∃ (x' y' : (R).Op), X ((Λt t) (γ (Ψ i t a))) d x' ∧ X ((Λt t) (Φ i t a)) d y' ∧
    inner ℂ (x' Ω) (y' Ω) = P.azurePrism x A c r n w F U i t a a ∧
    x' ≠ 0 ∧ y' ≠ 0 ∧ inner ℂ (x' Ω) (y' Ω) ≠ 0

variable (V : ∀ z : Axis,List Axis → ℝ → P.ColorHil z (P.advocate 3 x z))
    (g h : ℕ) {s k : ℕ} {K' : P.Register}
variable (D : P.FullPrismLab x A c r n w V g h T' 1 F U reviewEarlierBox reviewLaterBox s k K')
include D

lemma pulse_components (p : 2 ≤ (d:ℝ)) : ∀ᶠ i : ℕ in atTop, ∀ t : ℕ, s! i ≤ t →
    ∀ a : Lead.Clan, P.PulseNullBudget x A c r n w F U d i t a := by
  obtain ⟨v,hv,_,e⟩ := P.fullPrism_azure_margin x A c r n w V g h T' F U D
  let D' := (lt_of_lt_of_le zero_lt_two p)
  obtain ⟨N0,hn⟩ := eventually_atTop.mp (Chambers.notch_nat_event d D')
  filter_upwards [P.plan_issued x A c r n w V g h T' F U D,
    P.glassPermit_all x A c r n w F U T' V g h D d p,e,D.under_boxes,
    (D.then_read.high.eventually (eventually_ge_atTop N0))] with i t' hX q u b t z a
  obtain ⟨X',Z,W,W',E⟩ := hX t z a a
  have hr := (loud_fullrank (P.azurePrism x A c r n w F U i t) v (q t z) hv).2 a
  have he : inner ℂ (X' Ω) (Z Ω) ≠ 0 := E.paid ▸ hr
  obtain ⟨d0,v0,h'⟩ := hn t (le_trans (show N0 ≤ c (n i) from b) z)
  have endL : mirrorΩ j '' (L a i) ⊆ Chambers.strip j 0 d := by
    rintro _ ⟨y,p',rfl⟩
    obtain ⟨f,g⟩ := ((u a).1 p') j (Set.mem_univ j)
    have h₁ : -2 < y 3 := f
    have h₂ : y 3 < -1 := g
    change 0 ≤ mirrorΩ j y j ∧ mirrorΩ j y j ≤ (d:ℝ)
    rw [show mirrorΩ j y j = - y j from if_pos rfl]; constructor <;> linarith
  have endR : G a i ⊆ Chambers.strip j 0 d := by
    intro y p'
    obtain ⟨f,g⟩ := ((u a).2 p') j (Set.mem_univ j)
    exact ⟨le_trans zero_le_one f.le,g.le.trans p⟩
  refine ⟨(t' t z).first_plan a,(t' t z).second_plan a,fun f=> ?_,fun f => ?_,
    X', Z,E.leftMark.stripOp,E.rightMark.stripOp,E.paid.symm,?_,?_,he⟩
  · rw [←h']
    exact P.pulseOp_earlier_zero x j t d0 f (fun y p'=> (h' ▸ endL p')) v0
  · rw [←h']
    exact P.pulseOp_zero x j t d0 f (fun y p'=> (h' ▸ endR p')) v0
  · intro eq; rw [eq] at he; exact he (inner_zero_left ..)
  intro eq; rw [eq] at he; exact he (inner_zero_right ..)

section obstruction
-- even if the individual representatives are chosen by a different realization, if
-- they are operator-identified at these segments in the same vacuum, must be zero.
variable {P x A c r n w F U i t a d}
omit D
lemma PulseNullBudget.no_bilin (b : P.PulseNullBudget x A c r n w F U d i t a)
    (plan : P.PulseComponent t (P.spacePrice (P₁ a i) F) →₀ ℂ)
    (f g : P.PulseComponent t (P.spacePrice (P₁ a i) F) → (P.glassSpace 3 x j).Op)
    (pair : (u : P.PulseComponent t (P.spacePrice (P₁ a i) F)) →
      (R).Op → (R).Op → (R).Op)
    (u : ∀ u∈plan.support, X ((Λt t) (γ (PulseComponent.link u))) d (f u) ∧
                         X ((Λt t) (γ (PulseComponent.matter u))) d (g u))
    (hz : ∀ u∈plan.support, pair u 0 0=0) :
    ¬ X ((Λt t) (γ (Ψ i t a))) d (∑ u∈plan.support,plan u • pair u (f u) (g u)) := by
  intro h
  obtain ⟨x',y',p,q,_,g',_⟩ := b.total
  apply g'
  rw [unique_op Y H P.law u' j (P.room j) ν _ p h]; apply Finset.sum_eq_zero
  intro v hv
  rw [unique_op Y H P.law u' j (P.room j) ν _ ((u v hv).1) (b.earlier v).1,
    unique_op Y H P.law u' j (P.room j) ν _ ((u v hv).2) (b.earlier v).2,hz v hv,smul_zero]
end obstruction

#print axioms pulse_components
#print axioms PulseNullBudget.no_bilin
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
