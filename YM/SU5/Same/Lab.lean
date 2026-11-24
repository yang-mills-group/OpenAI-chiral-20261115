import SU5SatinVerifiedNovember6
import YM.SU5.Same.TicketsPrism

/-!
# Public application M1. The operator and GNS/vacuum step on the actual CP18 stencils

M1 concludes the (full H) **tape/stamp** ket & operator registrations, identifies norm
limits with the Glasshouse Hilbert space version, and verifies susceptibility of CP27
criterion on those operators in the posed regions in physical units. Those are in the open
*original* boxes, and one can even choose the supports also inside any
existing Azure locator for the fixed Mark at that consultation. One duration d
is common across boxes, schedules, stencil (large enough to host the region
for actual CP27 registration, NOT a claim of removing the heat pads).

Records exact registration and cone estimate remaining at this point on that
same character, and exhibits consequence for Wick programs on these very Supports.
No Section XI operator bound through unpadding, or unconditional purchase of
those estimates asserted here. The preserved comparator is the operational one.
-/
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
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

variable (P : Spine) (x : P.Spectrum0 3) (A : ℕ → P.Apron) (c r n : ℕ → ℕ)
    (w : Lead.Clan → Prism) (F U : SampleDose)
local notation "j" => (3:Axis)
local notation "C'" => reviewEarlierBox
local notation "B'" => reviewLaterBox
local notation "W₁" a:max i:max => (((P.soldTrumpet A c r n w) a i).kiss P 3)
local notation "W₂" b:max i:max => ((P.soldTrumpet A c r n w) b i)
local notation "f₁" t:max a:max i:max => P.prepared t (W₁ a i) F
local notation "f₂" t:max a:max i:max => P.prepared t (W₂ a i) U
local notation "ξ" z:max => P.advocate 3 x z
local notation "K" => P.calibration
local notation "S" => P.ColorHil j (ξ j)
local notation "S'" => P.ManyF j (ξ j)
local notation "R" => P.glassSpace 3 x j
local notation "X₂" => P.glassFort 3 x j
local notation "Ω" => P.glassVac 3 x j
local notation "Ω₂" => P.glassHeaven 3 x j
local notation "ι₂" => P.fortIn 3 x j
local notation "Λ₀" => P.glasshouseCharacter 3 x
local notation "λ₁" => opCarries P.run P.large P.law P.projection 3 (P.room 3) (P.glassAxis 3 x 3)
local notation "Hc" => Crease.Charter P.run P.large P.law P.projection P.room j Λ₀ j
local notation "Wc" => Crease.floor P.run P.large P.law P.projection P.room j Λ₀ j
local notation "K!" => P.toFort 3 x j
local notation "J!" => P.toGlass 3 x j
variable (T' : P.HandleWith x c r A n)
    (V : ∀ z : Axis, List Axis → ℝ → P.ColorHil z (P.advocate 3 x z))
    (d : marks (timeMesh P.par))
local notation "m!" i:max => c (n i)
local notation "X!" z:max => DoseTravel.beam (S') F (P.earlierProfile x V w 1 z)
local notation "Y!" z:max => DoseTravel.beam (S') U (P.laterProfile x V w 1 z)
local notation "w!" => BoostBacking P.run P.large P.law P.projection P.room j Λ₀
local notation "r!" => Crease.Registered P.run P.large P.law P.projection P.room j Λ₀ j

/-- The necessary WOT estimates at fixed CP18 stencils discussed in the reconstruction
proposal. Π not presumed invertible; Π₂ can forget costs. In the purchase under
BoostBacking (see theorem), no costs forgotten even in the KET test. -/
def LocalScriptReady (Q : Set RSpace) (A' : (P.glassSpace 3 x j).Op) : Prop :=
    ∃ M' : ℕ → ℂ → (X₂).Op, Hc (Crease.panelFace j Q) d (λ₁ A') M' ∧
      Anvil.Limited atTop (fun i => M' i 1) (λ₁ A') ∧
      (∀ p : R, Tendsto (fun i => inner ℂ p (ι₂ ((M' i 1) Ω₂))) atTop
        (𝓝 (inner ℂ p (A' Ω)))) ∧
      ∀ (i : ℕ) (η : ℝ), Lens.stroke (P.glassSeason 3 x j) (M' i) η 0 (Real.toNNReal (d:ℝ)) ∈
        Wc (Lens.period j (Crease.panelFace j Q) η 0 (Real.toNNReal (d:ℝ)))

structure LabRegistry : Prop where
  lengthEnough : 2 ≤ (d : ℝ)
  margin : ∃ v : ℝ, 0 < v ∧ LoudMargin (P.readPrism x V w 1 F U) v ∧
    ∀ᶠ i in atTop, ∀ t : ℕ, m! i ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) v
  locators : ∀ᶠ i in atTop, ∀ t : ℕ, m! i ≤ t → ∀ a b : Lead.Clan,
    ∃ (O M' : (R).Op) (X Y : Finset Cover),
      P.GlassTicketPair x A c r n w F U T' a b d i t X Y O M'
  across (a b : Lead.Clan) (t : ℕ → ℕ) (O M' : ℕ → (R).Op) (p : ∀ᶠ i in atTop, m! i ≤ t i)
      (u : ∀ᶠ i in atTop,
        ∃ X Y, P.GlassTicketPair x A c r n w F U T' a b d i (t i) X Y (O i) (M' i)) :
    Tendsto (fun i => O i Ω) atTop (𝓝 (ι₂ (K! (X! a)))) ∧
    Tendsto (fun i => M' i Ω) atTop (𝓝 (ι₂ (K! (Y! b)))) ∧
    inner ℂ (ι₂ (K! (X! a))) (ι₂ (K! (Y! b))) = P.readPrism x V w 1 F U a b
  clocks (z : Axis) (i : ℕ) (f : P.Test) (p : P.birthF z i f) :
    P.toGlass 3 x z (P.viewF z (P.advocate 3 x z) i p) =
      physicalKet P.run P.large P.law P.projection z (P.room z) (P.glassAxis 3 x z)
        (enclose P.run P.large P.projection (flank z 0) true i ⟨f,(P.birthF_iff_glass z i f).1 p⟩)
  angularRegistration (p : ℝ) (q : ℝ) (v : 0 ≤ p) (u : 0 < q) :
    w! ↔ StageT P.run P.large P.law P.projection P.room j Λ₀ q p
  sectorForward (z : Axis) (p : w!) :
    P.Viewers z (ξ z) = ⊤ ∧ ConePrice.Forward (P.seasons z (ξ z))
  wickYet (a b : Lead.Clan) (i t : ℕ) (O M' : (R).Op) (X Y : Finset Cover)
      (D : P.GlassTicketPair x A c r n w F U T' a b d i t X Y O M') (backing : w!) (estimate : r!) :
    P.LocalScriptReady x d (mirrorE j 0 '' (P.pinFoot t X)) O ∧ P.LocalScriptReady x d (P.pinFoot t Y) M'

lemma registerMatched (g h s k : ℕ) (K' : P.Register) (D : P.FullPrismLab x A c r n w V g h T' 1 F U reviewEarlierBox reviewLaterBox s k K')
    (p : 2 ≤ (d : ℝ)) : P.LabRegistry x A c r n w F U T' V d := by
  refine {
    lengthEnough := p
    margin := P.fullPrism_azure_margin x A c r n w V g h T' F U D
    locators := P.glassPermit_all x A c r n w F U T' V g h D d p
    across := fun a b t O M' p u => P.glassPair_limit x A c r n w F U T' V g h D d t a b O M' p u
    clocks := fun z i f p => (P.toGlass_view 3 x z i p).trans (P.glassBud_physicalKet 3 x z i p)
    angularRegistration := fun p q v u => (real_boost_purchase P.run P.large P.law P.projection P.room j Λ₀ v u).symm
    sectorForward := fun z v => ⟨(P.glassPresent_iff 3 x z).1 (v.present z), (P.glassForward_iff 3 x z).1 (v.forward z)⟩
    wickYet := ?_
  }
  intro a b i t O M' X Y E h g
  let p' : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_two p
  let W := P.glasshouseEnclosure_onSelectedCharacter x j h g
  have ht := E.leftMark.program p' ((P.pinFoot_isCompact X t).image (mirrorE_origin_continuous j)) h W
  have hu := E.rightMark.program p' (P.pinFoot_isCompact Y t) h W
  rw [E.leftMark.hit] at ht
  rw [E.rightMark.hit] at hu
  exact ⟨ht,hu⟩

/-- UNCONDITIONAL Application at the exact CP18 experiment; criteria with open inputs
are explicitly inside LabRegistry (not unconditional payment). -/
theorem exists_ticketed_lab : ∃ (P : Spine) (K' : P.Register) (c r : ℕ → ℕ)
    (x : P.Spectrum0 3) (J : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
    (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
    Experiment P K' c r x J ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
    tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
    P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K' x (c i₀) (r i₀) 0 F U ∧
    ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
      (V : ∀ z : Axis, List Axis → ℝ → P.ColorHil z (P.advocate 3 x z))
      (g h : ℕ) (T' : P.HandleWith x c r A n),
      P.FullPrismLab x A c r n w V g h T' 1 F U reviewEarlierBox reviewLaterBox
        (c i₀) (r i₀) K' ∧
      ∃ d : marks (timeMesh P.par), P.LabRegistry x A c r n w F U T' V d := by
  obtain ⟨P,K',c,r,x,J,i,F,U,b,e,t,p,q,v,v',h,h',A,n,w,V,g,k,T',D,_⟩ :=
    Spine.exists_disclosed_satin_native_contrast
  obtain ⟨d,hv⟩ := Schedule.very_late (daylight (timeMesh P.par)) (a:=2)
  exact ⟨P,K',c,r,x,J,i,F,U,b,e,t,p,q,v,v',h,h',A,n,w,V,g,k,T',D,d,
    P.registerMatched x A c r n w F U T' V d g k _ _ K' D hv.le⟩

#print axioms exists_ticketed_lab
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
