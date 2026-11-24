import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.Postcards.Receivables
/-! # M14: from small rotational estimate in Mean instead of elected M.

 See user §XI-XVIII and proof M14 doc. Reduces costs to
 a small tending family of rotations & (116) extension already on this K.
 M13 all conclusions inherit (and every limitation), and actual F/U kept exactly there.
 No claim of already having that rotational estimate. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
variable (K : P.Register) (c r : ℕ→ℕ) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose) (A : ℕ→P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4→L[ℂ] (P.ManyF 3 (P.advocate 3 x 3))) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4)
local notation "Μ" => M4Tuple P K c r x R i₀ F U A n w V g h X Y Z
local notation "Λ" => P.profilesZ x V w
local notation "ρ" => 𝓝[>] (0:ℝ≥0)
local notation "B" => P.pointBill x A c r n w
local notation "W" a:max => P.soldTrumpet A c r n w a
local notation "G₀" a:max => P.gaugeTrumpet A c r n w a
variable (F₀: M4Tuple P K c r x R i₀ F U A n w V g h X Y Z)
universe ν
variable (p:PlanetaryG.{0} P A)(T':∀ x:P.Spectrum0 3,P.Guest x c r A n)
open Swatch
local notation "aK"=> P.SalonBasis A
local notation "Zq"=> Swatch.ordinary A
local notation "Zw" a:max=> Swatch.ordinary (W a)
local notation "Zg" a:max=> Swatch.ordinary (G₀ a)
local notation "Zl" j:max=> Swatch.ordinary (P.registeredStamp A c r n w j)
open SatinWFixed Carton WView HelioRoof
-- hypothesis used further on Hpt rotations/covariant operator fields. 
section economy
variable {I:Type*}(B':I→P.Swatch)(tp:∀ i,(B' i).WPermit x 3) (R':Courts (epaulets I))
variable (Uo:P.TravelReady B') (S':P.PostalPrice B' R') (h':R'.Parley (r_star I))
local notation "Y₀"=> P.store x B' tp
local notation "E"=> epaulets I
local notation "T"=> (P.store x B' tp).joinT
include F₀ Uo S' h'
theorem angle_progress (φ:InkWaves (epaulets I))(Rz:WView (epaulets I))(E0:InkPort (Y₀) φ Rz) : P.RasterPrice x B' R' ∧ Rz.conical ∧ Rz.Localizes ∧ R'.Carriage φ ∧ (Palette.ticket Palette.blanket Rz).FullBody φ ∧
 ∃ V':Boundary.Action (Y₀).station,
  (Y₀).Joins R' V' ∧ V'.orbit=T ∧ V'.orbit.Spectrum ((Y₀).joinT.P) ∧
  (T).P.region Mink.coneᶜ=0 ∧ (∀ v:(Y₀).station,(∀ k:E4, (T).translation k v=v)→ v∈ Submodule.span ℂ {(Y₀).engaged []}) ∧
 (∀ (x y:epaulets I)(f g:Test4), Fields.causal f g→ Commute ((Y₀).pointMap x f) ((Y₀).pointMap y g)):= by
 let h₀ := P.sector_receipt x B' K Uo R' S'; exact ⟨h₀,P.all_rooms x K c r R i₀ F U A n w V g h X Y Z F₀ B' tp R' h₀ h' φ Rz E0⟩
omit F₀ Uo S' h'
section noangular
include F₀ p T'
open _root_.YM.SatinWFixed.Passage
lemma setup_region (B₁:I→ P.Swatch)(hz:∀ i, StillCurtain.{0} P 3 (P.SalonBasis A) (B₁ i)): P.TravelReady B₁:=by
 have hv(i:I × Bool): P.school B₁ i∈ Extensions.{0} P 3 (P.SalonBasis A):=by unfold school; split; exact (hz i.1).1; exact (hz i.1).2
 exact ⟨fun i=>(hv i).1,fun n l=> P.salon_paper 3 x A p (Seld.Poin.Each n) _ (fun i=>hv (l i))⟩
lemma town_exists : P.TravelReady (P.FastSales c r A n w) :=by
 apply P.setup_region x K c r R i₀ F U A n w V g h X Y Z F₀ p T'; rintro (a|t)
 · exact (P.punch x K c r R i₀ F U A n w V g h X Y Z F₀ p T' a).1
 exact P.salon_any 3 x A p Zq (P.salon_selected A)
end noangular
include Uo K
open _root_.YM.SatinWFixed.Passage
def narrowCalls (L:Ortho) : Prop:= ∀ i:sizedStep, ampleStep (L.move (Passage.compass i))
variable (φ:P.Spectrum0 3→InkWaves (epaulets I))(Ψ:P.Spectrum0 3→WView (epaulets I))
    (b:∀ x, InkPort (P.store x B' (Uo.along P B' x)) (φ x) (Ψ x))
include b
lemma in_itinerary (L':Ortho)(l t:List (TrainJ (epaulets I)))(f:narrowCalls L')(a:Auction l)(v:Auction t) (d:E4)(y:SweepAhead (turnSpec (r_star I) l) t d) :
 Tendsto (touringCosts (P.pillars 3) φ (turnSpec (r_star I) l) t d (L'.move ∘ Passage.compass)) atTop (𝓝 (inkCross (P.pillars 3) φ l t)):= by
 let t':=P.register_album B' K Uo Ψ φ b;
 rw [inkCross_corner _ l t t' a]
 exact (t'.clusters_any (L'.move ∘ Passage.compass) f (compact_turn Passage.compass compact_cost L') (salient_mirror _ a (r_star I)) v y)
end economy
#check @Spine.planetary_sunlit
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.town_exists
#print axioms Spine.angle_progress
#print axioms Spine.in_itinerary
#check Spine.in_itinerary
