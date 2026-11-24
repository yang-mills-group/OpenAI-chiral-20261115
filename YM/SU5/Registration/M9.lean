import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.Rasp.UncutStunt
import YM.SU5.Registration.M8
/-!
 # M9: The ready field jets for the interaction probes on the same character.

 Use M8's grant, M7 port and every γ sensor even for W with all arity
 at a funded ordering. This drives a conditional covariance program. NO claim
 to pay its estimates yet. See current milestone doc. Not full existence.
-/
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
variable (p:PlanetaryG.{ν} P A)(T':∀ x:P.Spectrum0 3,P.Guest x c r A n)
open Swatch
local notation "aK"=> P.SalonBasis A
local notation "Zq"=> Swatch.ordinary A
local notation "Zw" a:max=> Swatch.ordinary (W a)
local notation "Zg" a:max=> Swatch.ordinary (G₀ a)
local notation "Zl" j:max=> Swatch.ordinary (P.registeredStamp A c r n w j)
include F₀ p T'
lemma punch (a:Lead.Clan): StillCurtain.{ν} P 3 aK (Zw a) ∧ StillCurtain.{ν} P 3 aK (Zg a):=by
 let p':= salon_any P 3 x A p _ (P.salon_selected A); let v:= P.paidThin x K c r R i₀ F U A n w V g h X Y Z F₀ a; let b:= F₀.lab.then_read.high
 exact ⟨music_stage P x A (aK) p' c r n a X v T' w b, music_gauze P x A (aK) p' c r n a X v w b⟩ -- arg order tune
lemma polar_permit (j:Instrument): Zl j ∈ Extensions.{ν} P 3 aK:=by
 rcases j with ⟨a,j⟩; let t:= (punch P x K c r R i₀ F U A n w V g h X Y Z F₀ p T' a).1; cases j
 · exact (P.ordinary_kiss 3 (W a)) ▸ t.2
 exact t.1
-- partner formula to budget mate; in terms of original M4 f,p all kept. temporal field from its parent. actual kernel computed by `P.issuing_music`.
omit F₀ p T'
lemma turn_as_kiss (Z:ℕ→P.Apron) (u:P.CapReady x (fun i=>(Z i).kiss P 3))(v:((ordinary Z).turn 3).WPermit x 3): P.pointField x (fun i=>(Z i).kiss P 3) u=P.temporalField x 3 _ v:=by
 apply Eq.trans ( (P.point_published x _ (P.affine_cap x _ u) u).symm)
 have he:=P.ordinary_kiss 3 Z; congr; exact he.symm
include F₀ p T'
-- signatures not a new calculation using shifts of the Eu boxes
lemma interviewed (a:Lead.Clan)(U₁:(Zq).WPermit x 3)(f:Test4)(b:P.CapBacked x A c r n w):
     P.registeredField x A c r n w b (positiveLabel a) f=P.temporalField x 3 _ U₁ (stageTest w a f) ∧ P.registeredField x A c r n w b (negativeLabel a) f=P.temporalField x 3 _ (U₁.reflector x 3 Zq) (bar (stageTest w a (bar f))):=by
 let W':= P.affine_cap x _ (b a); let Q:= P.salon_any 3 x A p _ (P.salon_selected A); let hZ:=P.paidThin x K c r R i₀ F U A n w V g h X Y Z F₀ a; let ht:=F₀.lab.then_read.high
 let g':= stageTest w a f; let B':= P.cap_partner x _ (b a); constructor
 · change P.pointField x _ (b a) f= _; rw [← P.point_published x (W a) W']; exact signatureAct P x A (aK) U₁ Q x c r n w a X hZ T' ht W' f
 change P.pointField x _ B' f=_; rw [P.turn_as_kiss x _ B' (W'.reflector x 3 (Zw a))]; exact signature_adj P x A (aK) U₁ Q x c r n w a X hZ T' ht W' f

-- Programme: all mixed readings, license all norm limits from M8's Passport. includes egret_gram on table permits even on all characters & all stencil index. Only in generic poses with all-axis qualifying, E compressed presentations, choose any axis j to project there.
section moments
variable {I:Type ν}(L:List I)(B':I→P.Swatch)
local notation "κ'" => Set.range (fun i:Instrument=> Zl i)
abbrev here_punch (P:Spine)(A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(Y:P.Swatch): Prop:= Y∈P.SalonBasis A ∨ Y∈ Set.range (fun i:Instrument=> ordinary (P.registeredStamp A c r n w i))
lemma punch_all (u:∀ i, P.here_punch A c r n w (B' i)): P.all_desk 3 B' ∧ P.Paper 3 L B':=by
 have Hx(i:I): B' i∈ Extensions.{ν} P 3 aK:= by rcases u i with p₁|p₁; exact (P.salon_any 3 x A p _ p₁).1; obtain ⟨k,h⟩:=p₁; rw [← h]; exact polar_permit P x K c r R i₀ F U A n w V g _ X Y Z F₀ p T' k
 exact ⟨fun i=>(Hx i).1,P.salon_paper 3 x A p L B' Hx⟩
end moments
omit p F₀ T'
-- take THIS grant; with it also get precisely power estimate at G cap from M7 with Living Thesis.
#check @Spine.planetary_sunlit
#print axioms Spine.planetary_sunlit
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.interviewed
#print axioms Spine.punch_all
#print axioms Spine.turn_as_kiss
#print axioms Spine.punch
#print axioms Spine.polar_permit
