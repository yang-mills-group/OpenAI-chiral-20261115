import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.M9
import YM.SU5.Registration.Ink.RegEu

/-!
 # M10: InkWaves & Carton over The ready field jets for the interaction probes on the same character.

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

/- Register at least the whole six group and parent separately.
 Note that these two-point distributions on Test4^2 are priced relative to `(tieAt …)`
 in M5/; `actual_value` below even pins the cross calculus on each such audience member,
 and still have unique W distributions on the entire joint test space.
-/
open SatinWFixed
abbrev M10Lead:= κ ⊕ Unit
abbrev FastSales : M10Lead → P.Swatch:= Sum.elim (fun a=> (Zw a)) (fun _=>Zq)
variable (q:P.CapBacked x A c r n w)(pr:P.OverM4 x c r F U A n w V Y Z q)
variable (V₀:(Swatch.ordinary A).WPermit x 3)
local notation "W₀"=> P.FastSales c r A n w
include q V₀
lemma qualified10 : ∀ i,(P.FastSales c r A n w i).WPermit x 3:=by
 rintro (a|e)
 · exact P.affine_cap x _ (q a)
 exact V₀
-- include q V₀; note order FastSales c r A n w from variable list? `A` after F U; alphabet Lean basic.
noncomputable abbrev directs := P.store x W₀ (P.qualified10 x c r A n w q V₀)
omit q V₀
noncomputable abbrev represents10 (a: Lead.Clan) (b:Bool) := pupil ((Sum.inl a:M10Lead), b)
include q V₀
lemma actual_field (j:Instrument) : (P.directs x c r A n w q V₀).operator (represents10 j.1 j.2)= P.registeredField x A c r n w q j:= by
 rcases j with ⟨a,i⟩; cases i
 · refine (P.pupil_field x W₀ (P.qualified10 x c r A n w q V₀) ((Sum.inl a : M10Lead),false)).trans (?_); -- Kiss literally
   exact (P.turn_as_kiss x (W a) (P.cap_partner x _ (q a)) ((P.affine_cap x _ (q a)).reflector ..)).symm
 exact (P.pupil_field x W₀ (P.qualified10 x c r A n w q V₀) ((Sum.inl a:M10Lead), true)).trans (P.point_published x (W a) (P.affine_cap x _ (q a)) (q a))
local notation "D₀"=> P.directs x c r A n w q V₀
variable (F' : InkWaves (epaulets M10Lead))(W'': WView (epaulets M10Lead))(k:InkPort (P.directs x c r A n w q V₀) F' W'')
include pr
lemma vacuum_current (a:κ)(f:Test4) : ((D₀).row [(represents10 a true,f)]).1= Y a f:=by
 change ((D₀).operator (represents10 a true) f (Ω)).val= _
 rw [P.actual_field x c r A n w q V₀ (a,true)]; exact pr.actualField ..
include k
lemma actual_distribution (a b:Lead.Clan)(f g:Test4) : W''.expect [(represents10 a false, bar f),(represents10 b true,g)] = Z a b (tieAt f g):=by
 rw [k.real_value];
 change inner ℂ ζ ( (D₀).operator (represents10 a false) (bar f) ((D₀).operator (represents10 b true) g Ω)).val=_
 rw [P.actual_field x c r A n w q V₀ (a,false),P.actual_field x c r A n w q V₀ (b,true)]; exact (pr.actualDistribution a b f g).symm
omit pr k
lemma enables10 : ∃ R:InkWaves (epaulets M10Lead), ∃ Ww: WView (epaulets M10Lead),
  InkPort (D₀) R Ww ∧ Remembers (D₀) (r_star M10Lead) ∧ Analysis.NNKernel (Ww.kernel (r_star M10Lead)):=by
 obtain ⟨F',W₁,t⟩:= InkPort.obtainF D₀; let h:=P.preserves_income x W₀ (P.qualified10 x c r A n w q V₀); exact ⟨F',W₁,t,h,t.true_pos (r_star M10Lead) h⟩
omit q V₀
-- the pupil at kindergarten. can use M9's `interviewed` with it. availability
include p
lemma parent_income : (Swatch.ordinary A).WPermit x 3:= ((p.purchase 3 []).2 x) -- [] of A.pivot; defeq?
omit p
#check @Spine.planetary_sunlit -- outputs cumulative.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.parent_income
#print axioms Spine.actual_field
#print axioms Spine.vacuum_current
#print axioms Spine.actual_distribution
#print axioms Spine.enables10
