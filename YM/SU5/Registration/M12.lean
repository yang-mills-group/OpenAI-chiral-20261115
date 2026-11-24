import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.M10
import YM.SU5.Registration.Sectors.Polity
import YM.SU5.Registration.Ink.RegEu

import YM.SU5.Registration.M11
import YM.SU5.Registration.LineUp.SharpRaster
import YM.SU5.Registration.LineUp.Assembly
/-!
 # M12. Advance toward positive-energy rel field map from ONLY a fresh
 angular estimate (and choice of labels representing spins & adjoint law) on the M10 sector.
 
 Does *not* assert these hypotheses available. All M5-11 results separate.
 Need still derive commutation from this. Does include all-through-ties Eu.
 Apply parameterized on one possible family extended to the budget price, theorem
 `Spine.relatable`. To retain all six fixed F/U votes & actual W as in FullPrismLab and
 M4Tuple, can choose proposed grant whose family includes ONLY the centerpiece A (besides any genuinely
 new gauges/mixes) AT THIS x . Then even THIS sector relativity
 applies to the instrument map as fully local retests: `P.attachTicket`, `P.lineups_current`, `P.pulseTicket`.
 Combining contains actual LI at these readings & ground. Does not change the M4 elected parameters. See checkpoint docs about exact scope of interaction and bare parameters. No claims here of interacting theory.
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
open SatinWFixed Carton WView HelioRoof
-- hypothesis used further on Hpt rotations/covariant operator fields. 
section economy
variable {I:Type*}(B':I→P.Swatch)(tp:∀ i,(B' i).WPermit x 3) (R':Courts (epaulets I))
variable (S':P.RasterPrice x B' R') (h':R'.Parley (r_star I))
local notation "Y₀"=> P.store x B' tp
local notation "E"=> epaulets I
local notation "T"=> (P.store x B' tp).joinT
local notation "SE" => P.registeredField x A c r n w
include S' h' F₀
/-- Positive energy representation, orientation criterion EXACTLY p and R'. Can still add locality/drummest estimates. -/
theorem relatable (φ:InkWaves (epaulets I))(Rz:WView (epaulets I))(E0:InkPort (Y₀) φ Rz) :
 R'.Carriage φ ∧ Rz.conical ∧ ∃ «V'»:Boundary.Action (Y₀).station,
  (Y₀).Joins R' «V'» ∧
  «V'».orbit=T ∧ «V'».orbit.Spectrum ((Y₀).joinT.P) ∧
  (T).P.region Mink.coneᶜ=0 ∧ (∀ v:(Y₀).station,(∀ k:E4, (T).translation k v=v)→ v∈ Submodule.span ℂ {(Y₀).engaged []}) :=by
 let h:= (P.raster_carriages x B' tp φ Rz E0 R R').1 S'; obtain ⟨V₁,e⟩:= (Y₀).unites (r_star I) R' φ Rz E0 (P.preserves_income x B' tp) h h'; exact ⟨h,on_shape (InkPort.fades E0 h) E0.half_price,V₁,e,(Y₀).unanimous_time R' V₁ e,(Y₀).real_pvm R' V₁ e,(Y₀).real_cone R' V₁ e,fun v z=> P.solo_point x K c r R i₀ F U A n w V g _ X Y Z F₀ B' tp v z⟩
 -- _ char proof tune h overshadow
omit S' h' F₀
variable (q:P.CapBacked x A c r n w)(pr:P.OverM4 x c r F U A n w V Y Z q)
-- parent margin even if R uncleared. Allows not requiring W spin multiplets; as always can ALSO choose intrinsic ink permits carrying the direct stencils as part of R's inputs. in either case W Eu does mean engineered time stencil, not covariantly time-component-only scalar.
variable (i:I)
noncomputable def sortTicket (j:Instrument)(f:Test4) : MarkType (epaulets I):=
 (pupil (i,j.2),if j.2 then stageTest w j.1 f else bar (stageTest w j.1 (bar f))) -- `p` positional Polar.B
variable (t:B' i = Swatch.ordinary A)
include F₀ p T' t
lemma attachTicket (j:Instrument)(f:Test4) :
 (Y₀).operator (sortTicket w i j f).1 (sortTicket w i j f).2= SE q j f := by
 let ht:=P.interviewed x K c r R i₀ F U A n w V g h X Y Z F₀ p T'
 have Uv: (Zq).WPermit x 3 := P.parent_income x A p;
 rcases j with ⟨a,b⟩; cases b
 · rw [(ht a Uv f q).2]; -- j not definitional? 
   change (Y₀).operator (pupil (i,false)) (bar (stageTest w a (bar f)))=_; rw [P.pupil_field]; congr 2; -- spin school turn
   exact congrArg (fun Z:P.Swatch=> Z.turn 3) t
 rw [(ht a Uv f q).1]; change (Y₀).operator (pupil (i,true)) (stageTest w a f)=_; rw [P.pupil_field]; congr
-- support retest (no Claim labels individually scalar under boosts)
omit F₀ p T' t
lemma retest_ticket (j:Instrument)(f:Test4): tsupport (sortTicket w i j f).2 ⊆ tsupport f:=by
 rcases j with ⟨a,b⟩; cases b; · exact sig_bar_support w a f
 exact sig_support w a f
include F₀ p T' t
local notation "sale"=> sortTicket w i
lemma polar_hand (j:Instrument)(f:Test4)(v:(Y₀).citizen) : (Y₀).live ( (Y₀).oneOp (sale j f) v) = SE q j f ((Y₀).live v) :=by
 rw [Carton.issued]; rw [← attachTicket P x K c r R i₀ F U A n w V g h X Y Z F₀ p T' B' tp q i t]; rfl
include pr
-- all psi & Z even if not transferring numeric F/U test functions to Schwartz-in-Minkowski.
lemma aimed (a:κ)(f:Test4) : ((Y₀).engaged [sale (positiveLabel a) f]).1=Y a f:=by
 change ((Y₀).operator (sale _ _).1 (sale _ _).2 Ω).val= _; rw [P.attachTicket x K c r R i₀ F U A n w V g h X Y Z F₀ p T' B' tp q i t]; exact pr.actualField ..
lemma lineups_current (φ:InkWaves (epaulets I))(Rz:WView (epaulets I))(E0:InkPort (Y₀) φ Rz)(a b: κ)(f f':Test4) : Rz.expect [sale (negativeLabel a) (bar f), sale (positiveLabel b) f']= Z a b (tieAt f f'):=by
 rw [E0.real_value];
 let xNeg:= sale (negativeLabel a) (bar f); let xPos:= sale (positiveLabel b) f'; change inner ℂ ζ ( (Y₀).operator xNeg.1 xNeg.2 ((Y₀).operator xPos.1 xPos.2 Ω)).val= _
 have Z' (k:Instrument)(f:Test4): (Y₀).operator (sortTicket w i k f).1 (sortTicket w i k f).2= SE q k f := P.attachTicket x K c r R i₀ F U A n w V g h X Y Z F₀ p T' B' tp q i t k f
 unfold xNeg xPos; rw [Z',Z']; exact (pr.actualDistribution a b f f').symm
lemma pulseTicket : ∃ f: Test4, LinearIndependent ℂ (fun a=> (Y₀).engaged [sale (positiveLabel a) f]):=by
 obtain ⟨f,hf⟩:= F₀.zeroHeat.sense; let Vz:= fun a=> (Y₀).engaged [sale (positiveLabel a) f]; have he(a): Y a f=(Y₀).pointShelf.subtype (Vz a):= (P.aimed x K c r R i₀ F U A n w V g h X Y Z F₀ p T' B' tp q pr i t a f).symm; simp_rw [he] at hf; exact ⟨f, LinearIndependent.of_comp (Y₀).pointShelf.subtype hf⟩
end economy
#check @Spine.planetary_sunlit -- gives F₀ & parent_income & overM4 & anchor smears unchanged. at least one family *without* relat.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.relatable
#print axioms Spine.lineups_current
#print axioms Spine.pulseTicket
#print axioms Spine.polar_hand
