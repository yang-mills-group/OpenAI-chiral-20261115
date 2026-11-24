import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.SunDomain

/-!
# Milestone M5 public: energy bounds and registration over M4

This is **not** a Wightman theorem! For the upgraded witness goals read
`the construction notes`; in particular this is a partial result pricing
on these mixed symbols, not other fields a determining-family theorem may
need. The same-template result once `p` arrives on these instruments,
`sold_cap_registers`, removes further padding on fields/operators; does not
grant that input. First theorem applies even without it (radial M4).

Prices of the instruments are Euclidean positives continued; no statement
of same numerical Lorentzian comparison at these actual smears. No spatial
cone estimate needed in these theorems. See guide for next physical purchases.
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
open SatinRegistration
-- the common dense domain. Independently requested Y's all obtainable there
structure HasRapidReceipt : Prop where
  dense : Dense (D : Set (H))
  norm : ‖ζ‖=1
  started (a : Lead.Clan) (f : Test4) (t:ℝ≥0) (h : 0<t):
    (bands (S)).Approaches atTop (fun i=> warm (S) (B (positiveLabel a) t i) f Ω) (gathers (S) f (Λ a t))
  already (a : Lead.Clan) (f : Test4) : Y a f ∈ radial (S)
  unheated (a : Lead.Clan) (f : Test4): (bands (S)).Approaches ρ (fun t=> gathers (S) f (Λ a (t:ℝ))) ⟨Y a f, already a f⟩

variable (H₀ : M4Tuple P K c r x R i₀ F U A n w V g h X Y Z)
include H₀
theorem has_rapid_on_M4 : P.HasRapidReceipt x c r A n w V Y :=
  ⟨(G).grade_dense,P.stone_norm 3 ξ,P.first_stamp_limit x A c r n w V X F U H₀.lab,
    P.stars_live x A c r n w V X F U Y Z H₀.zeroHeat, P.radial_stars x A c r n w V X F U Y Z H₀.lab H₀.zeroHeat⟩
omit H₀
variable (p : P.CapBacked x A c r n w)
local notation "χ" => P.registeredField x A c r n w p
local notation "ℨ" => P.delivery_sold x A c r n w p
local notation "Word" => List (SatinRegistration.Letter Instrument ℕ)
local notation "Φ" a:max t:max i:max => P.prepared t (P.registeredStamp A c r n w (negativeLabel a) i) F
local notation "Ψ" b:max t:max i:max => P.prepared t (P.registeredStamp A c r n w (positiveLabel b) i) U
open SatinRegistration.Letter Grading
open SatinRegistration (Letter)
/-- Compact statement (use `reportPrism` etc on the original Comparator).
Here `Letter.enacts` actually applies the `registeredField`: see `asks`.
Independent heat profiles for the same word allowed. Ask-labels assigned arbitrary
natural tags just to query padding — here symmetric about each insertion, even
asymmetric per `passes_lim` at each step. With `Letter.spend` can maintain or
remove gap heat along either order. Keep PadCharge above every stencil half-width
in the intermediate fixed-pad purchase (holds eventually). These are ordered
**operators on the actual real-sheet H**, not an assertion that for arbitrary
F and poses a finished Mink word gives the regulated Eu grid valuation.
-/
structure OverM4 : Prop where
  receipt : P.HasRapidReceipt x c r A n w V Y
  widthOK (j : Instrument) (s : ℝ≥0) (hs : 0<s) : ∀ᶠ i in atTop, P.priceWidth (P.registeredStamp A c r n w j i)<s
  onDomain (j : Instrument) (f : Test4) : ((bands (S)).asPartial (χ j f)).IsClosable
  priced (j : Instrument) (v : D) : Continuous (fun f : Test4=> (χ j f v).1)
  localAdj (j : Instrument) (f : Test4) (x' y : D) :
    inner ℂ (χ j f x').1 y.1=inner ℂ x'.1 (χ (reverseProbe j) (bar f) y).1
  covarianceT (j : Instrument) (f : Test4) (m : E4) (x' : D) : SatinRegistration.shift (S) m (χ j f x')= χ j (ahead m f) (SatinRegistration.shift (S) m x')
  asks (j : Instrument) (f : Test4) (s : ℕ→ℝ≥0) (i : ℕ) : enacts B ℨ s (Letter.ask j f i)=χ j f
  width (a : Word) (s t : ℕ→ℝ≥0) (h : ∀ i, 0<s i) {X : ℕ→D} {x' : D} (u : (bands (S)).Approaches atTop X x') :
    (bands (S)).Approaches atTop (fun i=> (a.map (buys («S»:=S) B s t i)).prod (X i)) ((a.map (applies B ℨ s t)).prod x')
  through {ι : Type} (l : Filter ι) (a : Word) (T' : ℕ→ℝ≥0) (s t : ι→ℕ→ℝ≥0) (q : ∀ z, Tendsto (fun i=> s i z) l (𝓝[>] 0)) (v : ∀ z, Tendsto (fun i=> t i z) l (𝓝 (T' z))) {X : ι→D} {x' : D} (u : (bands (S)).Approaches l X x') :
    (bands (S)).Approaches l (fun i=> (a.map (applies B ℨ (s i) (t i))).prod (X i)) ((a.map (enacts B ℨ T')).prod x')
  actualField (a : Lead.Clan) (f : Test4) : (χ (positiveLabel a) f Ω).1=Y a f
  actualDistribution (a b : Lead.Clan) (f g : Test4) : Z a b (tieAt f g)= inner ℂ ζ ((χ (negativeLabel a) (bar f)) ((χ (positiveLabel b) g) Ω)).1
  actualAnchors : ∀ᶠ i in atTop, ∀ t:ℕ,c (n i) ≤ t→
    ∀ a b : Lead.Clan, P.spacePrice (P.registeredStamp A c r n w (negativeLabel a) i) F ⊆ reviewEarlierBox.invites ∧
     P.spacePrice (P.registeredStamp A c r n w (positiveLabel b) i) U ⊆ reviewLaterBox.invites ∧
    ((P.reportPrism A c r n w F U i t (P.singleState 3 t x)) a b= P.singleState 3 t x (Φ a t i * Ψ b t i)) ∧
    ((P.reportPrism A c r n w F U i t (P.thinSplit x t)) a b= P.thinSplit x t (Φ a t i * Ψ b t i))
  wick (a b : Lead.Clan): P.readPrism x V w 1 F U a b=
    ∫ y:Vantage,∫ z:Vantage,(F.val y:ℂ)*(U.val z:ℂ)*P.onFields x A c r n w p a b (z-y)
  values (a b : Lead.Clan) (y : Vantage) (h : 0<y 3) : paintedFrom (S) (Λ a) (Λ b) (polarBase y) ((y 3)*Complex.I)= P.onFields x A c r n w p a b y

include H₀ p
theorem sold_cap_registers : P.OverM4 x c r F U A n w V Y Z p:= by
  let L:= H₀.lab; let Y':= H₀.zeroHeat
  refine { receipt:= has_rapid_on_M4 P x K c r R i₀ F U A n w V g h X Y Z H₀
           widthOK:= fun j t ht=> P.eventuallyCovered x _ (P.all_backed x A c r n w p j) t ht
           onDomain := P.register_closable x A c r n w p
           priced := P.distributes x A c r n w p
           localAdj := P.register_inner x A c r n w p
           covarianceT := P.register_shift x A c r n w p
           asks := fun _ _ _ _=> rfl
           width := fun a s t h {_ _} u=> SatinRegistration.Letter.width B ℨ s t a h u
           through := fun {_} l a T' s t q v {_ _} u=> SatinRegistration.Letter.finish B ℨ T' l s t a q v u
           actualField := P.registered_vacuum x A c r n w V X F U Y Z L p Y'
           actualDistribution := P.registered_tie x A c r n w V X F U Y Z L p Y'
           actualAnchors := L.under_boxes.mono fun i h _ _ a b=> ⟨(h a).1,(h b).2,rfl,rfl⟩
           wick := P.registration_reading x A c r n w V X F U L p
           values := fun a b y t=> (Y'.point a b y t).trans (P.carried_price x A c r n w V X F U L p a b y t).symm }

#print axioms has_rapid_on_M4
#print axioms sold_cap_registers
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
