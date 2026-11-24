import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.M10
import YM.SU5.Registration.Sectors.Polity
import YM.SU5.Registration.Ink.RegEu

/-!
 # M11 Actual sector on M4

 Even the resulting Schwinger/Wightman distributions all n & nontriviality
 and partial (time) estimates on this projected sector. No importing a full
 cone or assuming axis-comparisons. See cp.
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


open Submodule SatinWFixed Carton

open Seld (optx timeslot laneslot)
variable {I:Type*} (B':I→P.Swatch)(u:∀ i,(B' i).WPermit x 3)
local notation "L"=> P.store x B' u
local notation "T"=> (P.store x B' u).joinT
include F₀
lemma solo_point (Z': (P.store x B' u).station)(t : ∀ x:E4, (T).translation x Z'=Z'): Z'∈ Submodule.span ℂ {(L).engaged []}:=by
 let S':= (P.seasons 3 (P.advocate 3 x 3)); have he(x:E4): S'.unit.translation x Z'.val=Z'.val:= congrArg (Subtype.val) (t x)
 let Vz:(P.ManyF 3 (P.otherSpectrum 3 3 x)).space:= Z'.val
 have hv(x:E4): Seld.M S' x Vz=Vz:= he x; have hx(s:ℝ): S'.edge s Vz= Vz:= Eq.trans ((DFunLike.congr_fun (timeslot S' s) Vz).symm) (hv _); have hz (a:OS.Cross timeAxis): S'.U a Vz= Vz:= Eq.trans ((DFunLike.congr_fun (laneslot S' a) Vz).symm) (hv a.val)
 have ht: Vz∈ Submodule.span ℂ {(P.heaven 3 (P.otherSpectrum 3 3 x))}:= (F₀.experiment.ground.1 3 Vz).2 ⟨hx,hz⟩
 obtain ⟨i,hi⟩:=Submodule.mem_span_singleton.mp ht
 exact mem_span_singleton.mpr ⟨i, Subtype.ext hi⟩
omit F₀
lemma lower_point (Z':(P.store x B' u).station) : ((T).P.diagonal Z').support ⊆ {p:E4 | 0 ≤ p timeAxis}:=by
 rw [(L).sees_m]; exact (S).nonneg _
variable (q:P.CapBacked x A c r n w)(pr:P.OverM4 x c r F U A n w V Y Z q)
variable (V₀:(Swatch.ordinary A).WPermit x 3)
local notation "D₀"=>P.directs x c r A n w q V₀
local notation "W₀"=> P.FastSales c r A n w
include q pr V₀ F₀
lemma pulse_at_sector : ∃ f: Test4, LinearIndependent ℂ (fun a=> (P.directs x c r A n w q V₀).engaged [(represents10 a true,f)]):=by
 obtain ⟨f,u⟩:= F₀.zeroHeat.sense; let Y'(a:Lead.Clan):= (D₀).engaged [(represents10 a true,f)]
 have he(a:κ): Y a f=(D₀).pointShelf.subtype (Y' a):= (P.vacuum_current x c r F U A n w V Y Z q pr V₀ a f).symm -- order?
 simp_rw [he] at u; refine ⟨f, LinearIndependent.of_comp (D₀).pointShelf.subtype u⟩ -- check
omit F₀ pr
lemma attaches (j:Instrument)(Zge:(D₀).citizen)(f:Test4):
 (D₀).live ((D₀).pointMap (represents10 j.1 j.2) f Zge) = P.registeredField x A c r n w q j f ((D₀).live Zge):=by
 refine Eq.trans (show (D₀).live ((D₀).pointMap (represents10 j.1 j.2) f Zge)= (D₀).operator (represents10 j.1 j.2) f ((D₀).live Zge) from rfl) ?_; rw [P.actual_field x c r A n w q V₀ j]; rfl
-- only reference.Eot
#check @Spine.planetary_sunlit
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.solo_point
#print axioms Spine.pulse_at_sector
#print axioms Spine.attaches
