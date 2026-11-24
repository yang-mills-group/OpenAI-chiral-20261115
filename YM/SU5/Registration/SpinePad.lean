import YM.SU5.Registration.Tuple
import YM.SU5.Registration.Reconstruction
/-!
# Positive-pad prices for the M4 stamp

Widths are the actual `Vantage` widths (P.macroStep etc.), symmetric
padding `t` means from **point** to each end in this clock. Only inquire
it if the managed stamp passes (has width ≤ t). Then it is the projected
`Apron.engine` on that election and that stencil, sealed with the remaining
heat on the real representation. Not a condition on a replacement sequence
with same limiting vacuum vector. Use both field orientations. More general
than sold stamp/partner lemmas for later inquiry. Keep label argument `W`
explicit. Prove first the domain estimate already unconditional for ANY fixed
stamp; any assertion of locality for this fixed width would be inappropriate
(see M4 support licenses & `-ReproofLabels`); then purchase for thinning
including point-pad charges before asking for unpadding.
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
local notation "Ω" => P.heaven 3 ξ
local notation "G" => bands (P.seasons 3 ξ)
local notation "T" => (P.seasons 3 ξ).E
variable (A : P.Apron)

def priceWidth : ℝ≥0:= (A.realWidth P 3).toNNReal
lemma price_pos : 0 < P.priceWidth A := Real.toNNReal_pos.mpr (A.real_width_pos P 3)
lemma price_exact : (P.priceWidth A:ℝ)=A.realWidth P 3:=Real.coe_toNNReal _ (A.real_width_pos P 3).le
local notation "W₀" => P.priceWidth A
abbrev manageBoth (s t : ℝ≥0) : (H).Op := T (s-W₀)* P.realTable x A*T (t-W₀)
abbrev manage (s : ℝ≥0) := P.manageBoth x A s s
lemma manage_run (s u : ℝ≥0) (p : P.priceWidth A ≤ s) : P.manage x A (s+u)= T u * P.manage x A s * T u:=by
  have he: s+u-W₀=s-W₀+u:=(tsub_add_eq_add_tsub p).symm
  let t:=s-W₀
  change T (s+u-W₀)*P.realTable x A*T (s+u-W₀)=T u*(T t*P.realTable x A*T t)*T u
  have hv:T (s+u-W₀)=T u * T t:=by rw [he,add_comm]; exact (S).time u t
  have ht:T t*T u=T u*T t:= ((S).time t u).symm.trans ((congrArg (T) (add_comm ..)).trans ((S).time u t))
  rw [hv]; simp only [mul_assoc, ht]
lemma manage_kiss (s t : ℝ≥0) : (P.manageBoth x A s t).adjoint=P.manageBoth x (A.kiss P 3) t s:=by
  have hv:(P.realTable x A).adjoint=P.realTable x (A.kiss P 3):=P.roll_label_adj x A
  unfold manageBoth; rw [←ContinuousLinearMap.star_eq_adjoint,star_mul,star_mul]; simp only [ContinuousLinearMap.star_eq_adjoint,(S).sym,hv]; rw [← mul_assoc]; rfl

variable (W : ℕ→P.Apron)
local notation "C" => fun (t:ℝ≥0) (i:ℕ)=> P.manage x (W i) t
def CapPrice : Prop := (∀ (t:ℝ≥0), 0<t → ∀ y:H, CauchySeq (fun i=> P.manage x (W i) t y) ∧ CauchySeq (fun i=> (P.manage x (W i) t).adjoint y)) ∧
  (∃ r : ℕ, ∃ c ≥ (0:ℝ), ∀ t : ℝ≥0, 0<t→t≤1→∀ᶠ i in atTop, (t:ℝ)^r * ‖P.manage x (W i) t‖ ≤ c)
def CapReady : Prop := (∀ j:Axis,Tendsto (fun i=> (W i).realWidth P j) atTop (𝓝 0)) ∧ P.CapPrice x W
lemma eventuallyCovered (p : P.CapReady x W) (t : ℝ≥0) (h : 0<t) : ∀ᶠ i:ℕ in atTop, P.priceWidth (W i)<t := by
  refine ((p.1 3).eventually (gt_mem_nhds (show (0:ℝ)<(t:ℝ) from h))).mono fun i e=>?_
  change (P.priceWidth (W i):ℝ) < (t:ℝ); rw [P.price_exact]; exact e
lemma delivery_cap (p : P.CapReady x W) : Delivery (S) C :=
  ⟨fun t h s=> (P.eventuallyCovered x W p t h).mono fun i h=> P.manage_run x _ t s h.le, fun t h y=>(p.2.1 t h y).1,p.2.2⟩
lemma cap_partner (p : P.CapReady x W) : P.CapReady x (fun i=> (W i).kiss P 3) := by
  refine ⟨fun j=> p.1 j, fun t h y=> ?_,?_⟩
  · let Q:= fun i:ℕ=>P.manage x (W i) t; rw [show (fun i=> P.manage x ((W i).kiss P 3) t y)=(fun i:ℕ=> (Q i).adjoint y) from funext fun i=> congrArg (fun z:(H).Op=>z y) ((P.manage_kiss x (W i) t t).symm)]
    refine ⟨(p.2.1 t h y).2,?_⟩
    simp_rw [manage,←P.manage_kiss x (W _) t t, ContinuousLinearMap.adjoint_adjoint]; exact (p.2.1 t h y).1
  obtain ⟨r,c,v,u⟩:=p.2.2; refine ⟨r,c,v,fun t h w=>?_⟩
  simp_rw [manage,←P.manage_kiss x (W _) t t,ContinuousLinearMap.adjoint.norm_map]; exact u t h w

-- registration phase for ANY such purchased symbol
abbrev managed (p : P.CapReady x W) := (P.delivery_cap x W p).accepts
def pointField (p : P.CapReady x W) := SatinRegistration.field (S) (P.managed x W p) ((P.delivery_cap x W p).isSound) (P.delivery_cap x W p|>.paid)
lemma field_partner (p : P.CapReady x W) : P.pointField x (fun i=> (W i).kiss P 3) (P.cap_partner x W p) = SatinRegistration.adj (S) (P.managed x W p) ((P.delivery_cap x W p).isSound) (P.delivery_cap x W p|>.paid) := by
  have he:= (P.delivery_cap x W p).reverse (P.delivery_cap x (fun i=> (W i).kiss P 3) (P.cap_partner x W p)) (fun s i=> P.manage_kiss x (W i) s s); unfold pointField adj managed; congr
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
