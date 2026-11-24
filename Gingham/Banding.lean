import Gingham.Bridle
import Gingham.Rosette
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration YM.Velour
variable (a:Weave)
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


-- Supports and product repricing, from the satellite Thin/Proof/CoherentMark
-- and Thin/Heritage/Marquee calculations in project.
open Tower.Reconstruction Tower.PhaseChoice
variable (s t:ℕ) (f g:P.Test) (B C:Set Vantage)
lemma hold_asked (h:P.asked_at s f B)(b:s≤t) :
    P.asked_at t (P.conveying s (t-s) f) B:= ⟨_,
  (Tower.proceeds P.run P.large P.history.circuit s (t-s) 
   ((Tapestry.locates P.calibration h.choose true (f:=f)).1 h.choose_spec.1)).1,
  (P.pin_onward s t _ b).trans h.choose_spec.2⟩

lemma held_apart (h:P.asked_at s f B) (k:P.asked_at s g C) (d:Disjoint B C):
    P.conveying s (t-s) (f*g) =
    P.conveying s (t-s) f * P.conveying s (t-s) g := by
  obtain ⟨J,v,l⟩:=h; obtain ⟨Z,u,w⟩:=k; rw [P.usual_footprint] at l w
  have he:= d.mono l w
  have e:Detached P.par P.width J Z:=
    PhaseChoice.separatedPhys (show printedHere P.par P.width s J (handstamp _) from has_footprint P.par P.width s J)
      (show printedHere P.par P.width s Z (handstamp _) from has_footprint P.par P.width s Z) (Disjoint.preimage _ he)
  exact Subtype.ext (woven_product P.run P.large P.history.circuit s (t-s)
    ((Tapestry.locates ..).1 v) ((Tapestry.locates ..).1 u) e)


open Diary
section
variable (g m:Hook P x) (i k:ℕ)
local notation "L"=>BlotAt a P x g i s
local notation "W"=>WellAt a P x m k s
abbrev CarrierB (f:P.Test) := P.conveying s (t-s) f
local notation "Cᵤ"=> CarrierB P s t
def tariff (u:P.Test)(e:ℕ)(f:P.Test):ℂ:=
   rawE P t e (magnet P u f) / rawE P t e (magnet P u 1)

/-- Held stencil prices. -/
def SharpEu (u:P.Test)(e:ℕ):Parts :=
   let X:=tariff P t u e
   (X ((Cᵤ L)*(Cᵤ W)), X (Cᵤ L), X (Cᵤ W))

structure RadiusAudit (N:ℝ): Prop where
  pos:0<N
  bev(q:Vantage)(h:q∈a.ra ∪ a.rb): |q 3|<N

lemma encloses : ∃ N,RadiusAudit a N:= by
  obtain ⟨c,h⟩:=((a.ba.union a.bb).image (continuous_apply (3:Axis)|>.abs)).bddAbove
  let R:=max (c+1) 1
  refine ⟨R,zero_lt_one.trans_le (le_max_right ..), fun q v=>
     (h (mem_image_of_mem _ ((Set.union_subset_union subset_closure subset_closure) v))).trans_lt
       ((lt_add_of_pos_right _ zero_lt_one).trans_le (le_max_left ..))⟩
structure SharpCover : Prop where
  holdsL:P.asked_at t (Cᵤ L) a.ra
  holdsW:P.asked_at t (Cᵤ W) a.rb
  a_color:(Cᵤ L) ∈ enclave P.calibration
  b_color:(Cᵤ W) ∈ enclave P.calibration
  product:Cᵤ (L * W)=Cᵤ L * Cᵤ W


lemma covered_sharp (h: InBuoy a P x g m i k s)(v:s≤t): SharpCover a P x s t g m i k := by
  obtain ⟨J,hJ,l⟩:=h.1.raw
  obtain ⟨K,hK,b⟩:=h.2.raw
  have l:P.asked_at s L a.ra:= ⟨_,hJ,l.trans h.1.physical⟩
  have b:P.asked_at s W a.rb:= ⟨_,hK,b.trans h.2.physical⟩
  refine ⟨hold_asked P s t L _ l v, hold_asked P s t W _ b v,
    P.refine_keeps s L h.1.singlet _,P.refine_keeps s W h.2.singlet _,
    held_apart P s t L W _ _ l b ?_⟩
  refine Set.disjoint_left.mpr fun z r u=> ?_
  exact lt_irrefl _ (a.stagger _ r _ u).2.1

structure SharpBill (δ:ℝ) (u:P.Test) : Prop where
  inquiry : SharpCover a P x s t g m i k
  scan : ∀ᶠ j in atTop, Ferry P.run t (irr P j) (uvv P j) ∧
     rawE P t j (magnet P u 1)≠0 ∧
     Topaz (SharpEu a P x s t g m i k u j) (AudEu a P x g m) δ

abbrev lever (z:Option Bool → ℂ):Parts:= (z none,z (some true),z (some false))


lemma sharp_ticket {δ:ℝ} 
    (h:InBuoy a P x g m i k s)
    (b:Topaz (GridEu a P x g m i k s) (AudEu a P x g m) δ)
    (N:ℝ):
    ∃ t, s≤t ∧ ∃ u:P.Test, Lodgment P t N u ∧ SharpBill a P x s t g m i k δ u:=by
  let f:Option Bool→P.Test:=fun e=>match e with
    | none=>L * W
    | some true=>L
    | some false=>W
  let U:Set (Option Bool→ℂ):={z| Topaz (lever z) (AudEu a P x g m) δ}
  have o:IsOpen U:=isOpen_iff_mem_nhds.mpr fun z y=>
    (show Continuous lever from (continuous_apply _).prodMk
       ((continuous_apply _).prodMk (continuous_apply _))).continuousAt.preimage_mem_nhds
       (likelier _ (lever z) y)
  obtain ⟨t,v,u,A,H⟩:= after_knives P x s f o b N
  have S:=covered_sharp a P x s t g m i k h v
  refine ⟨t,v,u,A,S,H.mono fun j e=>⟨e.1,e.2.1,?_⟩⟩
  unfold SharpEu
  rw [← S.product]
  exact e.2.2
end


/-- Regulator delivery of the strict budget by consultation readings
of the ONE joint chiral course at terminal coupling. A single auditor
charged twice, to the far sides of the probes at this measurement.
Late path indices enough (may depend on grid). -/
theorem veiled (g m:Hook P x) {δ:ℝ} (h:Glory a P x g m δ):
    ∃ A:ℝ, RadiusAudit a A ∧
     ∃ n,∀ i k s:ℕ, n ≤ i → n ≤ k → n ≤ s → Height P x g m i k s →
       InBuoy a P x g m i k s ∧
       ∃ t, s≤t ∧ ∃ u:P.Test, Lodgment P t (A+1) u ∧
          SharpBill a P x s t g m i k δ u :=by
  obtain ⟨A,e⟩:=encloses a
  obtain ⟨n,E⟩:=h.eu_ledger
  refine ⟨A,e,n,?_⟩
  intro i k s v w t g₁
  obtain ⟨b,d⟩:=E i k s v w t g₁
  exact ⟨b,sharp_ticket a P x s g m i k b d (A+1)⟩

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Gingham.veiled

