import VerifiedSatinGradedEuclidean
import AuditSatinSeparatedReadings

/-! The same election supplies the price, the physical supports and the selected character. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option maxRecDepth 7500
set_option synthInstance.maxSize 30000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open Tower.Reconstruction
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

-- Kept indexed so that new Ports can compose with exactly these data.
variable {ε η : ℝ} {U:Supplier} {P : Preparation} {l : ℕ} {Z ζ:ℝ} {H : Real.exp 1 ≤ P.x}
    {Y : Course P (VolumeCape.Dream.Nimbus l)} {q d w:ℕ} {C:ℝ}
    {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ} {E : ℕ → Buffered.Family (tent Y H) → ℂ}
    {L : Rack P l} {B : Tapestry.Clay P l} {T : ℕ → ℕ → Tapestry.Tariff} {t : ℕ → Tapestry.Tariff}
    {D : Tapestry.Fashion Y H a b I E L B T t}
    {G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H}
    {room : ∀ j, Tower.Arena Y H G.history.circuit j 0 false}
    {pan : Panel Y H D.univ_ G.history G.clipped 0 false (room 0)}
    {s : ℕ}
    {f f' : SU.Slot → observable (tent Y H) true}
    {sample : pan.X}

open Tower.Reconstruction
open scoped Topology

/-- The elected probe stays admissible and nonzero under independent small shifts.
Its common translations have exactly the same selected reading. -/
def PaidNeighborhoods : Prop :=
  ∀ (j : Axis) (z : SU.Slot) (δ : ℝ), 0 < δ →
    ∃ p n : Cover,
      let marks := pattern Y H j s (f' z) p n
      let pay := panorama Y H D.toExhibition G 0 room (pan.character sample) marks [false, true]
      Coupled Y H D.toExhibition G 0 j room (pan.character sample) s (z:=z)
        (u:=d) (v:=q) (S:=grindscape (booty (CF.Pannier.Chancel.grain (payout d q w)) d q)
          (Sen (CF.Pannier.Chancel.grain (payout d q w)) (payout d q w)))
        (o:=CF.Pannier.Chancel.grain (payout d q w)) (δ:=δ) (w:=ζ) p n (f' z) ∧
      (∀ᶠ y : Bool → Axis → ℝ in 𝓝 0, y ∈ journeying Y H marks [false, true] ∧ 1 / 33 < ‖pay y‖) ∧
      ∀ v : Axis → ℝ, pay (fun _ => v) = pay 0

lemma Election.paidNeighborhoods
    (h : Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample) :
    PaidNeighborhoods (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample)
      (s:=s) (ζ:=ζ) (f':=f') (q:=q) (d:=d) (w:=w) := by
  intro j z δ hd
  obtain ⟨p,n,paid⟩ := h.install.joint j z δ hd
  refine ⟨p,n,paid,?_,?_⟩
  · filter_upwards [near_true Y H D.toExhibition G j 0 room (pan.character sample)
        δ s (f' z) p n _ paid.certified] with y hy
    exact ⟨hy.1, hy.2.1⟩
  · intro v
    exact (displaced_test Y H D.toExhibition G j 0 room (pan.character sample)
      δ s (f' z) p n _ paid.certified v).trans
        (contacts_deployed Y H D.toExhibition G j 0 room (pan.character sample)
          δ s (f' z) p n _ paid.certified).symm

/-- The prior graded refinements and coordinate charts hold on precisely the
course, character and probe election used in the new neighborhood bound. -/
theorem selectedPaidNeighborhoods (ε η : ℝ) (hη : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧
      GradedRefinementLaws (i:=a) (k:=b) Y H G ∧
      WorldChartLaws Y H D G room (pan.character sample) ∧
      PaidNeighborhoods (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample)
        (s:=s) (ζ:=ζ) (f':=f') (q:=q) (d:=d) (w:=w) := by
  obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,h⟩ :=
    electGlass ε η hη U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,h,
    gradedRefinement_on Y H D G, worldCharts_on Y H D G room (pan.character sample),
    h.paidNeighborhoods⟩
end YM.CF.Py.Rate.LocalLimit.Papal

#print axioms YM.CF.Py.Rate.LocalLimit.Papal.Election.paidNeighborhoods
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedPaidNeighborhoods
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.starstruck
