import VerifiedSatinPaidNeighborhoods
import YM.SU5.Relativistic.AllErected

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

open Mir Phase RP Reflect Advance Heat
open Tower.Reconstruction.FermionSlab
universe v

/-- The twisted reflected Gram matrix is positive on one specified character,
for each common parity, lattice reflection plane and admissible finite probe list. -/
def ElectedGradedProbes : Prop :=
  ∀ (stage : ℕ) (j : Axis) (plane : ℤ) (parity : Bool) (J : Type v) [Fintype J]
    (probe : J → Buffered.Family (tent Y H)),
    (∀ i, ∃ S : Finset Cover, InTest (tent Y H) true S parity (probe i) ∧
      Tower.region j (Heat.gaugeShift P.block plane) (tent Y H).ℓ S) →
    Matrix.PosSemidef (Matrix.of fun i k =>
      evaluate Y H D.univ_ G 0 room
        (SameCharacter.resident Y H D.univ_ G 0 false (room 0) (pan.character sample)) stage
        (Reflect.chord parity • (mirror (tent Y H) j (Heat.gaugeShift P.block plane) (probe i) * probe k)))

theorem Election.gradedProbeMatrices
    (e : Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample) :
    ElectedGradedProbes.{v} (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample) := by
  obtain ⟨thin, lift, grades⟩ := grades_at Y H D.univ_ G.history
  intro stage j plane parity J inst probe admissible
  exact erected Y H D.toExhibition G thin grades 0 j room (pan.character sample)
    stage plane probe admissible

/-- One and the same interacting election has the paid separated signal and
the graded reflection bound, with all subsequence and lift data constructed. -/
theorem selectedInteractingGradedProbes (ε η : ℝ) (hη : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧
      PaidNeighborhoods (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample)
        (s:=s) (ζ:=ζ) (f':=f') (q:=q) (d:=d) (w:=w) ∧
      ElectedGradedProbes.{v} (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample) := by
  obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,e⟩ :=
    electGlass ε η hη U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,
    e,e.paidNeighborhoods,e.gradedProbeMatrices⟩
end YM.CF.Py.Rate.LocalLimit.Papal

#print axioms YM.CF.Py.Rate.LocalLimit.Papal.Election.gradedProbeMatrices
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedInteractingGradedProbes
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.chargedGram
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.erected
