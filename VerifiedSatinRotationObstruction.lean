import YM.SU5.Obstruction.Election
import YM.SU5.Rotation.Elected

/-! Both source proofs on one history and one elected character. -/
namespace YM.CF.SatinRotation
open Lattice

/-- Both constructions rotate the same real coordinate plane in the same direction. -/
theorem samePlaneAction (θ : ℝ) (x : Axis → ℝ) :
    roll (planeRotation θ) x = YM.SU5Rotation.Plane.turn θ x := rfl
end YM.CF.SatinRotation

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option maxRecDepth 7500
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open Tower.Reconstruction CF.SatinRotation
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

universe v

/-- Both tight-localization obstructions hold on the very character retaining
the separated interaction and the graded reflection-positive probes. -/
theorem selectedRotationObstructionCrosschecked (ε η : ℝ) (hη : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧
      PaidNeighborhoods (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample)
        (s:=s) (ζ:=ζ) (f':=f') (q:=q) (d:=d) (w:=w) ∧
      ElectedGradedProbes.{v} (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample) ∧
      Obstruction Y H D G room (pan.character sample) ∧
      RotationObstruction.FixedResolutionGap Y H D G room (pan.character sample) := by
  obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,e,paid,graded,primary⟩ :=
    selectedRotationObstruction.{v} ε η hη U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,
    e,paid,graded,primary, Election.obstruction e⟩

end YM.CF.Py.Rate.LocalLimit.Papal
#check @YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstruction
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstruction
#check @YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstructionAlternative
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstructionAlternative
#check @YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstructionCrosschecked
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstructionCrosschecked
#check @YM.CF.SatinRotation.samePlaneAction
#print axioms YM.CF.SatinRotation.samePlaneAction
#check @YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.fixed_neighborhood
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.RotationObstruction.fixed_neighborhood
