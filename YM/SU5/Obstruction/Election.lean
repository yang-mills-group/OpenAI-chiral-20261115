import VerifiedSatinOddProbes
import YM.SU5.Obstruction.Gap

/-!
# One calibrated election with the gap
-/
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

/-- The gap is on the same character giving both the separated gauge--matter readings and the
positive-semidefinite graded reflected Gram matrices (including the odd ones with their phase).

Movement/continuity targets here: see `Obstruction`, `Retestable`, `approxValues`. Even allow
arbitrarily good, reading-only local interpolation in *all* bounded open moved neighborhoods,
for testing against just this J, with *all* levels of target stencils and no gauge neutrality
required on the approximating moved observables. Correlation continuity at the identity already
fails with such a requirement. Uses existing footprint & products. It's on the physical
resolution tests, `Pol`, even per slot, wide. Not asserting no-go for arbitrary extra-local
support slacks or for other algebras with other identifications/products. -/
theorem selectedRotationObstruction (ε η : ℝ) (hη : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧
      PaidNeighborhoods (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample)
        (s:=s) (ζ:=ζ) (f':=f') (q:=q) (d:=d) (w:=w) ∧
      ElectedGradedProbes.{v} (D:=D) (G:=G) (room:=room) (pan:=pan) (sample:=sample) ∧
      Obstruction Y H D G room (pan.character sample) := by
  obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,e,k,p⟩ :=
    selectedInteractingGradedProbes.{v} ε η hη U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,e,k,p,
    obstruction_holds Y H D G room (pan.character sample)⟩

end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.selectedRotationObstruction
