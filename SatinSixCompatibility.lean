import YM.Sextet.PaintForward
import YM.SU5.Six.PointReceipt
import YM.Sextet.KernelPay
import YM.Sextet.WallLimit

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open scoped Topology Matrix BigOperators InnerProductSpace NNReal
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Lamour.Bridge.Celeste.Morn

namespace Spine

theorem reviewSixTick (P : Spine) (n : ℕ) : P.incStep n = P.timeJump n := by
  simp [incStep, ticksUp, timeJump, tickRound, ruler]

theorem reviewSixHeat (P : Spine) (s n : ℕ) : P.incT s n = P.advanceHeat s n := by
  simp only [incT, advanceHeat, reviewSixTick]

theorem reviewSixMark (P : Spine) (Z : Window.Family) (n : ℕ) :
    P.incF Z n = P.timeDifference Z n := by
  simp only [incF, timeDifference, reviewSixTick]

private theorem viewOfEqualMarks (P : Spine) (j : Axis) (x : P.Spectrum0 j) (s : ℕ)
    {f g : P.Test} (p : P.birthF j s f) (q : P.birthF j s g) (e : f = g) :
    P.viewF j x s p = P.viewF j x s q := by
  subst g
  rfl

theorem reviewSixVector (P : Spine) (x : P.Spectrum0 3) (Z : Window.Family) (s n : ℕ) :
    P.incV x Z s n = P.macroVector x Z s n := by
  exact congrArg (P.wealth 3 (P.otherSpectrum 3 3 x))
    (viewOfEqualMarks P 3 (P.otherSpectrum 3 3 x) s (P.incF_bright Z s n)
      (P.timeDifference_birth Z s n) (P.reviewSixMark Z n))

theorem reviewSixMatrix (P : Spine) (x : P.Spectrum0 3) (s n : ℕ) (r : Vantage) :
    P.rise x s n r = P.kernel6 x s n r := by
  ext Z Y
  simp only [rise, risingK, kernel6, Matrix.of_apply, reviewSixVector, cart_shore]
  rfl

/-- Independently smearing two Hilbert vectors on the same elected law commutes with grid
refinement. Applying this to an actual pair of priced physical marks additionally uses their
ordered-grid identity and clearance from the common reflection wall. -/
theorem reviewSixSmearPair (P : Spine) (x : P.Spectrum0 3) (J : P.Ellis 3 x)
    (Z Y : Window.Family) (s n : ℕ) (c : ℝ) (f g : Vantage → ℝ)
    (hf : Continuous f) (cf : HasCompactSupport f) (hg : Continuous g) (cg : HasCompactSupport g) :
    Tendsto (fun t => inner ℂ (P.fineSense x Z s n c f t) (P.fineSense x Y s n c g t)) atTop
      (𝓝 (inner ℂ (P.enter 3 (P.advocate 3 x 3) (P.realSense x Z s n c f))
        (P.enter 3 (P.advocate 3 x 3) (P.realSense x Y s n c g)))) :=
  (P.smoothed_motion x Z s n c f J hf cf).inner (P.smoothed_motion x Y s n c g J hg cg)

#check @reviewSixMatrix
#print axioms reviewSixTick
#print axioms reviewSixHeat
#print axioms reviewSixMark
#print axioms reviewSixVector
#print axioms reviewSixMatrix
#check @reviewSixSmearPair
#print axioms reviewSixSmearPair

/-- The selected, independently smeared physical pair price is the exact weighted double
sum of the first worker's six-channel kernel on any ordered grid clearing both footprints. -/
theorem reviewSixPhysicalGrid (P : Spine) (K : P.Register) (x : P.Spectrum0 3) (J : P.Ellis 3 x)
    (Z Y : Window.Family) (s n t : ℕ) (ht : s ≤ t) (f g : Vantage → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (ordered : ∀ p ∈ P.fineSites t hf, ∀ q ∈ P.fineSites t hg,
      P.transportWidth s n 3 + P.transportWidth s n 3 < P.grid t q 3 - P.grid t p 3)
    (apart : ∀ p ∈ P.fineSites t hf, ∀ q ∈ P.fineSites t hg, ∀ j : Axis,
      P.transportWidth s n j + P.transportWidth s n j < |P.grid t q j - P.grid t p j|) :
    P.spirits K 3 x (P.paintPair ((P.macroBody Z s n).kiss P 3) (P.macroBody Y s n) t f g) =
      (((P.macroTick t)^8 : ℝ) : ℂ) * ∑ p ∈ P.fineSites t hf, ∑ q ∈ P.fineSites t hg,
        ((f (P.grid t p) : ℂ) * (g (P.grid t q) : ℂ)) * P.rise x s n (P.grid t q - P.grid t p) Z Y := by
  rw [P.paintPair_here, P.read_markPair _ _ _ _ _ hf hg]
  apply congrArg (fun z : ℂ => (((P.macroTick t)^8 : ℝ) : ℂ) * z)
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [P.reviewSixMatrix x s n, P.grid_plenum x J s n Z Y t p q ht (ordered p hp q hq) (apart p hp q hq)]

#check @reviewSixPhysicalGrid
#print axioms reviewSixPhysicalGrid

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
