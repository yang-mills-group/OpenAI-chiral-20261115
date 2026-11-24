/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Cells.Corrected
import YM.Euclid.OtherPlanes
import YM.Phase.Mixture
import YM.Fields.System
import YM.PCalc.Band

/-!
# Target (UNPROVED)

E L539--614, using that paper's Wilson construction (denotational
representations & trajectories, not claiming to prove all the proposed
intermediate estimates or algorithms), conventions documented in spec docs.
Goal is existence *without* hypotheses about limits, estimates, field model,
etc. Not Hamiltonian identification/OPE; not mass gap; not any claim about
proving or refuting the Clay Problem. The actual existence of the system,
including Seeds, Analytic turns, Selection and Wightman, remains red.
No conditional arrow proving one part is the solution.

Gauge = actual compact matrix image with the stipulated Lie algebra simplicity
in `Gauge.Simple`. Calendar = actual lengths & periods in one path, discrete
choices shared from E kernel. Reference coordinates = Taylor-gauge polynomials
in the weight grading, normalized color/matrix comparison. All-arity includes
arity 0. Fourier convention internalized in consequent W.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spec
open Extraction Table Boundary Wilson Cells
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge}

/-- L544--581. Adds generic point convergence needed in (iii). -/
structure Seed (C : Family G) (f : Order) (S : Table C.book) : Prop where
  cutoff : C.Makes
  ordered : f.Ordered C S
  generic : f.PointLimits C S
  kernel : S.Hierarchy
  copies : CellHyp C f
  corrected : RankWidths C f S

structure Algebra {L : Register G} (S : Table L) where
  derivatives : DiffPlan S
  turns : Rotation S
  energy : Stress S

/-- L583--597. Uses finite cap & field equivalences and quotient ops on
Union. Fields over all characters also specified with symmetries and
inheritance, and a chosen unique-heat phase in that decomposition.
-/
structure Locals {L : Register G} {S : Table L} (X : Algebra S) (h : S.RealSpin) : Prop where
  injection : X.derivatives.Inclusions S
  derivatives : X.derivatives.Derivatives S
  rights : X.derivatives.Orientation h
  spots : X.turns.Laws X.derivatives h
  motion : X.turns.Oriented S
  comparator : Maxwell.Ranks S h
  conserved : Conserved X.derivatives h X.energy
  spin : Tensorial X.turns X.energy
  charges : StressLaws S X.energy X.derivatives.deriv X.turns.lie

structure Materializes {C : Family G} {Z : Table C.book} (X : Algebra Z) (Y : OS.Selection Z) (h : Z.RealSpin) : Prop where
  transport : Locals X h
  phase : OS.Selection.Certificate (P := X.derivatives) X.turns X.energy Y

/-- L598--606. Same C and S and X, J_E pinned in Wightman,
not arbitrary W. (J_E here also equals `unionAdj` on pins.) -/
structure Relativistic {C : Family G} {S : Table C.book} (X : Algebra S) (Y : OS.Selection S) (B A : Contour S) (F : Wightman S)
    (h : S.RealSpin) : Prop where
  allWorld : B.From S
  chosen : A.From (Y.ensemble Y.atPoint)
  qt : F.Realizes (W := A.world) X.turns h

open RG Input Precision Supply Shoot
/-- Include stationary/reset witnesses (analytic finite-loop matching on
  this trajectory) for specificity. Not a uniqueness/fitted-β claim on
  arbitrary cutoff measures. Doesn't require logarithmic comparison on
  smaller/Lie-only contour view to be proven from RPos. Chosen WPs
  use this construction receipt through RED producers. See manual.
-/
def Calibrated (C : Family G) : Prop :=
    ∃ (S : Sheet G) (D : Rolls S) (T : Protection D) (W : Delays T) (Y : Bar W) (I : Wait Y)
        (O : ChartRatio G) (K : MapPrices) (P : PostCost D) (B : Directed G I O K P) (F : ℕ → ∀ p, Trail B.a p),
      B.bake.Stays F ∧ C.path=B.bake.make F ∧ ∀ N m p, m<N → B.Move N m p (F N p m) (F N p (m+1))

/-- Full T goal body on one family / extraction. A witness requested for
all levels, weights, configurations; quantifiers see the imported records.
Explicit tests in `Checks`. -/
structure Final (C : Family G) (f : Order) (S : Table C.book) where
  calibration : Calibrated C
  room : Seed C f S
  sector : Algebra S
  α : OS.Selection S
  phase : Materializes sector α room.kernel.spin
  B : Contour S
  A : Contour S
  action : Wightman S
  realization : Relativistic sector α B A action room.kernel.spin

/-- Not a theorem! The explicit T goal, including production of ALL data for
any allowed compact gauge image and faithful unitary representation per E.
This hypothesis is on the actual image; see `Gauge.Image` for input representation.
-/
def CLOSED : Prop := ∀ G : Gauge, G.Simple → ∃ (C : Family G) (f : Order) (S : Table C.book), Nonempty (Final C f S)

/-- Parameter persistence test. No subsequent limit after boundary: these
refinements are at the FAMILY level. -/
def Final.onward {C : Family G} {f : Order} {S : Table C.book} (F : Final C f S) (g : Order) : Final C (f.refine g) S :=
  let h : Seed C (f.refine g) S :=
    { cutoff := F.room.cutoff
      ordered := Order.upon F.room.ordered g
      generic := f.point_retained _ _ F.room.generic g
      kernel := F.room.kernel
      copies := recur F.room.copies g
      corrected d := by
        obtain ⟨X,Y,hy⟩ := F.room.corrected d
        exact ⟨X,Y,Y.refresh f hy g⟩ }
  ⟨F.calibration,h, F.sector, F.α, F.phase, F.B, F.A, F.action, F.realization⟩
end YM.Spec
