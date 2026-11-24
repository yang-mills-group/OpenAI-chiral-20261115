import ExactRunning.Endpoints.Total

/-!
# Fixed-step records

Held throughout the comparison of high and low determinants. No
estimates relating differently blocked histories needed.
A `BlockTie E I` stores one step (including all hypotheses needed for
comparison, for compact signatures), from the finer `Pylon E` to the
coarser `I`. `T`: translation data. `W`: installed linear lift in finite
periods, `Phi` its symbol (with color) in the archive's conventions. `lo`: lower
threshold for finite-period matching (`Test`; compare Gold.sold).
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix


open Precision Wilson Exterior Tree
variable {G : Gauge}

/-- At one scale. -/
structure Pylon (G : Gauge) where
  p : Clip
  r : PathData G
  F : KindF G
  B : Bed
  σ : ℝ
  ε : ℝ
  C : ℝ
  τ : ℝ
  A : ℝ
  Λ : ℝ
  house : 0<σ
  strict : 0<ε
  cap : 0 ≤ C
  paths : r.Bounds p τ A Λ
  bound : 0 ≤ A
  rent : 1 ≤ Λ
  covered : B.covered σ C
  floor (m) : Floor B p m ε C
  attached : Attached B r
  sworn (m) : Bid.Sworn B m G
  endpoint : Endpoint p r F

namespace Pylon
variable (E : Pylon G)
lemma strip : E.B.metric.strip E.σ E.C := E.covered.2.1
lemma deck : E.B.metric.safe := E.B.metric.rights _ _ E.strip E.house.le
lemma hτ : 0<E.τ := E.paths.width
end Pylon

/-- A step between consecutive data sets. We assume
availability at every sufficiently large period. The exact diagonal
needn't use those same periods. -/
structure BlockTie (E I : Pylon G) where
  patch : Patch
  kernel : KernelChoices
  branches : patch.Branches kernel G
  simple : G.Simple
  T : Towers patch.L
  q : ℝ
  form : ChartRatio G
  actual : LocalRatio form

  η : ℝ
  drift : ℝ
  rate : ℝ
  toll : ℝ
  gap : ℝ
  lo : ℕ
  hη : 0<η
  hd : 0≤drift
  ht : 0<toll
  hr : 0<rate
  hg : 0<gap
  width : Headers (P:=patch) T.A0 2 η drift
  diagonal (m : Side) :
    Towers.Diagonal (c:=m) (f:=m*patch.L) ⟨patch,kernel,rfl⟩ E.B I.B T
  large (m : Side) (h : lo ≤ m.val) :
    Bid.Larger (G:=G) (c:=m) (f:=m*patch.L) ⟨patch,kernel,rfl⟩

  ready (m : Side) (h : lo ≤ m.val) :
    let s : StepData m (m*patch.L) := ⟨patch,kernel,rfl⟩
    ∃ f : Forest s.ratio, PriceGap (S:=s) f E.p E.r gap ∧
    ∃ u, Critical (S:=s) f E.p E.r u ∧ Guessed f (installed s.ratio T.A0) u ∧
     ClassicalMatch f E.p I.p E.r I.r u ∧ FiniteBound f E.r I.r E.p I.p q form u toll rate 1

namespace BlockTie
variable {E I : Pylon G} (T : BlockTie E I)

abbrev L := T.patch.L
abbrev up (m : Side) := m * T.L
def step (m : Side) : StepData m (T.up m) := ⟨T.patch,T.kernel,rfl⟩
def W (m : Side) := installed (T.step m).ratio T.T.A0
def Phi := moonlit G T.patch T.T.A0
/-- fixed choice. -/
noncomputable def choice (m : Side) : (T.step m).Choices := Classical.arbitrary _
variable {m : Side}

structure Test (T : BlockTie E I) (m : Side) where
  reach : T.lo ≤ m.val
  tree : Forest (T.step m).ratio
  shellChart : fieldDir G m 1 → AxisChart G tree
  gap : PriceGap tree E.p E.r T.gap
  critical : Critical tree E.p E.r shellChart
  guess : Guessed tree (T.W m) shellChart
  classicalMatch : ClassicalMatch tree E.p I.p E.r I.r shellChart
  finite : FiniteBound tree E.r I.r E.p I.p T.q T.form shellChart T.toll T.rate 1

lemma test (h : T.lo ≤ m.val) : Nonempty (T.Test m) := by
  obtain ⟨f,a,u,b,c,d,e⟩ := T.ready m h
  exact ⟨⟨h,f,u,a,b,c,d,e⟩⟩

lemma bridge : Cruise T.Phi 2 T.η T.drift := T.width.cruise G T.hη T.hd

lemma via (m : Side) : Premise (T.step m) (T.W m) T.Phi := by
  apply launchBridge
  have h := Row.rights _ _ (T.width [] (by simp)) T.hη.le
  exact h

end BlockTie
end ExactRunning
