import YM.CF.Buffered.Shooting

/-!
# Physical histories for applying the corollary

Inputs (separate from this proof) uniform on the ms cone and progression,
spelled out for the gaugeM and ratio argument at level 0. Use them even on
Borel F when taking the corresponding joint-E limits, but never on general
auxiliary reads. Top numeric bare of each sharp comparison is common on
these per-cutoff periods by construction of Shots (same β schedule `B₀` and
tilt values, coupling at the pivot x, derive equality), and analogously on
the heat. Need no pressure extrapolation in THIS corollary, i.e. use the
presrec bound of ms pc-low at the stopped level, as well as its rec-delta on
the two densities (these hard input estimates are discussion points in the
report). This formalization of the corollary is conditional on the preceding
prescription; it is not a construction of history data. It uses the
`Month` clock already paid for the pivot. Arbitrarily given top B0, regenerating
budgets, multiple draws, changed ν-expectations etc cannot instantiate it
without the hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker ComplexOrder
open Cube Tenant Lat Spire Scroll Scree Jet Phase Branch Fock Skye
open Py Vale Vale.Grace Haro Nova
open Wilson Precision Next.Free Next.SectorChange Tulip Gauge Paige Vault Brace
open Push.SectorMeasure
open Heat Advance Pressure
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- ms choice of increasing sizes, eventually contain every allowed m (in particular under m⁵≤n).
-- support fixed; don't turn this into any particular convergence-growth assertion.
def oddMultiple (x y : Side) : Prop := ∃ k:Side, Odd k.val ∧ x=y*k
structure Calibration where
 K : Teller SU.group
 R : RG.Patch
 rJ : R.J=4
 L : ChartRatio SU.group
 V : Grace K R L
 clip : K.top.clip.direct≤1
 b₀ : ℕ
 b_pos : 1≤b₀
 B : Side
 shape : B= R.L^b₀
 e : ℝ
 P : Grasp V.U B e
 W : GivenX V P
 M' : Side
 J : Robes M' V W
 η : Chi
 x : ℝ -- terminal physical inverse coupling
 base : Real.exp 1 ≤ x
 a : ℝ
 p : ℕ
 i : ℕ
 N0 : ℕ
 T : Month x a i p N0 V W
 h : ℝ
 positive_h : 1 ≤ h
 R0 : ℝ→ℝ
 δ : ℝ→ℝ
 D : ℕ -- Laurent size bound used for ℓ*
 w : ℕ -- r₂ used in choosing buffer
 ℓ : ℕ
 legal : Stencil.LaurentRadius K.j R.L D
 buffer : Margin R.L D w R.J ℓ
 vertex : ℕ -- R_T, large (tolerance estimated separately in bill-E)
 positiveR : 1≤vertex
 line : 2*ℓ ≤ 4*B.val*(vertex/(2*B.val))
 q : Side
 big : 61≤ q.val
 q_even : Even q.val
 roofSize : ∀ m, oddMultiple m q → ∃ M : Side, m=M*M' ∧ J.h ≤ M.val
 monthSize : ∀ m, oddMultiple m q → T.q ≤ m.val
 listTop : ℕ→Side
 sides : ∀ᶠ n in atTop, oddMultiple (listTop n) q ∧ ∀ m:Side, oddMultiple m q → m.val≤n → oddMultiple (listTop n) m -- ample covering tails

namespace Calibration
variable (K : Calibration)
abbrev takes (m : Side) := oddMultiple m K.q
def onList (m : Side) (n : ℕ) := oddMultiple (K.listTop n) m
def Allowed (m : Side) (n : ℕ) := K.takes m ∧ K.onList m n ∧ m.val^5 ≤ n
lemma eventually_allowed {m : Side} (h : K.takes m) : ∀ᶠ n in atTop, K.Allowed m n := by
 filter_upwards [K.sides,eventually_ge_atTop m.val,eventually_ge_atTop (m.val^5)] with i u k v
 exact ⟨h,u.2 _ h k,v⟩
lemma even {m : Side} (h : K.takes m) : Even m.val := by obtain ⟨p,h,rfl⟩:= h; exact K.q_even.mul_right p.val
def ζ : ℤ := -(K.vertex/(2*K.B.val):ℕ) -- gaugeShift ζ gives the ms pl-R in gauge cover units
abbrev plane0 := gaugeShift K.B K.ζ
def planeR : ℤ := -(4*K.B.val*(K.vertex/(2*K.B.val):ℕ)) -- check neg interpreted ℤ, casts
lemma atPlane : K.plane0 = K.planeR := by unfold plane0 planeR ζ gaugeShift; rw [mul_neg]
abbrev c (m:Side) := Vale.cell m K.B K.R.L 0
abbrev fits (m : Side) := band (K.c m) (3:Axis) K.plane0 K.ℓ
end Calibration

structure Histories (K:Calibration) where
 loom : ∀ m: Side, Cape m K.B K.R.L -- values outside the chosen progression not constrained; don't integrate any of those here
 sharp : ∀ m: Side, ℕ → Vestal m K.B K.R.L
 warm : ∀ m: Side, ℕ → Vestal m K.B K.R.L
 B₀ : ℕ→ℕ→ℝ
 wave : ℕ→ℕ→SpaceM
 tilt : ℕ→ℕ→ℝ
 wave' : ℕ→ℕ→SpaceM
 tilt' : ℕ→ℕ→ℝ
 m' : ℝ -- rhs exp constants for estimates
 c' : ℝ
 paid : ∀ᶠ n in atTop, ∀ m:Side, ∀ a: K.Allowed m n,
   Shots K.V K.T K.J K.η (K.monthSize m a.1) (loom m) n (sharp m n) (warm m n) (wave n) (wave' n) (B₀ n) (tilt n) (tilt' n) K.h K.R0 K.δ ∧
   Delta K.P (sharp m n 0) (warm m n 0) (loom m 0) (Burn.bill m.val n K.b₀ m') ∧
   Burn.presrec m.val c'≤ ‖vac0 K.P (warm m n 0) (loom m 0)‖
 lawn : ∀ m, K.takes m → ∀ j:ℕ, LoomLaw (loom m j) K.w

namespace Histories
variable {K : Calibration} (P : Histories K)
def cap {m : Side} (n : ℕ) (F : Mark (K.c m)) := atZero K.P (P.sharp m n) (P.loom m) F
lemma stepSame : ∀ᶠ n in atTop, ∀ m k : Side, K.Allowed m n → K.Allowed k n → ∀ i≤n, (P.sharp m n i).beta=(P.sharp k n i).beta ∧ (P.warm m n i).beta=(P.warm k n i).beta := by
 filter_upwards [P.paid] with n p
 intro m k h g i hi; obtain ⟨a,d,t⟩:= p m h; obtain ⟨b,H,e⟩:= p k g
 induction i with
 | zero=> exact ⟨a.sharp.note.color.trans b.sharp.note.color.symm,a.pivot.trans b.pivot.symm⟩
 | succ i ih=> obtain ⟨t,v⟩:= ih (by omega); constructor; · linarith only [a.sharp.note.shift i hi,b.sharp.note.shift i hi,t]
               linarith only [a.shiftY i hi,b.shiftY i hi,v]

variable {m : Side} (k : ℕ → ℕ) (p : Tendsto k atTop atTop) (t : K.takes m)
include t p
lemma eventuallyPaid : ∀ᶠ i in atTop, AtUV K.P (P.loom m) (P.sharp m) (P.warm m) K.b₀ P.c' P.m' (k i) := by
 filter_upwards [p.eventually P.paid, p.eventually (K.eventually_allowed t), p.eventually (eventually_gt_atTop 0)] with x h a v
 obtain ⟨p,h,hx⟩:=h m a; exact p.atComparison v h hx _ _ rfl rfl
lemma divisions : ∀ᶠ i in atTop, partitionZ (P.sharp m (k i) 0) K.P (P.loom m 0)≠0 ∧ partitionZ (P.warm m (k i) 0) K.P (P.loom m 0)≠0 := (lowerAt_fixed p (P.eventuallyPaid k p t)).mono (fun _ a=> a.2)
lemma uvSign {f : Mark (K.c m)} (a : AtSupport false (K.fits m) f) {Y : ℂ}
   (h : Tendsto (fun i=> P.cap (k i) (squareMark K.plane0 3 f f)) atTop (𝓝 Y)) : 0 ≤ Y := by
  refine fixedPeriod p (P.eventuallyPaid k p t) K.η K.J.d (steps K.V m K.B) P.wave' K.ζ 3 K.buffer K.legal K.R.coarse (P.lawn m t) ?_ a _ h
  filter_upwards [p.eventually P.paid, p.eventually (K.eventually_allowed t)] with x h a
  let p := (h m a).1
  exact ⟨⟨p.heat.choose⟩, p.warm_grant⟩
end Histories
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Histories.uvSign
