import YM.SU5.WakeFields.Sites


set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Filter
open Function
open Metric
open MeasureTheory
open Lattice Cube Lat Skye Lifted EmberWind
open Py Py.Rate LocalLimit FullBill Preparation Yoke Journey
open Satin Fock
open Ballad
open scoped Topology BigOperators Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Onyx (riseX)
open YM.Stationary (Gaia)

namespace Resolving

open Finset
open EmberWind.Staff
open CF.Pannier.Chancel
open Signal.Interval (separationCost)
open Tapestry

open PhaseChoice Reconstruction

/-- In scaled physical (microscope) units. -/
def lower : Gaia := 0
def incline : Gaia := WithLp.toLp 2 ![1,(1:ℝ),6,1]
abbrev primary : PlaqAxes := ⟨(0,1),by decide⟩

lemma incline_eq (j : Axis) : incline j = if j = (2:Axis) then 6 else 1 := by
  fin_cases j <;> rfl

lemma inclined : incline ≠ 0 := by
  intro h; have t := incline_eq 0; rw [h] at t; norm_num [show (0:Axis)≠2 by decide] at t

private lemma pencil_price {x : Gaia} (v : x 3 ≠ 0) (h : x ≠ 0) : Hiro.shotL x Spine.pairMood Spine.pairMood ≠ 0 := by
  have hx := norm_pos_iff.mpr h
  change Onyx.pencil x (Window.dnSpin 0) (Window.upSpin 0) ≠ 0
  rw [Onyx.pencil,Matrix.smul_apply,Cordial.quaternion,Complex.real_smul]
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast ne_of_gt (show 0<(Real.pi ^ 2* ‖x‖^4)⁻¹ by positivity)
  intro q
  apply v
  have p := congrArg Complex.re q; simpa using p

private lemma slopeCurves : Maxwell.bareCurl 0 1 0 1 incline ≠ 0 := by
  have t : ‖incline‖^2 = 39 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ,Axis,incline_eq,incline]
  rw [Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad inclined,Maxwell.Bare.opp_grad inclined]
  have n := Maxwell.normal_pos
  simp only [↓reduceIte, Maxwell.second_Green inclined, t, incline_eq, basis_eq, mul_one]
  norm_num [show (0:Axis)≠2 by decide,show (1:Axis)≠2 by decide]
  nlinarith only [n]

abbrev claim : ℂ := shot primary primary Spine.pairMood Spine.pairMood lower incline (lower-incline)
lemma claim_pos : 0 < ‖claim‖ := by
  have hk : (incline 3:ℝ)≠0 := by norm_num [incline_eq,show (3:Axis)≠2 by decide]
  have u : Hiro.shotR Spine.pairMood Spine.pairMood (X:= -incline)≠0 := by
    unfold Hiro.shotR; rw [neg_neg]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pencil_price (neg_ne_zero.mpr hk) (neg_ne_zero.mpr inclined)))
      (pencil_price hk inclined)
  letI := Thera.yet_one.nontrivial_color
  have v : 0 < SU.group.lieDim := by rw [Gauge.lieDim, ← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
  unfold claim shot lower; rw [zero_sub]
  refine norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (by norm_num) u) ?_)
  change (Fintype.card (Fin SU.group.lieDim):ℂ) * (↑(Maxwell.bareCurl 0 1 0 1 (-incline)):ℂ)≠ 0
  rw [Fintype.card_fin, Maxwell.Bare.even inclined]
  exact mul_ne_zero (by exact_mod_cast v.ne') (by exact_mod_cast slopeCurves)

abbrev earlyDoor (d : ℝ) := cellAt lower d (1/8)
abbrev lateDoor (d : ℝ) := cellAt incline d (1/8)

/-- strictly positive clearance in each Euclidean projection, even the stronger axis-2
condition for prospective spacelike tests (time axis 3). -/
def Slant (δ : ℝ) (a b : Set RSpace) :=
  ∀ x∈a, ∀ y∈b, (∀ j : Axis, x j + δ < y j) ∧ x 2 + δ + |x 3-y 3| < y 2

theorem slants (d : ℝ) (p : 0 < d) : Slant (d/2) (earlyDoor d) (lateDoor d) := by
  intro x u y v
  have h(j : Axis) : - d/8 < x j ∧ x j < d/8 := by
    have hu : |x j - d * lower j| < d * (1/8) := u j
    have hy : lower j = 0 := rfl
    rw [hy,mul_zero,sub_zero] at hu
    obtain ⟨t,v⟩ := abs_lt.mp hu; constructor <;> linarith only [t,v]
  have V(j : Axis) := abs_lt.mp (show |y j- d* incline j| < d * (1/8) from v j)
  constructor
  · intro j; have hv := V j |>.1; rw [incline_eq] at hv; have hq:= (h j).2
    split_ifs at hv <;> linarith

  rcases (h 3) with ⟨g,b⟩; obtain ⟨e,k⟩ := V 3; have y' := (V 2).1; have t: (3:Axis) ≠ 2 := by decide
  simp only [incline_eq,if_neg t, ite_true, mul_one] at y' e k
  rw [abs_of_nonpos] <;> linarith [(h 2).2]

variable (P : Spine)
def HeldAt (s : ℕ) (U : Set RSpace) (X : Family P.calibration) (S : Finset Cover) : Prop :=
  InTest P.calibration true S false X ∧ CovCover P.calibration X ∧
    silhouette P.par P.width s S ⊆ U

abbrev later (s n : ℕ) := stream P.run P.large P.refineTest s n

lemma HeldAt.earns {s S U X} (m : HeldAt P s U X S) (n : ℕ) :
    HeldAt P (s+n) U (later P s n X) (volumeAround P.par P.width n S) :=
  ⟨(proceeds P.run P.large P.history.circuit s n m.1).1,
    ((obs_in ..).1 (chroma P.run P.large P.history.circuit s n ((obs_in ..).2 ⟨m.1,m.2.1⟩))).2,
    stamped_later P s n U m.2.2⟩

lemma HeldAt.earned {s S U X} (m : HeldAt P s U X S) (n : ℕ) :
    P.E (s+n) (later P s n X) = P.E s X :=
  (proceeds P.run P.large P.history.circuit s n m.1).2

def averageCredit (s : ℕ) (X Z : Family P.calibration) := P.E s (X*Z)-P.E s X*P.E s Z

def confirmedCredit (s i j : ℕ) (X Z : Family P.calibration) := let p := sharp P.run P.large s i j; p (X*Z)-p X*p Z

lemma common_credit (f β) (h : Tuned P f β) (g : P.PhysicalWakeGram) {A : ℝ} (p : 0 < A)
    {u v : ℕ → Cover} (U : Appoint P.par A u lower) (V : Appoint P.par A v incline) :
    let A' := stencils P β A u primary Spine.pairMood 4
    let B' := stencils P β A v primary Spine.pairMood 4
    Tendsto (fun s => averageCredit P s (A' s) (B' s)) atTop (𝓝 claim) ∧
    Tendsto (fun i : ℕ × ℕ => confirmedCredit P i.1 (physicalPeriod P f i.2) (physicalCut P f i.2) (A' i.1) (B' i.1))
        towerLimit (𝓝 claim) := by
  intro A' B'
  obtain ⟨x,y,h⟩ := cashAdj P primary primary Spine.pairMood Spine.pairMood 4 f β h g p le_rfl U V (Ne.symm inclined)
  have a := h.realized.sub (x.realized.mul y.realized)
  have b := h.approved.sub (x.approved.mul y.approved)
  rw [zero_mul,sub_zero] at a b; exact ⟨a,b⟩

lemma held_price {s X Z A B S T} (u : HeldAt P s A X S) (v : HeldAt P s B Z T)
    (w : Disjoint A B) (n : ℕ) :
    averageCredit P (s+n) (later P s n X) (later P s n Z) = averageCredit P s X Z := by
  have he : Detached P.par P.width S T := separatedPhys (supported_iff.mpr u.2.2) (supported_iff.mpr v.2.2)
    (Disjoint.preimage (fun x:RSpace => fun j:Axis => x j / 2) w)
  unfold averageCredit; rw [u.earned P, v.earned P, later, ←woven_product P.run P.large P.history.circuit s n u.1 v.1 he,
    (proceeds P.run P.large P.history.circuit s n (show InTest P.calibration true (S∪T) false (X*Z) from (u.1.mono subset_union_left).mul (v.1.mono subset_union_right))).2]

-- full proof tasks will use same `X x` character as other polls; at this checkpoint
-- this is unselected `P.E`. Login poll permissions retained. Not a statement that either
-- operand is a pure-sector operator. It's a calibrated estimate of a *mixed term*.
structure InitialGeometry (P : Spine) (A : ℝ) (f β) (u v : ℕ → Cover) (s : ℕ) : Prop where
  layout : PaidPair P (A+1) 4 s (adjacent (u s) primary Spine.pairMood)
                      (adjacent (v s) primary Spine.pairMood) (side P.run (physicalPeriod P f s) s)
        -- moreover on all n; specify explicitly
  all_n (n : Side) : PaidPair P (A+1) 4 s (adjacent (u s) primary Spine.pairMood)
                      (adjacent (v s) primary Spine.pairMood) n
  leftProbe : HeldAt P s (earlyDoor (apertureScale P A s)) (stencils P β A u primary Spine.pairMood 4 s) (skyDeck (nodeC (u s)) (4+8))
  rightProbe : HeldAt P s (lateDoor (apertureScale P A s)) (stencils P β A v primary Spine.pairMood 4 s) (skyDeck (nodeC (v s)) (4+8))
  gap : Slant (apertureScale P A s/2) (earlyDoor (apertureScale P A s)) (lateDoor (apertureScale P A s))
  positive : ∀ n : ℕ, ‖claim‖/2 < ‖averageCredit P (s+n) (later P s n (stencils P β A u primary Spine.pairMood 4 s)) (later P s n (stencils P β A v primary Spine.pairMood 4 s))‖
  precursors : ∀ᶠ n in atTop, ‖claim‖/2 < ‖confirmedCredit P s (physicalPeriod P f n) (physicalCut P f n)
                              (stencils P β A u primary Spine.pairMood 4 s) (stencils P β A v primary Spine.pairMood 4 s)‖

lemma groundPrice (f β) (h : Tuned P f β) (g : P.PhysicalWakeGram) (A : ℝ) (p : 0 < A)
    (u v : ℕ → Cover) (U : Appoint P.par A u lower) (V : Appoint P.par A v incline) :
    ∀ᶠ s in atTop, InitialGeometry P A f β u v s := by
  obtain ⟨W,Q⟩ := common_credit P f β h g p U V
  let X := stencils P β A u primary Spine.pairMood 4
  let Y := stencils P β A v primary Spine.pairMood 4
  filter_upwards [P_p U, P_p V, paid P 4 le_rfl p (lt_add_one A) primary primary Spine.pairMood Spine.pairMood U V,
            W.norm.eventually (lt_mem_nhds (half_lt_self claim_pos)), (towerLate _).1 (Q.norm.eventually (lt_mem_nhds (half_lt_self claim_pos)))] with s h g v H t
  let d := apertureScale P A s; have hv := apert_pos P s A; let z:= slants d hv
  refine ⟨v _, v, h, g,z,fun n => ?_, t⟩
  rw [held_price P h g (Set.disjoint_left.mpr fun x a b => ?_) n]; exact H
  have ht: x 0 + d/2 < x 0 := (z x a x b).1 0; change 0<d at hv; linarith only [hv,ht]
where
  P_p {x : Gaia} {u : ℕ → Cover} (g : Appoint P.par A u x) :
      ∀ᶠ s in atTop, HeldAt P s (cellAt x (apertureScale P A s) (1/8))
                                  (stencils P β A u primary Spine.pairMood 4 s) (skyDeck (nodeC (u s)) (4+8)) := by
    filter_upwards [apartment P p g (1/8) (by positivity) (4+8)] with s h
    have Q := usable P primary Spine.pairMood 4 β A (u s) le_rfl s; exact ⟨Q.1,Q.2,h⟩

universe ν

/-- Checkpoint 1: purchase on the wake election. This reaches a force-ingredient price
   living at the scalable microscope for all high `s`, then also at any one such (arbitrarily
   fine) fixed `s` physically slanted separation. Uses the two *mixed* Spin+plaquette
   stencils (not the proposed comparator) and unselected mean.
   Refinement in `InitialGeometry.positive` is **resolution transport**, not a claim
   of persistence when shrinking the two stencils while keeping external smears fixed. -/
theorem wakeElectionWithMixedHistory (X : TintDemand) (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ),
      Spine.PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      Spine.QualifiedWakeReadout.{ν} P K ∧ P.PhysicalWakeGram ∧
      ∀ f : ℕ → ℕ, StrictMono f →
      ∃ c : ℕ → ℕ, StrictMono c ∧ ∃ β, Tuned P (f ∘ c) β ∧
      ∀ A : ℝ, 0 < A → ∀ (d : ℕ), 0 < d → ∀ D : Cover,
      ∃ u v : ℕ → Cover, (∀ s (i : Axis), (d:ℤ) ∣ u s i - D i) ∧
           (∀ s (i : Axis), (d:ℤ) ∣ v s i - D i) ∧
           P.PencilLease A lower incline u v ∧
           (∀ᶠ s in atTop, InitialGeometry P A (f ∘ c) β u v s) := by
  obtain ⟨P,K,E,h,pose,T,F⟩ := Spine.wakeElectionWithPhysicalGram.{ν} X Mc
  refine ⟨P,K,E,h,pose,T,F,fun f r => ?_⟩
  obtain ⟨c,β,v,p⟩ := tuneFurther P r; refine ⟨c,v,β,p, fun A g d w D => ?_⟩
  obtain ⟨U,L⟩ := P.announces d w g D lower; obtain ⟨V,D⟩ := P.announces d w g D incline
  exact ⟨_,_,L,D,⟨U,V,fun h=> (inclined h.symm).elim⟩,groundPrice P _ β p F A g _ _ U V⟩

#print axioms groundPrice
#print axioms wakeElectionWithMixedHistory
end Resolving
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
