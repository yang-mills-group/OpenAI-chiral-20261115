import YM.SU5.MacroSix.Ceremony
import Mathlib.Topology.MetricSpace.Thickening
/-!
# Perturbable body center positions, and survival with slack

In `Main.lean` the perturbation assertion in all smooth, real pose test densities
is even in L¹ cost on them (with the fixed probe resolution `s` and `n`, and full
frame checks). In case of question about perturbing *centers*: they're already the
pose parameters of the test densities. Here we show this stability also explicitly as on
independent translations of the physically supported smear (contrast: `fieldAt` uses translations
on the tick grid of each `t`; on the larger measurement `t → ∞` we're talking
about all Vantage translations). One may compose shifts or perturb weights independently.
This is not covariance under Euclidean rotations! `testMotion` and `motionPlace`
also verify the support action and the actual formula on the tick-realizable translations.
All these are supplementary cost theorems, not needed to establish that the tests can
be chosen macroscopic or that they travel. At the end, includes stability of the Part(i)
**independently perturbed test pairs** (even beyond translations) with the same real-floor
quota (with any strict slack), explicitly even on the consultation at the micro
(observing-resolution) scales.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3600
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.MacroSix
open Function Set Filter MeasureTheory Metric
open scoped Topology ContDiff
variable {I : Type} [Fintype I]
local notation "X"=> (I → ℝ)
-- Translate the TEST, physical Vantage, not translating charged/co-moving labels internally.
def tomorrow (f : (I → ℝ) → ℝ) (x : I → ℝ) : (I → ℝ) → ℝ := fun y => f (y+ -x)

-- includes all derivative & support qualifications for arbitrary parameter roster
lemma goingForward (f : X → ℝ) (x : X) (p : SmoothDensity f) : SmoothDensity (tomorrow f x) where
  smooth:= p.smooth.comp (contDiff_id.add contDiff_const)
  compact:= p.compact.comp_homeomorph (Homeomorph.addRight (-x))
  nonneg _:= p.nonneg _
  mass:= (integral_add_right_eq_self f (-x)).trans p.mass
omit [Fintype I] in
lemma muchLater (f : X → ℝ) (x : X) : tsupport (tomorrow f x)=(fun y↦ y + x) '' (tsupport f) := by
  let H:= Homeomorph.addRight (-x)
  change tsupport (f ∘ H)= _
  rw [tsupport_comp_eq_preimage]
  ext u; constructor
  · intro v; exact ⟨H u,v,by simp [H]⟩
  rintro ⟨y,p,rfl⟩; simpa [H] using p
lemma horizon_stays (f : X→ℝ) (p : SmoothDensity f) (D : Set (X)) (h : tsupport f⊆ D) (u : IsOpen D) :
    ∀ᶠ r in 𝓝 (0:X), tsupport (tomorrow f r)⊆ D := by
  obtain ⟨δ,q,b⟩:= p.compact.exists_cthickening_subset_open u h
  filter_upwards [Metric.ball_mem_nhds (0:X) q] with v t
  rw [muchLater]
  rintro x ⟨i,y,rfl⟩; exact b (Metric.mem_cthickening_of_dist_le _ i δ _ y (by simpa [dist_eq_norm]
    using (show dist v 0 ≤ δ from (show dist v 0 < δ from t).le)))

-- the ∫ cost: same argument as `Grid.Setup.shiftBudget`. 
lemma future_shrinks (f : X→ℝ) (p : SmoothDensity f) :
    Tendsto (fun v ↦ discrepancy (tomorrow f v) f) (𝓝 (0:X)) (𝓝 0) := by
  obtain ⟨A,h⟩ := (show IsCompact (tsupport f) from p.compact).isBounded.subset_closedBall (0:X)
  obtain ⟨c,u⟩ := p.smooth.continuous.bounded_above_of_compact_support p.compact
  let D := closedBall (0:X) (A+1)
  have hm : MeasurableSet D := Metric.isClosed_closedBall.measurableSet
  let B := D.indicator fun _ ↦ c+c
  have hB : Integrable B := (integrable_indicator_iff hm).mpr (integrableOn_const
    (isCompact_closedBall _ _ |>.measure_lt_top.ne))
  let F (v : X) (x : X) := ‖tomorrow f v x-f x‖
  have he : Tendsto (fun v ↦ ∫ x, F v x) (𝓝 (0:X)) (𝓝 (∫ _ : X,(0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall (fun v ↦
      ((goingForward f v p).smooth.continuous.sub p.smooth.continuous).norm.aestronglyMeasurable))
      ?_ hB ?_
    · filter_upwards [Metric.ball_mem_nhds (0:X) zero_lt_one] with v Hv
      apply ae_of_all; intro x
      rw [Real.norm_of_nonneg (show 0 ≤ F v x from norm_nonneg _)]
      by_cases e : x∈D
      · rw [show B x=c+c from Set.indicator_of_mem e _]
        exact (norm_sub_le ..).trans (add_le_add (u _) (u _))
      have hz : f x=0 := by
        by_contra k
        exact e (Metric.closedBall_subset_closedBall (by linarith) (h (subset_tsupport f k)))
      have ht : f (x+-v) = 0 := by
        by_contra k
        have he := h (subset_tsupport f k)
        refine e ((dist_triangle _ (x+-v) _).trans ?_)
        have hg : dist x (x+-v) ≤ 1 := by
          simpa using (show dist v 0 ≤ 1 from (show dist v 0 < 1 from Hv).le)
        linarith [Metric.mem_closedBall.mp he]
      simp [F,hz,ht,B,e,tomorrow]
    apply ae_of_all; intro i
    have ht : ContinuousAt (fun x : X ↦ f (i + -x)) 0 := (p.smooth.continuous.comp (continuous_const.add continuous_neg)).continuousAt
    simpa only [F,Pi.sub_apply,tomorrow,neg_zero,add_zero,sub_self,norm_zero] using (ht.sub (continuousAt_const (y:=f i))).norm.tendsto
  rw [integral_zero] at he; exact he
end YM.MacroSix

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Aria Pockets
open _root_.YM.MacroSix _root_.YM.MacroSix.ClockTest
namespace Spine
variable (P : Spine) (R : P.Register) (s n t : ℕ) (x : P.Spectrum0 3) (J : P.Ellis 3 x)
  (f g : Vantage → ℝ)

lemma motionPlace (A : P.Apron) (y : Vantage) : P.occupiedSpace (tomorrow f y) A=
    (fun x↦ x+y) '' (P.occupiedSpace f A) := by
  simp_rw [P.positions_footprint, muchLater]; ext x; constructor
  · rintro ⟨u,⟨v,p,rfl⟩,h⟩; refine ⟨x-y,⟨v,p,fun i ↦ ?_⟩, sub_add_cancel ..⟩
    rw [Pi.sub_apply,show x i-y i-v i=x i-(v+y) i from by rw [Pi.add_apply]; abel]; exact h _
  rintro ⟨v,⟨u,p,w⟩,rfl⟩; exact ⟨u+y,⟨u,p,rfl⟩,fun i ↦ by simpa only [Pi.add_apply,add_sub_add_right_eq_sub] using w i⟩

lemma testMotion (A : P.Apron) (y : Cover) (h : HasCompactSupport f) :
    P.chartAll y (P.smearField t f A)= P.smearField t (tomorrow f (P.pose t y)) A := by
  let T:=P.chartAll y; let S(v: Cover):= P.fieldAt t A v
  let a i:= f (P.pose t i)
  have hv : HasFiniteSupport (fun i ↦ (a i:ℂ) • S i) := (P.pose_finite t f h).subset (by
    intro i u q
    have hp : a i = 0 := q
    exact u (by change (a i:ℂ) • S i = 0; rw [hp,Complex.ofReal_zero,zero_smul]))
  unfold smearField MacroSix.finiteTest
  rw [map_smul]; congr 1
  dsimp only [S,a] at hv; dsimp only [Function.comp_apply]; rw [map_finsum _ hv]
  apply finsum_eq_of_bijective (fun i : Cover ↦ i + y) ((Equiv.addRight y).bijective)
  intro i
  dsimp only [tomorrow]; rw [map_smul,show P.pose t (i+y)=P.pose t i+P.pose t y from
    MacroSix.Grid.place_add (P.meshSize t) _ _,add_neg_cancel_right,fieldAt,P.chart_ids]
  rw [add_comm y i]; rfl

lemma OnFrame.commonMove (y : Vantage) {c : ℝ} (h : P.OnFrame s n f g c) :
    P.OnFrame s n (tomorrow f y) (tomorrow g y) (c+y 3) := by
  constructor
  · intro x p; rw [muchLater] at p; obtain ⟨v,u,rfl⟩:= p; dsimp only; rw [Pi.add_apply]; linarith [h.before v u]
  intro x p; rw [muchLater] at p; obtain ⟨v,u,rfl⟩:= p; dsimp only; rw [Pi.add_apply]; linarith [h.after v u]

variable {T : Type*} (L : Filter T) {a b : T → Vantage} (ha : Tendsto a L (𝓝 0)) (hb : Tendsto b L (𝓝 0))
section together
include ha hb
lemma OnFrame.shifts_keep {c : ℝ} (v : P.OnFrame s n f g c) (p : SmoothDensity f) (q : SmoothDensity g) :
    ∀ᶠ r in L, P.OnFrame s n (tomorrow f (a r)) (tomorrow g (b r)) c := by
  let w:ℝ:= P.sixWidth s n 3
  filter_upwards [ha.eventually (horizon_stays f p _ (show tsupport f⊆{x| x 3 + w < c} from
    (fun _ ↦ v.before _)) (isOpen_lt ((continuous_apply _).add continuous_const) continuous_const)),
    hb.eventually (horizon_stays g q _ (show tsupport g⊆{x| c < x 3 - w} from
    (fun _ ↦ v.after _)) (isOpen_lt continuous_const ((continuous_apply _).sub continuous_const)))] with r t y
  exact ⟨fun _ h ↦ t h,fun _ h ↦ y h⟩

lemma Questions.openCenters (p : P.Questions s n f g) :
    P.Through s n f g L (fun r ↦ tomorrow f (a r)) (fun r ↦ tomorrow g (b r)) := by
  obtain ⟨c,u⟩:= p.looking
  refine ⟨?_,(future_shrinks f p.fden).comp ha,(future_shrinks g p.gden).comp hb⟩
  exact (OnFrame.shifts_keep _ s n f g L ha hb u.funds p.fden p.gden).mono fun r h ↦
    ⟨goingForward f _ p.fden,goingForward g _ p.gden,_,h⟩

/-- Moved supports (can also first move into a wider still-qualified pair of rectangles). -/
lemma Achieves.stillPaints (A B : RectanglePose) (h : P.Achieves s n x A B f g) : ∀ᶠ i in L,
    tsupport (tomorrow f (a i)) ⊆ A.paints ∧ tsupport (tomorrow g (b i)) ⊆ B.paints :=
  (ha.eventually (horizon_stays f h.smoothLeft A.paints h.paintsLeft A.open_paint)).and
    (hb.eventually (horizon_stays g h.smoothRight B.paints h.paintsRight B.open_paint))
end together

include J
lemma Realized.slackFloor (p : P.Realized R s n x f g)
    (A B : T → Vantage → ℝ) (h : P.Through s n f g L A B) (q : P.StockClear n) (b d : ℝ) (w : b<d)
    (t' : ReFloor (P.measureField s n f g x) d) :
    ∀ᶠ i in L, ∀ᶠ t in atTop, ReFloor (P.measureAt s n t (A i) (B i) x) b := by
  obtain ⟨a,e,E⟩:= exists_between w
  obtain ⟨z,r⟩:= Realized.perturb P R s n x J f g p q L A B h
  filter_upwards [r, (ReFloor.retain E t' L _ (fun i j ↦ tendsto_pi_nhds.mp
    (tendsto_pi_nhds.mp z i) j))] with i v p
  exact ReFloor.retain e p atTop _ (fun i j ↦ tendsto_pi_nhds.mp (tendsto_pi_nhds.mp v.limits i) j)

-- common motion of these real test placements (all R^4 and widths price holds). It's the
-- actual licensed measurement that has this property, not a postulate of separately coherent interpretations.
lemma tomorrowAnswer (y : Vantage) {c : ℝ} (h : P.OnFrame s n f g c) :
    P.measureField s n (tomorrow f y) (tomorrow g y) x = P.measureField s n f g x := by
  have hv:= OnFrame.commonMove P s n f g y h
  ext1 i j
  let T (v w: Vantage):=P.fieldKernel s n x v w
  let Z:= (volume:Measure (Vantage×Vantage))
  let K(v w:Vantage) := T v w i j; let U := weightKernel K f g
  let L: Vantage×Vantage := (-y,-y)
  let H := weightKernel K (tomorrow f y) (tomorrow g y)
  have he (v:Vantage×Vantage) : H v= U (v+L):= by
    let u:=v.1; let x':=v.2
    unfold H U weightKernel
    change (f (u+-y):ℂ) * (g (x'+-y):ℂ) * K u x' =(f (u+-y):ℂ)*(g (x'+-y):ℂ)*K (u+-y) (x'+-y)
    by_cases p : f (u+-y) = 0; · simp [p]
    by_cases q : g (x'+-y) = 0; · simp [q]
    have ht : _ := (h.factors (subset_tsupport f (show f _≠0 from p)) (subset_tsupport g (show g _ ≠0 from q))).1
    have hh: P.fieldOrder s n 3 u x':= (hv.factors (subset_tsupport _ p) (subset_tsupport _ q)).1
    have hz : T u x' = T (u+-y) (x'+-y) := by
      unfold T; rw [P.fieldKernel_move _ _ x J u x' hh,P.fieldKernel_move _ _ x J _ _ ht]
      congr 1; abel
    unfold K; rw [hz]
  exact (integral_congr_ae (ae_of_all Z he)).trans (integral_add_right_eq_self (μ:=volume.prod volume) U L)

-- no extra positive orientation assertion even after pert.
end Spine

#print axioms Spine.Questions.openCenters
#print axioms Spine.Realized.slackFloor
#print axioms Spine.motionPlace
#print axioms Spine.testMotion
#print axioms Spine.tomorrowAnswer
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

section bill
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
namespace YM.MacroSix
open RealInnerProductSpace Matrix
attribute [local instance] CF.opCStarAlgebra
variable {J : Type*} [Fintype J] [DecidableEq J] {A : Matrix J J ℂ} {b : ℝ}
local notation "VX" a:max=> (WithLp.toLp 2 a:EuclideanSpace ℂ J)

-- if wanting to read `ReFloor` (positive real quota on Hermitian part)
-- on possibly NON-Hermitian answers at perturbed poses. Stronger than just
-- a lower bound on the real part of the diagonals or zero-comparison.
lemma ReFloor.ray_cost (p : ReFloor A b)(x : J→ℂ) :
    b*‖(WithLp.toLp 2 x: EuclideanSpace ℂ J)‖^2 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
  have hp := ((Matrix.le_iff).1 p).dotProduct_mulVec_nonneg x
  let W := star x
  let T := VX x
  have he : W ⬝ᵥ (star A *ᵥ x) = star (W ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.dotProduct_mulVec,← Matrix.star_mulVec, Matrix.star_dotProduct]
  have h : W ⬝ᵥ x= (↑(‖T‖^2):ℂ) := by
    rw [dotProduct_comm]
    exact (EuclideanSpace.inner_eq_star_dotProduct T T).symm.trans
      ((inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (VX x)).trans (by norm_cast))
  change 0 ≤ W ⬝ᵥ ((_ - _) *ᵥ x) at hp
  rw [hermitianRay,sub_mulVec,smul_mulVec,add_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,
      dotProduct_smul,dotProduct_add,he,dotProduct_smul,h,Complex.real_smul, smul_eq_mul] at hp
  rw [Complex.le_def] at hp
  simp at hp
  change b*‖T‖^2 ≤ _; unfold W T at *; norm_cast at hp; linarith

lemma ReFloor.transfer_cost (p : ReFloor A b)(x : J→ℂ) :
    b*‖(WithLp.toLp 2 x: EuclideanSpace ℂ J)‖ ≤ ‖(WithLp.toLp 2 (A*ᵥ x): EuclideanSpace ℂ J)‖ := by
  by_cases e : x=0; subst x; simp -- scoping
  have hp := (p.ray_cost x).trans (Complex.re_le_norm _)
  let U:= VX x; let V:= VX (A*ᵥ x)
  rw [dotProduct_comm,show (A *ᵥ x) ⬝ᵥ star x=inner ℂ U V from rfl] at hp
  have hx : b*‖U‖^2 ≤ ‖U‖ * ‖V‖:= hp.trans (norm_inner_le_norm ..)
  have he : 0<‖U‖:= norm_pos_iff.mpr (fun p ↦ e (congrArg WithLp.ofLp p))
  change b*‖U‖ ≤ ‖V‖
  nlinarith
end YM.MacroSix
#print axioms YM.MacroSix.ReFloor.transfer_cost
end bill
