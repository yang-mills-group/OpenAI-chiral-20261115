import YM.SU5.LoomForce.RungObstruction
import SU5SatinWakePhysicalGramNovember8
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
open Vale (hat)

/-!
Apply the limits to an elected layout. Use *these* particular mixed stamps,
both located at the same positions as the matter polls of HoldRead.
Keep the strict gap **on the Wake (scale r_s)** even on the native resolution net.
-/

def touchPoint : Gaia := WithLp.toLp 2 (fun i : Axis => if i = 2 then 4 else 1)

omit P in
lemma point_rule (i : Axis) : touchPoint i = if i = 2 then 4 else 1 := rfl

omit P in
lemma point_large (i : Axis) : 0 < touchPoint i := by rw [point_rule]; split <;> norm_num

omit P in
lemma point_ne : touchPoint ≠ 0 := fun v => (by
  have h := point_large 2
  rw [v] at h
  exact (lt_irrefl (0:ℝ) h))

local notation "F₀" => Prototype.goldF
local notation "g₀" => pairMood -- defined in Spine

def payoff : ℂ := wakeFee F₀ F₀ g₀ g₀ (-touchPoint) (-touchPoint)

omit P in
lemma payoff_positive : 0 < ‖payoff‖ := by
  let x := touchPoint
  let D := Real.pi^2*‖x‖^4
  have hx : -x ≠ 0 := neg_ne_zero.mpr point_ne
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr point_ne
  have hD : 0 < D := by unfold D; positivity
  have he : shotR g₀ g₀ (X:=-touchPoint)≠0 := by
    have hz : kP20 x ≠ 0 := by
      rw [shapeWeyl]
      unfold curlWeyl
      exact mul_ne_zero (by norm_num) (mul_ne_zero
        (div_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr hD).ne') (by norm_num)) (fun v => by
          have k := congrArg Complex.re v; simp only [Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
            sub_zero, add_zero, Complex.zero_re] at k
          exact (point_large 3).ne' k))
    change -60*kP20 (-x)*kP20 (- -x)≠0
    rw [k_flip,neg_neg]; exact mul_ne_zero (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hz)) hz
  have hu : speckleV F₀ F₀ SU.group (-x)≠0 := by
    have hl: 4 ≤ ‖x‖ := (le_of_eq (by rw [Real.norm_eq_abs,
      show x (2:Axis) = 4 by unfold x; rw [point_rule]; simp]; norm_num : (4:ℝ) = ‖x 2‖)).trans (PiLp.norm_apply_le x 2)
    have h : Maxwell.bareCurl 0 1 0 1 (-x) =
        (4*Maxwell.normal)*(‖x‖^2)⁻¹^2-(16*Maxwell.normal)*(‖x‖^2)⁻¹^3 := by
      rw [Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad hx, Maxwell.Bare.opp_grad hx]
      simp only [↓reduceIte,Maxwell.second_Green hx, norm_neg, PiLp.neg_apply]
      unfold x; norm_num [point_rule, show (0:Axis)≠2 from by decide,show (1:Axis)≠2 from by decide]; ring
    have hk : 0 < Maxwell.bareCurl 0 1 0 1 (-x) := by
      rw [h]; apply sub_pos.mpr
      have hr := Maxwell.normal_pos
      suffices h : 4 < (‖x‖^2) by field_simp; nlinarith -- adjust
      nlinarith only [hp,hl]
    haveI:Nontrivial SU.group.Color:=Thera.yet_one.nontrivial_color
    have ht:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
    change (Fintype.card (Fin SU.group.lieDim):ℂ)*(Maxwell.bareCurl 0 1 0 1 (-x))≠0
    rw [Fintype.card_fin]; exact mul_ne_zero (Nat.cast_ne_zero.mpr ht.ne') (Complex.ofReal_ne_zero.mpr hk.ne')
  exact norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num : (1/2:ℂ)≠0)) he) hu)

def widePlenum (U V : Set RSpace) (δ : ℝ) : Prop := ∀ u ∈ U, ∀ v ∈ V,
  (∀ i, δ ≤ v i-u i) ∧ |v (3:Axis)-u 3| + δ ≤ v 2-u 2

omit P in
private lemma clearance' (δ : ℝ) (h : 0 < δ) (y z : RSpace)
    (v : ∀ i, |y i| < δ*(1/4))
    (u : ∀ i, |z i-δ*touchPoint i| < δ*(1/4)) : (∀ i, δ/2≤ z i - y i) ∧
    |z (3:Axis)-y 3| + δ/2 ≤ z 2-y 2 := by
  have he (i) : δ*(if i=(2:Axis) then 4 else 1)-δ/2 < z i - y i ∧
        z i - y i < δ*(if i=(2:Axis) then 4 else 1)+δ/2 := by
    obtain ⟨p,g⟩ := abs_lt.mp (u i); obtain ⟨e,w⟩ := abs_lt.mp (v i)
    rw [point_rule i] at p g; constructor <;> linarith
  constructor
  · intro i; by_cases t:i=2; all_goals have h:= (he i).1; simp only [t,ite_true,ite_false] at h ⊢; linarith
  have hd: (3:Axis)≠2 := by decide
  obtain ⟨p,g⟩:= he 3; have h' := (he 2).1; simp only [ite_true,hd,ite_false] at p g h'
  rw [abs_of_pos (by linarith)]; linarith

lemma visits_clear (A : ℝ) (s : ℕ) : widePlenum (rescaledFit P s A 0 (1/4))
    (rescaledFit P s A touchPoint (1/4)) (rungSpace P A s / 2) := fun y t z q =>
  clearance' _ (rungSpace_pos ..) y z (fun i=> by simpa using t i) q

variable (A : ℝ) (u v : ℕ → Cover)
def staffAt (q : Cover) : Staff := adjacent q F₀ g₀
def billAt (s : ℕ) (β : ℕ → ℝ) : Papal.Weaver := weaving P A (staffAt (u s)) 10 s β

def unselectedCost (s : ℕ) (β : ℕ → ℝ) : ℂ := infiniteE P s (billAt P A u s β * billAt P A v s β) -
      infiniteE P s (billAt P A u s β) * infiniteE P s (billAt P A v s β)

open Heat
universe j
lemma early_stamp_election (X : TintDemand) (Mc : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ) (u v : ℕ → Cover) (β : ℕ → ℝ) (f c : ℕ → ℕ)
      (x : P.Spectrum0 3),
      PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      QualifiedWakeReadout.{j} P K ∧ PhysicalWakeGram P ∧
      PencilLease P A 0 touchPoint u v ∧ Pooling P.run (takenVolume P) (takenCutoff P) f β ∧
      (∀ s, |κFix β s| ≤ 2 * bornQ P.par s) ∧
      StrictMono c ∧ JointTuple.{j} P K x ∧ HoldRead P A c x 0 touchPoint u v ∧
      PaidPair P (A+1) (staffAt ∘ u) (staffAt ∘ v) (fun _ => 10) ∧
      (∀ (w : ℕ → Cover) (s : ℕ),
        InTest P.calibration true (skyDeck (nodeC (w s)) (10+8)) false
          (household P.calibration (billAt P A w s β)) ∧
        CovCover P.calibration (household P.calibration (billAt P A w s β))) ∧
      0 < ‖payoff‖ ∧ Tendsto (fun s => infiniteE P s (billAt P A u s β)) atTop (𝓝 0) ∧
      Tendsto (fun s => infiniteE P s (billAt P A v s β)) atTop (𝓝 0) ∧
      Tendsto (fun s => unselectedCost P A u v s β) atTop (𝓝 payoff) ∧
      ∀ᶠ s : ℕ in atTop,
        printedHere P.par P.width s (skyDeck (nodeC (u s)) (10+8)) (rescaledFit P s A 0 (1/4)) ∧
        printedHere P.par P.width s (skyDeck (nodeC (v s)) (10+8)) (rescaledFit P s A touchPoint (1/4)) ∧
        ‖payoff‖ / 2 < ‖unselectedCost P A u v s β‖ ∧
        ∀ᶠ n in atTop, Ferry P.run s (takenVolume P (f n)) (takenCutoff P (f n)) ∧
          ShelterRent P.run s (takenVolume P (f n)) (takenCutoff P (f n)) ∧
          TiltInvoice P.run s (takenVolume P (f n)) (takenCutoff P (f n)) E := by
  obtain ⟨P,K,E,elig,pose,Q,W⟩ := wakeElectionWithPhysicalGram.{j} X Mc
  let u := advice P A 1 0 0
  let v := advice P A 1 0 touchPoint
  have ht : PencilLease P A 0 touchPoint u v := ⟨(announces P 1 zero_lt_one hA 0 0).1,
    (announces P 1 zero_lt_one hA 0 touchPoint).1, fun h => (point_ne h.symm).elim⟩
  -- periods and cutoffs thin by f; allowed also to thin the rungs by f
  obtain ⟨f,β,bf,w⟩ := Pooling.fettle P.run P.history (strictMono_id (α:=ℕ))
  obtain ⟨d, hd, p⟩ := Q A hA 0 touchPoint u v Empty f bf ht (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  obtain ⟨x,_,e,k,_⟩ := p (fun _ => True) (Eventually.of_forall fun _ => trivial)
  refine ⟨P,K,E,u,v,β,f,f∘d,x,elig,pose,Q,W,ht,w, paidFix _ w P.large,bf.comp hd,e,k,
    fitting_pair P hA ht.p0 ht.p1 F₀ F₀ g₀ g₀ (show A<A+1 by linarith) (by norm_num),?_,payoff_positive,?_⟩
  · intro u s
    let l:=adj_pays (u s) F₀ g₀ (e:=0) (show 4 ≤ 10 by norm_num)
    exact ⟨weaving_ok P _ A _ 0 _ β l, covariant_scale _
      ((staffAt (u s)).registration (κFix β s) _ P.calibration (r:=10) l) (ampl P s A)⟩
  obtain ⟨F,G,L⟩ := visit_book P hA ht.p0 ht.p1 W w F₀ F₀ g₀ g₀ (show 4≤10 by norm_num) point_ne.symm
  rw [zero_sub] at L; refine ⟨F,G,L,?_⟩; obtain ⟨t,Y⟩:=elig.investment
  have hy:=tilt_paid P.run elig.dispatch Y
  filter_upwards [fitsPrinted P hA (by norm_num : (0:ℝ)<1/4) ht.p0 P.width (10+8),
    fitsPrinted P hA (by norm_num : (0:ℝ)<1/4) ht.p1 P.width (10+8),
    rents P.run elig.rocky.merit,hy,L.norm.eventually (lt_mem_nhds (half_lt_self payoff_positive))] with s F G q t a
  refine ⟨F,G,a,?_⟩
  filter_upwards [(bf.tendsto_atTop.eventually (P.history.finance s)),
    ((P.law.pick.grow_i.comp P.history.growsA).comp bf).tendsto_atTop.eventually t] with n p v
  exact ⟨p,q _ _ p.depth p.enters, v _ p.enters⟩

#print axioms visits_clear
#print axioms early_stamp_election
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
