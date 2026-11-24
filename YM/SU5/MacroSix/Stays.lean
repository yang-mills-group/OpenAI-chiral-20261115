import YM.SU5.MacroSix.TestTopology
import YM.SU5.MacroSix.Reflected
import YM.SU5.MacroSix.Cross
/-! # One election and extra viability / perturbation conclusions used with both prices

Here bind the one election `Chosen`; also expose that it's available within the main
supplied physical existence theorem (`Prototype.summit`). All following properties apply
ad lib to the *same* x on the supplied P. There is no subsequence election from optimized
measurements or eigenspace outside this holder. Part (i) really applies at preset fixed
physically distant positive-time supports (`positive_ready`). Stability is given for
independent L¹ perturbations keeping strict order, so for instance slightly perturbed smooth
density centers/tests *within that qualification* can still really be asked.

This file doesn't define the gauge--matter split comparison. No clustering or frame beyond
the order qualifications is part of the perturbation lemma.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria Set
open _root_.YM.MacroSix _root_.YM.MacroSix.ClockTest
open Ballad Twah

namespace Spine
variable (P : Spine) (x : P.Spectrum0 3) (s n : ℕ)
    (Z W : Window.Family) (f g : Vantage → ℝ)
    (K : P.Register) (c r : ℕ → ℕ) (J : P.Ellis 3 x)
structure Chosen : Prop where
  launch : Prototype.Launch P c r
  party : P.party 3 K x
  ready : Prototype.readyUV P c r x keyV
  summit : Summit x
  deck : P.LowerDeck x K J

lemma chosenPossible (L M D : ℝ) (Y : Supplier) (q : 0 < M) (p : 0 < D) (z : ℕ → ℕ) :
    ∃ (P : Spine) (K : P.Register), uniform P K Y L M ∧
      ∃ (r : ℕ → ℕ), z ≤ r ∧ ∃ c x J, P.Chosen x K c r J := by
  obtain ⟨P,K,f,r,h,c,B,-,-,-,α,t,p,d,Y₁,R,W⟩ := Prototype.summit L M D Y q p z
  obtain ⟨i,x,y,-,-,v,e,J,h',U,-⟩ := W.exists
  exact ⟨P,K,f,r,h,c,x,J,B,y,v,U,h'⟩

open Spectral Caino Spectral.Orbit.Prairie
lemma always_windows (b : Fin 3 → Bool) :
    ∃ x : E4, ∃ d : ℝ, 0 < d ∧ SpectralWindow (ball x d) ∧ closedBall x d ⊆ Mink.inside ∧
      closedBall x d ⊆ YM.spatial ⁻¹' alley b := by
  let R := YM.spatial ⁻¹' alley b
  have he := Mink.open_inside.inter ((alley_open b).preimage Mink.rest_cont)
  let v : Terrain (Fin 3) := WithLp.toLp 2 (fun i : Fin 3 ↦ if b i then (1:ℝ) else (-1:ℝ))
  let x := YM.position v (‖v‖+1)
  have h : x ∈ Mink.inside ∩ R := by
    refine ⟨(show ‖YM.spatial x‖ < YM.time x from (by simp [x])), ?_⟩
    change YM.spatial (YM.position v _) ∈ alley b
    rw [spatial_position]
    intro i; cases hi:b i <;> simp [hi,v]
  obtain ⟨d,u,p⟩ := Metric.mem_nhds_iff.mp (he.mem_nhds h)
  have hp : closedBall x (d/2) ⊆ (Mink.inside ∩ R) := (closedBall_subset_ball
    (half_lt_self u)).trans p
  exact ⟨x,d/2,half_pos u,⟨⟨x,mem_ball_self (half_pos u)⟩,isOpen_ball,
    ball_subset_closedBall.trans (hp.trans Set.inter_subset_left),b,
    ball_subset_closedBall.trans (hp.trans Set.inter_subset_right)⟩,
    hp.trans Set.inter_subset_left,hp.trans Set.inter_subset_right⟩

lemma prepare_time (U : Set ℝ) (p : U.Nonempty) (v : IsOpen U) : ∃ g : ℝ → ℝ, TimeDensity g ∧ tsupport g ⊆ U := by
  obtain ⟨x,h⟩ := p
  obtain ⟨ε,e,w⟩ := Metric.isOpen_iff.mp v _ h
  let K : ContDiffBump x := ⟨ε/4,ε/2,by positivity, by linarith⟩
  refine ⟨K.normed volume,⟨K.contDiff_normed,K.hasCompactSupport_normed,fun y ↦ K.nonneg_normed y,
    K.integral_normed⟩,?_⟩
  rw [K.tsupport_normed_eq]; exact (closedBall_subset_ball (half_lt_self (show 0<ε from e))).trans w

lemma positive_ready {P : Spine} {c r : ℕ → ℕ} (A : Prototype.Launch P c r)
    {g : ℝ → ℝ} (p : TimeDensity g) (v : tsupport g ⊆ Set.Ioi 0) :
    ∀ᶠ i in atTop, P.TimeFare (c i) (r i) g := by
  have ht : ∃ x, g x ≠ 0 := by
    by_contra! h; have he := p.mass; simp [h] at he
  obtain ⟨x,hx⟩ := ht
  obtain ⟨u,hu,h⟩ := IsCompact.exists_isMinOn p.compact
    ⟨x,subset_tsupport g hx⟩ (continuousOn_id (s:=tsupport g))
  filter_upwards [(sixWidth_vanishes A (3:Axis)).eventually (gt_mem_nhds
    (show 0 < u from v hu))] with i he x k
  exact he.trans_le (h k)

lemma ReflectedGrant.positive {P : Spine} {x s n f D} (p : P.ReflectedGrant s n f x D) :
    (P.measureField s n (f ∘ mirrorΩ 3) f x).PosDef := by
  let d := p.price.choose; have hp := p.price.choose_spec
  exact p.answer ▸ gram_positive (P.ManyF 3 (P.otherSpectrum 3 3 x))
    (fun j ↦ P.darkSmear s n j f 0 x true) d hp.1 (le_trans hp.2.2 p.answer.le)
lemma ReflectedGrant.survives {P : Spine} {x s n f D} (p : P.ReflectedGrant s n f x D) :
    Success (P.measureField s n (f ∘ mirrorΩ 3) f x) :=
  let Q := P.measureField s n (f ∘ mirrorΩ 3) f x
  ⟨p.positive.det_pos.ne',fun _ ↦ p.positive.diag_pos.ne'⟩


local notation "β" => P.otherSpectrum 3 3 x
local notation "ν" => P.seasons 3 β
local notation "M" => P.fieldKernel s n x
local notation "η" i:max => P.darkField s n i x
include J
lemma payFrame_unif {c : ℝ} (p : P.OnFrame s n f g c) :
    fieldBound (fun x y ↦ M x y Z W) (‖(η Z)‖*‖(η W)‖) f g := by
  intro x' hx y hy; let a := p.factors (subset_tsupport _ hx) (subset_tsupport _ hy)
  let K := P.cartage 3 β; let h := Real.toNNReal (y 3-x' 3); let u := K x' (η Z); let v := K y (η W)
  have hu : ‖u‖=‖(η Z)‖:= P.cart_norm 3 β _ _
  have hv : ‖v‖=‖(η W)‖:= P.cart_norm 3 β _ _
  calc
    _ = ‖inner ℂ u ((ν).E h v)‖ := congrArg norm (P.fieldKernel_eq s n Z W x J x' y a.1)
    _ ≤ ‖u‖ * ‖(η W)‖ := (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((OS.Semigroup.Balloon.heatedLim ν h v).trans_eq hv) (norm_nonneg _))
    _ = _ := congrArg (fun x ↦ x*_) hu

/-- Change tests independently in *any* way through a filter, asking normalized smooth
real densities in a time-separation qualification. `x` and `s n` fixed; support is not
required to remain in the union of some fixed compact sets to grant this modulus. -/
lemma variation_limit {T : Type*} (L : Filter T) (a b : T → Vantage → ℝ)
    (p : SmoothDensity f) (q : SmoothDensity g) (funds : ∃ y : ℝ, P.OnFrame s n f g y)
    (w : ∀ᶠ i in L, SmoothDensity (a i) ∧ SmoothDensity (b i) ∧ ∃ y : ℝ, P.OnFrame s n (a i) (b i) y)
    (ha : Tendsto (fun i ↦ discrepancy (a i) f) L (𝓝 0))
    (hb : Tendsto (fun i ↦ discrepancy (b i) g) L (𝓝 0)) :
    Tendsto (fun i ↦ P.measureField s n (a i) (b i) x Z W) L (𝓝 (P.measureField s n f g x Z W)) := by
  obtain ⟨u,h⟩ := funds
  let K := fun x y : Vantage ↦ M x y Z W
  have hf (f g : Vantage → ℝ) (c : ℝ) (p : SmoothDensity f) (q : SmoothDensity g)
      (h : P.OnFrame s n f g c) : Integrable (weightKernel K f g) :=
    (P.measureField_integral s n Z W f g c x p.smooth.continuous p.compact q.smooth.continuous
      q.compact J h).1
  exact costs_limit K _ (mul_nonneg (norm_nonneg (η Z)) (norm_nonneg (η W))) L a b f g
    (hf f g u p q h) p q (P.payFrame_unif x s n Z W f g J h)
    (w.mono fun i ⟨p,q,u,h⟩ ↦ ⟨p,q,hf _ _ _ p q h,P.payFrame_unif x s n Z W _ _ J h⟩) ha hb

lemma accurate {T : Type*} (L : Filter T) (a b : T → Vantage → ℝ)
    (p : SmoothDensity f) (q : SmoothDensity g) (funds : ∃ y : ℝ, P.OnFrame s n f g y)
    (w : ∀ᶠ i in L, SmoothDensity (a i) ∧ SmoothDensity (b i) ∧ ∃ y : ℝ, P.OnFrame s n (a i) (b i) y)
    (ha : Tendsto (fun i ↦ discrepancy (a i) f) L (𝓝 0))
    (hb : Tendsto (fun i ↦ discrepancy (b i) g) L (𝓝 0))
    (ht : Success (P.measureField s n f g x)) :
    ∀ᶠ i in L, Success (P.measureField s n (a i) (b i) x) :=
  eventually_success L _ _ (fun i j ↦ P.variation_limit x s n i j f g J L a b p q funds w ha hb) ht

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms ReflectedGrant.survives
#print axioms accurate
#print axioms chosenPossible
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
