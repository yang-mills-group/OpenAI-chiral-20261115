import VerifiedSatinGroundInteraction

/-!
# A fixed physical insertion -- in the Satin resolution system

Use **fermion** spacing at level zero as physical length one, as in Tower's
`timeMesh`. We reuse `Tapestry`'s Cover geometry (divide its real-space
coordinates by two). No assumptions on a Tapestry extraction or any history
outside of this `Universal` with `GroundExtension`. 

There are different separation tests. The one here is for **one**
gauge-singlet mixed observable, in `Pannier.Chancel.Filigree`. So for example
its opposite matter letters are at separated locations. It is not two
spatially separated neutral observables, and it would not be appropriate to
require the dressing gauge coefficients here to be away from the matter
they dress. And we don't assert separation of the ell-*buffers* around the
two kinds of matter legs. This is not a point-field object. We prove one
fixed set of physical locations / positive lower bound on separation native
to the observable kept in the elected hierarchy (not just one `¼` obtained
after chasing a diagonal of observing rungs), no periodic short-circuiting
of the displacements on the final path, support in a fixed buffered physical
region even through refinements, and bounds & identities on the original
vacuum's joint-Aurora readings. Later files address vacuum selection.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification CF.Pannier.Chancel

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "ir" => i ∘ G.rows
local notation "uv" => k ∘ G.columns

/-- All support sites plus buffers still inside the physical set `A`. -/
def SupportedPhysically (Λ : Preparation) (l s : ℕ) (S : Finset Cover)
    (A : Set (Axis → ℝ)) : Prop :=
  Tapestry.printedHere Λ l s S ((fun x : Axis → ℝ => fun j => x j / 2) ⁻¹' A)

def location (Λ : Preparation) (s : ℕ) (x : Cover) : Axis → ℝ := fun j =>
  Tapestry.markZ Λ s (x j) / 2

lemma SupportedPhysically.contains {S A s} (p : SupportedPhysically Λ l s S A)
    {x : Cover} (hx : x ∈ S) : location Λ s x ∈ A := p x hx (Tapestry.treads _ _ _ _)

lemma SupportedPhysically.step {S A s} (p : SupportedPhysically Λ l s S A) :
    SupportedPhysically Λ l (s+1) (wingspan Λ l S) A :=
  Tapestry.shielding Λ l s _ S p
lemma SupportedPhysically.persists {S A s} (p : SupportedPhysically Λ l s S A) (r : ℕ) :
    SupportedPhysically Λ l (s+r) (volumeAround Λ l r S) A := by
  induction r with
  | zero => exact p
  | succ r hr => exact hr.step

lemma canBound (Λ : Preparation) (l s : ℕ) (S : Finset Cover) :
    ∃ a : ℝ, 0 < a ∧ SupportedPhysically Λ l s S (Tapestry.cabin a) := by
  obtain ⟨n,h,p⟩ := ((eventually_gt_atTop (0 : ℕ)).and (Tapestry.fundCabin Λ l s S)).exists
  have hu : (0:ℝ) < n := by positivity
  refine ⟨n,hu,?_⟩
  intro x hx y hy j
  change |y j / 2| ≤ (n:ℝ)
  have he : |y j| ≤ (n:ℝ) := p x hx hy j
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

lemma matterSpacing {s : ℕ} {x y : Cover} (h : x ≠ y) :
    ∃ j : Axis, 1/Tapestry.precisionAt Λ s ≤
      |location Λ s (nodeC y) j-location Λ s (nodeC x) j| := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp h
  let a : ℝ := Tapestry.precisionAt Λ s
  have ha : 0 < a := Tapestry.positiveScale ..
  have he : location Λ s (nodeC y) j-location Λ s (nodeC x) j =
      ((y j : ℝ) - (x j : ℝ))/a := by
    unfold location a
    rw [Tapestry.nodePrint,Tapestry.nodePrint]
    ring
  refine ⟨j,?_⟩
  change 1/a ≤ _
  rw [he,abs_div,abs_of_pos ha,div_le_div_iff_of_pos_right ha]
  rcases lt_or_gt_of_ne hj with p | p
  · have he : (x j : ℝ)+1 ≤ (y j : ℝ) := by
      exact_mod_cast (show x j + 1 ≤ y j by omega)
    exact le_trans (by linarith : 1 ≤ (y j : ℝ) - (x j : ℝ)) (le_abs_self _)
  · have he : (y j : ℝ)+1 ≤ (x j : ℝ) := by
      exact_mod_cast (show y j + 1 ≤ x j by omega)
    exact le_trans (by linarith : 1 ≤ -((y j : ℝ) - (x j : ℝ))) (neg_le_abs _)

/-- Unwrapped displacements, including magnitude. Cover here at gauge lattice
scale of the indicated period (use `node_of` for the matter letters). -/
def FullDistances (S : Finset Cover) (m : Side) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Lattice.lift (wrap (More m) y - wrap (More m) x) = y-x

include V G in
lemma final_distances (S : Finset Cover) (s : ℕ) :
    ∀ᶠ t in atTop, FullDistances S (side Y ((ir) t) s) := by
  have ht : Tendsto (fun t : ℕ => (Journey.side Y ((ir) t) s).val) atTop atTop :=
    (goes Y H s).comp ((V.pick.grow_i.comp G.history.growsA).tendsto_atTop)
  have hh : Tendsto (fun t : ℕ => More (Journey.side Y ((ir) t) s)) atTop atTop := by
    refine tendsto_atTop.mpr (fun m => (ht.eventually_ge_atTop m.val).mono ?_)
    intro t v
    change m.val ≤ (Journey.side Y ((ir) t) s).val at v
    change m.val ≤ (Journey.side Y ((ir) t) s).val * 2
    omega
  refine S.eventually_all.mpr (fun x _ => S.eventually_all.mpr (fun y _ => ?_))
  filter_upwards [hh.eventually (CF.Crest.Shore.raising (y-x))] with t h
  rwa [map_sub] at h

include G in
lemma final_limit (s : ℕ) (f : Family K) (p : TestFamily K true f) :
    Tendsto (fun t : ℕ => sharp Y H s ((ir) t) ((uv) t) f) atTop (𝓝 (E s f)) := by
  obtain ⟨S,g⟩ := p.paid
  obtain ⟨C,h⟩ := Journey.valuation Y H g
  have hv : pay f C := h
  have hC : 0 ≤ C := pay_nonneg hv
  obtain ⟨_, _, path⟩ := G.history.implements s S
  refine Metric.tendsto_nhds.mpr (fun ε hp => ?_)
  let e := ε/(C+1)
  have he : 0 < e := by unfold e; positivity
  filter_upwards [path e he] with t v
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((v f g C hv).2.2.2.2.1)
  exact (mul_lt_mul_of_pos_left (lt_add_one C) he).trans_eq (div_mul_cancel₀ _ (by positivity))

structure Fixture (z : SU.Slot) (q d w : ℕ) (o : Cover) (s : ℕ)
    (f : observable (tent Y H) true) (A : ℝ) : Prop where
  dressed : f.val ∈ Filigree K (Window.family z) (booty o d q) (Sen o (payout d q w))
  neutral : Tapestry.Neutral (tent Y H) f.val
  local_base : f.val ∈ observ (tent Y H) (Sen o (payout d q w)) false
  Apos : 0 < A
  refine_bound (r : ℕ) :
    let S := volumeAround Λ l r (Sen o (payout d q w))
    SupportedPhysically Λ l (s+r) S (Tapestry.cabin A) ∧
      (upward Y H G.history true f s r).val ∈ observ (tent Y H) S true ∧
      (∀ᶠ t in atTop, Ferry Y (s+r) ((ir) t) ((uv) t) ∧ FullDistances S (side Y ((ir) t) (s+r))) ∧
      Tendsto (fun t : ℕ => sharp Y H (s+r) ((ir) t) ((uv) t)
        (upward Y H G.history true f s r).val) atTop (𝓝 (E s f.val))
  anchors : Injective (booty o d q) ∧ ∀ j, nodeC (booty o d q j) ∈ Sen o (payout d q w)
  separation_pos : 0 < 1 / Tapestry.precisionAt Λ s
  /-- This applies to every candidate crease `j,y` in every term (the premise is the
  separation clause in the `CRow` grammar). With `dressed` it records what kind of
  separation the witness has. -/
  spacing : ∀ (j : Fin (q^4)) (y : Cover), (∀ t, y ≠ booty o d q t) →
    ∃ u : Axis, 1/Tapestry.precisionAt Λ s ≤
      |location Λ s (nodeC y) u-location Λ s (nodeC (booty o d q j)) u|
  actual : 1/4 ≤ ‖E s f.val‖
  ground (j : Axis) (C : Arena Y H G.history.circuit j 0 true) (r : ℕ) :
    let x := upward Y H G.history true f s r
    let B := cap Y H V (s+r) G.history G.clipped j true C x
    let Ω := seat0 Y H V G.history j true C
    B = cap Y H V s G.history G.clipped j true C f ∧
      inner ℂ Ω (B Ω) = E s f.val

/-- Freeze a single probe *in* the `GroundExtension`, keeping the Coherent
history and support budget. This is before translation-extremal selection. -/
theorem freeze_probe (z : SU.Slot) {q d w : ℕ} (o : Cover) {C Z : ℝ}
    (p : Papal.Cornet Y H q d w C Z) :
    ∀ᶠ s in atTop, ∃ (f : observable K true) (A : ℝ),
      Fixture Y H V G z q d w o s f A := by
  let S := Sen o (payout d q w)
  filter_upwards [Papal.certificate Y H C Z z p I E V] with s hp
  obtain ⟨_, _, f, _, v, neutral, _, _, pos⟩ := hp o
  have hf := FilTest v
  let F : observable K true := ⟨f,aux_test hf.widen,fun _ => neutral⟩
  obtain ⟨A,hA,a⟩ := canBound Λ l s S
  refine ⟨F,A,⟨v,neutral, (obs_in ..).2 ⟨hf,neutral⟩,hA, ?_,
    ⟨p.cents _, Papal.stake_centers Y H o d q w⟩,
    div_pos zero_lt_one (Tapestry.positiveScale Λ s),
    fun j y g => matterSpacing (g j|>.symm), pos, ?_ ⟩⟩
  · intro r L
    have h := proceeds Y H G.history.circuit s r hf.widen
    refine ⟨a.persists r, chroma Y H G.history.circuit s r ((obs_in ..).2 ⟨hf.widen,neutral⟩),
      (G.history.finance _).and (final_distances Y H V G L _),?_⟩
    rw [← h.2]
    exact final_limit Y H G _ _ (aux_test h.1)
  · intro j B r x T Ω
    have hb := Vacancy.cap_level (F := F) Y H V s G.history G.clipped j true B (s+r) (by omega)
    rw [Nat.add_sub_cancel_left] at hb
    exact ⟨hb,(congrArg (fun t : (Aurora Y H V G.history j true B) →L[ℂ] (Aurora Y H V G.history j true B) => inner ℂ Ω (t Ω)) hb).trans
      (Vacancy.inspected Y H V s G.history G.clipped j true B)⟩

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.freeze_probe
