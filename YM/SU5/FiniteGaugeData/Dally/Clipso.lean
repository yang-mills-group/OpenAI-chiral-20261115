import YM.SU5.FiniteGaugeData.Dally.Esche
/-!
 # Ward Chamber Estimator. Only a (possibly as-small-as-wanted) *single jig per chamber* for all-arity inputs,
 at stencil-step. In chart one assembly, separated by any distance you demand in EACH axis.
 -/
noncomputable section
open Metric Filter Function WithLp
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
open _root_.YM Dally Gem Leal Leal.Breve Celeritas Land Mist OS OS.Semigroup Flute Apso
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space) (A : Tribe G)
variable {n : ℕ} (u : Fin n → ι) (w : Palette G u)
variable (b : SpaceAxis) (x : Points n) (t s : ℝ)
attribute [local instance] ostensible
local notation "ₜ" => timeAxis
def debut (n : ℕ) (M : Axis → List (Fin n)) : Set (Points n) := {x | ∀ a : Axis, chart a x (M a)}
def wide (n : ℕ) (Δ : ℝ) : Set (Points n) := {x| ∀ a : Axis, ∀ i j : Fin n, i≠j→ Δ < |x i a-x j a| }
variable (M : Axis → List (Fin n)) (Δ : ℝ) (η : ℝ)
lemma lounge (h : x ∈ debut n M) : longitude x := fun a => (capable_iff a x).2 ⟨M a,h a⟩
lemma sears (ha : longitude x) : ∃ M, x ∈ debut n M := by
  choose M p using fun a => (capable_iff a x).1 (ha a)
  exact ⟨M,p⟩
lemma wide_d (n : ℕ) (Δ : ℝ) : IsOpen (wide n Δ) := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => eventually_all.mpr fun a =>
    eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases H : i=j
  · exact Eventually.of_forall fun _ k => (k H).elim
  filter_upwards [(isOpen_lt continuous_const (by fun_prop : Continuous (fun x : Points n => |x i a-x j a|))).mem_nhds (hx a i j H)
    ] with y p using fun _ => p
lemma debut_d : IsOpen (debut n M) := isOpen_iff_mem_nhds.mpr fun x hx => eventually_all.mpr fun a => earth a x _ (hx a)
lemma straight : Convex ℝ (debut n M) := by
  intro x hx y hy r s hr hs t a
  have he := (hx a).2; have hf := (hy a).2
  refine ⟨(hx a).1,List.pairwise_iff_get.mpr fun i j k => ?_⟩
  let p := (M a).get i; let q := (M a).get j
  have V : x p a<x q a := (List.pairwise_iff_get.mp he) _ _ k
  have U : y p a<y q a := (List.pairwise_iff_get.mp hf) _ _ k
  change r*x p a+s*y p a<r*x q a+s*y q a; by_cases h : r=0
  · have B : s=1 := by linarith
    simpa only [h,B,zero_mul,one_mul,zero_add] using U
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left V (hr.lt_of_ne (Ne.symm h))) (mul_le_mul_of_nonneg_left U.le hs)
lemma long_stretch (h : x ∈ debut n M) : ∀ᶠ t : ℝ in atTop, t • x ∈ debut n M ∩ wide n Δ := by
  have D : ∀ᶠ t : ℝ in atTop, (t • x : Points n)∈ wide n Δ := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases v : i = j
    · exact Eventually.of_forall fun _ k=> (k v).elim
    let c := |x i a-x j a|
    have p : 0 < c := abs_pos.mpr (sub_ne_zero.mpr ((lounge x M h a).ne v))
    filter_upwards [eventually_gt_atTop 0,eventually_gt_atTop (Δ/c)] with t ht u
    intro _
    change Δ < |t*x i a - t*x j a|
    rw [← mul_sub,abs_mul,abs_of_pos ht]; exact (div_lt_iff₀ p).mp u
  filter_upwards [D,eventually_gt_atTop 0] with t ht δ
  refine ⟨fun a => ⟨(h a).1,?_⟩,ht⟩
  exact (h a).2.imp fun {i j} v => (show t*(x i a)<t*x j a from mul_lt_mul_of_pos_left v δ)
-- boxes
structure Spot (n : ℕ) (M : Axis→List (Fin n)) (Δ η : ℝ) where
 center : Points n
 radius : ℝ
 pay : 0 < radius
 quota : radius ≤ η
 savings : closedBall center radius ⊆ debut n M ∩ wide n Δ
lemma stow (h : (debut n M).Nonempty) (e : 0 < η) : Nonempty (Spot n M Δ η) := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨t,ht⟩ := (long_stretch x M Δ hx).exists
  obtain ⟨r,hr,H⟩ := nhds_basis_closedBall.mem_iff.mp (((debut_d M).inter (wide_d n Δ)).mem_nhds ht)
  exact ⟨⟨_,min η r, lt_min e hr,min_le_left _ _,(closedBall_subset_closedBall (min_le_right _ _)).trans H⟩⟩
#print axioms stow

variable (τ : ℕ → ℝ) (S : ∀ n, Set (Points n))
private lemma dockRun (hy : Tendsto τ atTop (𝓝 0)) (x c : Points n) {r} (hx : x ∈ ball c r) :
    ∀ᶠ k in atTop, ∀ i : Fin n,∀ a : Axis, Leak x i a (τ k)∈ ball c r := by
  refine eventually_all.mpr fun i=> eventually_all.mpr fun a=> ?_
  have H : Continuous (Leak x i a) := by unfold Leak; fun_prop
  exact hy.eventually ((H.tendsto' _ _ (Leak_root ..)).eventually (isOpen_ball.mem_nhds hx))

def AtJig (q : Spot n M Δ η) : Prop :=
  ∀ x ∈ ball q.center q.radius, x ∈ S n → ∀ u : Fin n → ι, ∀ w : Palette G u,
  ∀ b : SpaceAxis, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ‖blush W G ω A u w b x (τ i)‖ ≤ τ i * ε ∧
    ∀ j : Fin n, Leak x j timeAxis (τ i) ∈ ball q.center q.radius ∧ Leak x j b.castSucc (τ i) ∈ ball q.center q.radius
structure Rookie : Prop where
 purchase (n : ℕ) (M : Axis → List (Fin n)) (h : (debut n M).Nonempty) :
    ∃ q : Spot n M Δ η, AtJig W G ω A M Δ η τ S q

def Grace : Prop := ∀ (n : ℕ) (x : Points n), longitude x → ∀ u : Fin n → ι, ∀ w : Palette G u,
    ∀ b : SpaceAxis, chip W G ω A u w b x=0
variable {U : Set (Shrine K)} (hp : ∀ (n : ℕ) b, b ≠ timeAxis → Philos (σ:=Fin n) W ω timeAxis b U)
    (hc : ∀ i, saucer (W i) (ω i)=ω i) (g : Stamp W G A U)
variable (ht : ∀ᶠ i in atTop, 0 < τ i) (hy : Tendsto τ atTop (𝓝 0)) (hS : ∀ n, Dense (S n))
include hp hc g ht hy hS
omit hS in
lemma charisma (H : Grace W G ω A) (T : Spot n M Δ η) : AtJig W G ω A M Δ η τ S T := by
  intro x hx _ u w b ε e
  have P := lounge x M (T.savings (ball_subset_closedBall hx)).1
  filter_upwards [(knack W G ω A u w b x (hp n) hc g P ht hy).2 (H n x P u w b) ε e,
    dockRun τ hy x T.center hx] with k hk t using ⟨hk,fun j => ⟨t j _,t j _⟩⟩
lemma choral (h : Rookie W G ω A Δ η τ S) : Grace W G ω A := by
  intro n x hx u w b
  obtain ⟨M,H⟩ := sears x hx; obtain ⟨q,E⟩ := h.purchase n M ⟨x,H⟩
  let f := chip W G ω A u w b
  have WF : AnalyticOnNhd ℝ f (debut n M) := fun z p => chip_analytic W G ω A u w b z (hp n) hc g (lounge z M p)
  have A0 (y) (p : y ∈ ball q.center q.radius) := (q.savings (ball_subset_closedBall p)).1
  have B0 (y) (p : y ∈ ball q.center q.radius) (v : y∈S n) : f y=0 := by
    apply (knack W G ω A u w b y (hp n) hc g (lounge y M (A0 y p)) ht hy).1
    intro ε e; exact (E y p v u w b ε e).mono fun t k => k.1
  suffices e : f =ᶠ[𝓝 q.center] (fun _=> 0) from
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq WF analyticOnNhd_const
      (straight M).isPreconnected (A0 _ (mem_ball_self q.pay)) e H
  filter_upwards [ball_mem_nhds q.center q.pay] with z hz
  by_contra v
  have V := (WF z (A0 z hz)).continuousAt.tendsto.eventually (eventually_ne_nhds v)
  have D : ∃ᶠ z in 𝓝 z, z∈ S n := mem_closure_iff_frequently.mp (hS n z)
  obtain ⟨y,e,p,w⟩ := (D.and_eventually (V.and ((isOpen_ball).mem_nhds hz))).exists
  exact p (B0 _ w e)
lemma catalysis (hr : 0 < η) : Rookie W G ω A Δ η τ S ↔ Grace W G ω A :=
  ⟨choral W G ω A Δ η τ S hp hc g ht hy hS,fun e => ⟨fun _ M h => (stow M Δ η h hr).elim
    fun q => ⟨q,charisma W G ω A M Δ η τ S hp hc g ht hy e q⟩⟩⟩
#print axioms catalysis
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
