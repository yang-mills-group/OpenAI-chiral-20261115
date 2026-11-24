import YM.SU5.FiniteGaugeData.Dally.Thal
import YM.SU5.FiniteGaugeData.Poin.Rosette
/-!
 # Opening the PRICE on actual Seers — formal paper ink without Shelf.
 -/
noncomputable section
open Metric Filter Function WithLp
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Fuchsia
open Gem Leal Leal.Breve Celeritas Celeritas.Land Mist
open _root_.YM Dally
open OS OS.Semigroup
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i) (Ω : ∀ i, (K i).space)
local notation "Ξ" => (σ × Axis) → ℝ
local notation "Θ" => σ → E4
variable (ν : σ → ℕ) (F : σ → Shrine K) (L : List σ) (a : Axis)
def linen : (Ξ) ≃L[ℝ] (Θ) := LinearEquiv.toContinuousLinearEquiv {
  toFun (x : Ξ) (i : σ) := toLp 2 fun a => x (i,a)
  invFun x i := x i.1 i.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl }
variable (x : σ → E4) (k : σ)
def elevator (p : Ξ) (r : ℝ) := x + linen (update p (k,a) r)
@[simp] lemma elevator_zero : elevator a x k 0 0 = x := by
  unfold elevator; rw [show update (0:Ξ) (k,a) (0:ℝ) = (0:Ξ) from update_eq_self ..]; simp
lemma ev_sot : Continuous (fun t : Ξ × ℂ => elevator a x k t.1 t.2.re) := by
  unfold elevator
  fun_prop
private lemma euC : Continuous (fun p : Ξ => elevator a x k p 0) := by
  unfold elevator
  fun_prop
def bead (k i : σ) : ℝ := if i=k then 1 else 0
lemma euL (p : Ξ) (r : ℝ) (i : σ) : elevator a x k p r i =
    (bead k i*r) • basis a + elevator a x k p 0 i := by
  apply PiLp.ext
  intro j
  by_cases h : i = k
  · by_cases hj : j = a
    · subst j; subst i; simp [elevator, linen, bead, add_comm]
    · simp [elevator, linen, bead, basis_eq, hj,h]
  · simp [elevator, linen, bead, h]
private lemma europt (p : Ξ) (r : ℝ) : actO W F (elevator a x k p r) a =
    actO W F (elevator a x k p 0) a := by
  funext i
  unfold actO Plot opt
  rw [euL]
  simp only [neg_add_rev, leg_add, ← neg_smul, leg_veil, one_mul, mul_one]
private lemma paint_bound (x : Θ) (i : σ) : ‖actO W F x a i‖ ≤ ‖(F i).f a‖ := by
  unfold actO Plot opt
  exact (norm_mul_le _ _).trans (by
    calc
      _ ≤ (1*‖(F i).f a‖)*1 := mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (leg_norm ..) (norm_nonneg _))) (leg_norm ..) (norm_nonneg _) (by positivity)
      _ = _ := by ring)
-- Momentum of the probe along axis in this paper extension.
def ribbon (i j : σ) (p : Ξ) (z : ℂ) : ℂ :=
  let y := elevator a x k p 0
  ((startX F y a j-endX F y a i:ℝ):ℂ) + ((bead k j-bead k i:ℝ):ℂ)*z
lemma ribbon_re (i j : σ) (p : Ξ) (z : ℂ) :
    (ribbon F a x k i j p z).re = startX F (elevator a x k p z.re) a j - endX F (elevator a x k p z.re) a i := by
  unfold ribbon startX endX
  conv_rhs => rw [euL, euL (i:=i) (r:=z.re)]
  simp; ring
lemma ribbon_real (i j : σ) (p : Ξ) (z : ℂ) (h : z.im=0) :
    ribbon F a x k i j p z = ((startX F (elevator a x k p z.re) a j-endX F (elevator a x k p z.re) a i:ℝ):ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using ribbon_re ..
  · simp [ribbon, h]

def Lease {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (f g : (Ξ) → ℂ → A) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : Ξ × ℂ in 𝓝 0,
    AnalyticAt ℂ (f t.1) t.2 ∧ ‖f t.1 t.2‖ ≤ C ∧ (t.2.im = 0 → f t.1 t.2 = g t.1 t.2)
private lemma flat (c : (K a).Op) : Lease (σ:=σ) (fun _ _ => c) (fun _ _ => c) :=
  ⟨_, norm_nonneg c, Eventually.of_forall fun _ => ⟨analyticAt_const, le_rfl, fun _ => rfl⟩⟩
lemma Lease.billed {f g u v : (Ξ) → ℂ → (K a).Op} (h : Lease f u) (i : Lease g v) :
    Lease (fun p z => f p z * g p z) (fun p z => u p z * v p z) := by
  obtain ⟨c,hc,H⟩ := h; obtain ⟨d,hd,G⟩ := i
  refine ⟨c*d, mul_nonneg hc hd, ?_⟩
  filter_upwards [H,G] with t A B
  exact ⟨A.1.mul B.1,(norm_mul_le _ _).trans (mul_le_mul A.2.1 B.2.1 (norm_nonneg _) hc),
    fun y => by rw [A.2.2 y,B.2.2 y]⟩
private lemma folk (i : σ) : Lease (fun p _ => actO W F (elevator a x k p 0) a i)
    (fun p z => actO W F (elevator a x k p z.re) a i) :=
  ⟨_, norm_nonneg ((F i).f a), Eventually.of_forall fun _ => ⟨analyticAt_const,
      paint_bound .., fun _ => (congrFun (europt W F a x k ..) i).symm⟩⟩
private lemma Lue (i j : σ) (h : Seers F x a i j) :
    Lease (fun p z => parabola (W a) (ν i+ν j) (ribbon F a x k i j p z))
      (fun p z => coast W a ν F (elevator a x k p z.re) i j) := by
  let q : Ξ × ℂ → ℂ := fun t => ribbon F a x k i j t.1 t.2
  have R : Continuous q := by
    unfold q ribbon startX endX
    have T := euC a x k
    fun_prop
  have RZ : q 0 ∈ inside := by
    change 0 < (q 0).re
    unfold q; rw [ribbon_re]; change 0 < startX _ (elevator a x k 0 0) a j - endX _ (elevator a x k 0 0) a i
    rw [elevator_zero]; exact sub_pos.mpr h
  let A : ℂ → (K a).Op := parabola (W a) (ν i+ν j)
  have U : ContinuousAt (fun t => ‖A (q t)‖) 0 :=
    ((Bokeh _ _ _ RZ).continuousAt.comp R.continuousAt).norm
  refine ⟨‖A (q 0)‖+1, by positivity, ?_⟩
  filter_upwards [R.continuousAt (open_inside.mem_nhds RZ),
    U.eventually (gt_mem_nhds (by linarith : ‖A (q 0)‖ < ‖A (q 0)‖+1))] with t ht V
  have hp : AnalyticAt ℂ (ribbon F a x k i j t.1) t.2 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  refine ⟨(?_:AnalyticAt ℂ (parabola (W a) (ν i+ν j)) (ribbon F a x k i j t.1 t.2)).comp hp, le_of_lt V, ?_⟩
  · exact Bokeh (W a) _ (q t) ht
  intro h
  have D : 0 < startX F (elevator a x k t.1 t.2.re) a j - endX F (elevator a x k t.1 t.2.re) a i := by
    rw [← ribbon_re]; exact ht
  unfold coast OS.Semigroup.duration Hi
  rw [ribbon_real .., Real.coe_toNNReal _ D.le]
  exact h
def lotion (p : Ξ) (z : ℂ) (i j : σ) : (K a).Op := parabola (W a) (ν i + ν j) (ribbon F a x k i j p z)
lemma propulsion (h : L.Pairwise (Seers F x a)) :
    Lease (fun p z => Film (actO W F (elevator a x k p 0) a) (lotion W ν F a x k p z) L)
      (fun p z => let y := elevator a x k p z.re; Film (actO W F y a) (coast W a ν F y) L) := by
  induction L with
  | nil => exact flat a 1
  | cons i L ih =>
    obtain ⟨P,Q⟩ := List.pairwise_cons.mp h
    refine Lease.billed a (folk W F a x k i) (Lease.billed a
      (f := fun p z => clip (lotion W ν F a x k p z) i L)
      (u := fun p z => clip (coast W a ν F (elevator a x k p z.re)) i L) ?_ (ih Q))
    cases L with
    | nil => exact flat a 1
    | cons j L => exact Lue W ν F a x k i j (P j List.mem_cons_self)

def zodiac (p : Ξ) (z : ℂ) : ℂ := inner ℂ (Ω a) ((Film (actO W F (elevator a x k p 0) a) (lotion W ν F a x k p z) L) (Ω a))
lemma inked (h : L.Pairwise (Seers F x a)) :
    Lease (zodiac W Ω ν F L a x k) (fun p z => chalk W Ω a ν F (elevator a x k p z.re) L) := by
  let T := Film (α := σ) (R := (K a).Op)
  let g := (innerSL ℂ (Ω a)).comp (ContinuousLinearMap.apply ℂ (K a).space (Ω a))
  obtain ⟨C,hC,P⟩ := propulsion W ν F L a x k h
  refine ⟨‖g‖*C, by positivity, ?_⟩
  filter_upwards [P] with t ht
  exact ⟨(g.analyticAt _).comp ht.1, (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht.2.1 (norm_nonneg _)),
    fun i => by unfold zodiac chalk; rw [← comparator, ht.2.2 i]⟩
#print axioms inked
section
variable (b : Axis) (M : Axis → List σ) (y : (σ → E4) → ℂ)
/- ALL selected layout entries strictly apart by coordinate widths. no spectrum pressure.
    No mutual ordering requirement *between* those layouts, except hooks elsewhere. -/
lemma rents (H : ∀ a, (M a).Pairwise (Seers F x a))
    (B : ∀ a, y =ᶠ[𝓝 x] (fun p => chalk W Ω a ν F p (M a))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ R : ℝ, 0 < R ∧ Thal.Yare R K (fun p : Ξ => y (x + linen p)) := by
  let Cc (i : σ × Axis) := zodiac W Ω ν F (M i.2) i.2 x i.1
  have h (i : σ × Axis) : Lease (Cc i) (fun p z => y (elevator i.2 x i.1 p z.re)) := by
    obtain ⟨C,hc,q⟩ := inked W Ω ν F (M i.2) i.2 x i.1 (H i.2)
    refine ⟨C,hc,?_⟩
    have v : Tendsto (fun t : Ξ × ℂ => elevator i.2 x i.1 t.1 t.2.re) (𝓝 0) (𝓝 x) := by
      have h : elevator i.2 x i.1 (0:Ξ) (0:ℂ).re = x := elevator_zero i.2 x i.1
      simpa only [Prod.fst_zero, Prod.snd_zero, h] using ((ev_sot i.2 x i.1).continuousAt.tendsto (x:= (0 : Ξ × ℂ)))
    filter_upwards [q, v.eventually (B i.2)] with t ⟨f,p,k⟩ u
    exact ⟨f,p,fun r => (k r).trans u.symm⟩
  choose K' P V using h
  obtain ⟨R,hR,u⟩ := nhds_basis_closedBall.eventually_iff.mp (eventually_all.mpr V)
  refine ⟨∑ i, K' i, Finset.sum_nonneg (fun i _ => P i), R, hR, ?_⟩
  intro p hp i
  have U z (hz : z ∈ closedBall (0:ℂ) R) := @u (p,z) (show (p,z) ∈ closedBall (0 : Ξ × ℂ) R from by
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    exact ⟨hp, by simpa [mem_closedBall] using hz⟩) i
  refine ⟨Cc i p, fun z hz => (U z hz).1,fun z hz => (U z hz).2.1.trans
    (Finset.single_le_sum (fun i _ => P i) (Finset.mem_univ i)), fun r hr => ?_⟩
  exact (U (r:ℂ) (by simpa [mem_closedBall] using hr)).2.2 rfl
#print axioms rents
lemma cream (H : ∀ a, (M a).Pairwise (Seers F x a))
    (B : ∀ a, y =ᶠ[𝓝 x] (fun p => chalk W Ω a ν F p (M a))) : AnalyticAt ℝ y x := by
  obtain ⟨C,hc,R,hR,Q⟩ := rents W Ω ν F x M y H B
  let g (p : Θ) := linen.symm (p-x)
  have P : AnalyticAt ℝ g x := ((linen (σ:=σ)).symm.toContinuousLinearMap.analyticAt (x-x)).comp (f := fun p : Θ => p - x)
    (show AnalyticAt ℝ (fun p : Θ => p-x) x from analyticAt_id.sub analyticAt_const)
  let u : Ξ → ℂ := fun p => y (x + linen p)
  have A : AnalyticAt ℝ u (g x) := by
    rw [show g x = 0 by simp [g]]; exact Thal.gulf Q hR hc
  refine (show AnalyticAt ℝ (u ∘ g) x from A.comp P).congr ?_
  exact Eventually.of_forall fun z => by simp [u,g]
lemma sill (h : L.Pairwise (Seers F x b)) : ∀ᶠ z in 𝓝 x, L.Pairwise (Seers F z b) := by
  induction L with
  | nil => exact Eventually.of_forall fun _ => .nil
  | cons i L ih =>
    obtain ⟨A,B⟩ := List.pairwise_cons.mp h
    have H : ∀ᶠ z in 𝓝 x, ∀ j ∈ L.toFinset, Seers F z b i j := by
      refine (eventually_all_finset _).mpr fun j hj => ?_
      let f (z : Θ) := endX F z b i
      let g (z : Θ) := startX F z b j
      have t : f x < g x := A j (by simpa using hj)
      exact (isOpen_lt (show Continuous f by unfold f endX; fun_prop)
        (show Continuous g by unfold g startX; fun_prop)).mem_nhds t
    filter_upwards [H, ih B] with z e p; exact List.pairwise_cons.mpr ⟨fun j hj => e j (by simpa using hj),p⟩
variable (U : Set (Shrine K)) (p : ∀ a, a ≠ b → Philos (σ:=σ) W Ω b a U)
    (h : ∀ i, saucer (W i) (Ω i) = Ω i)
    (e : ∀ i, F i ∈ Magic W U (ν i))
include p h e
lemma lyric (H : ∀ a, (M a).Pairwise (Seers F x a)) (k : ∀ a, (M b).Perm (M a)) (t : (M b).Nodup) :
    AnalyticAt ℝ (fun z => chalk W Ω b ν F z (M b)) x := by
  apply cream W Ω ν F x M _ H
  intro a
  by_cases hb : a=b
  · subst a; exact EventuallyEq.rfl
  filter_upwards [sill F (M a) x a (H a), sill F (M b) x b (H b)] with z χ γ
  exact Cords W Ω b a (M b) ν F z U (p a hb) (h b) (h a) e (M a) (k a) t γ χ
#print axioms lyric
end
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Fuchsia
