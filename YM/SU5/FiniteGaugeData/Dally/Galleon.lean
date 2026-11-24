import YM.SU5.FiniteGaugeData.Dally.Fuchsia
/-!
 # Moving price for the point sensors. Normal analytics together labels.
 -/
noncomputable section
open Metric Filter Function WithLp
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon
open Gem Leal Leal.Breve Celeritas Land Mist _root_.YM Dally Fuchsia OS OS.Semigroup
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space)
    (A : Tribe G)
variable (a b : Axis) {n : ℕ} (x : Points n) (L : List (Fin n)) (u : Fin n → ι) (p : L.Perm (Each n))
local notation "☂" => Points n
abbrev Vol (i : Fin n) := colorP (G.P (u i)).amount
abbrev Palette := ∀ i, Vol G u i
variable (w : Palette G u)
def sailK : Fin n → G.Chip := fun i => ⟨u i,w i⟩
abbrev weigh := Gem.evaluate x W G ω A (sailK G u w) L a
local notation "⟪" L "," w "⟫₁" => weigh W G ω A a x L u w
private def car (i : Fin n) : Vol G u i →ₗ[ℂ] (K a).Op :=
  (LinearMap.mulRight ℂ (M (W a) (- (SEP a (x i)).val))).comp ((LinearMap.mulLeft ℂ (M (W a) (SEP a (x i)).val)).comp (A.legato a (u i)).toLinearMap)
private abbrev JVM (i : Fin n) := car W G A a x u i (w i)
private abbrev Nut : Fin n → Fin n → (K a).Op := rho (W a) (G.credit (sailK G u 0)) (clockV a x)
private def Banner : (K a).Op := Film (JVM W G A a x u w) (Nut W G a x u) L
private lemma bannerLink : ⟪L,w⟫₁ = inner ℂ (ω a) (Banner W G A a x L u w (ω a)) := by
  unfold weigh; rw [utop]; rfl
private lemma lapse (i : Fin n) (h : i ∉ L) (z : Vol G u i) :
    Banner W G A a x L u (update w i z) = Banner W G A a x L u w := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    have ⟨H,k⟩ := (show i ≠ j ∧ i ∉ L from by simpa only [List.mem_cons, not_or] using h)
    let Q := Nut W G a x u
    unfold Banner
    rw [Film_step, Film_step, show JVM W G A a x u (update w i z) j = JVM W G A a x u w j from
      congrArg (fun z => car W G A a x u j z) (update_of_ne (Ne.symm H) _ _)]
    unfold Banner at ih
    rw [ih k]
private lemma opal (d : L.Nodup) (i : Fin n) (h : i ∈ L) :
    ∃ f : Vol G u i →ₗ[ℂ] (K a).Op, ∀ z, Banner W G A a x L u (update w i z) = f z := by
  induction L with
  | nil => simp at h
  | cons j L ih =>
    let Q := clip (Nut W G a x u) j L
    obtain ⟨B,D⟩ := List.nodup_cons.mp d
    rcases List.mem_cons.mp h with v|v
    · subst j
      refine ⟨(LinearMap.mulRight ℂ (Q* Banner W G A a x L u w)).comp (car W G A a x u i),fun z => ?_⟩
      change car W G A a x u i _ * (Q * Banner W G A a x L u _) = car W G A a x u i z * _
      rw [lapse W G A a x L u w i B, update_self]
    obtain ⟨f,e⟩ := ih D v
    have ne : j ≠ i := fun t => B (t.symm ▸ v)
    let J := car W G A a x u j
    refine ⟨(LinearMap.mulLeft ℂ (J (w j))).comp ((LinearMap.mulLeft ℂ Q).comp f), fun z => ?_⟩
    change J _ * (Q * Banner W G A a x L u _) = J (w j)*(Q*f z)
    rw [update_of_ne ne, e]
include p
private lemma azure (i : Fin n) : ∃ f : Vol G u i →ₗ[ℂ]ℂ, ∀ z, ⟪L, update w i z⟫₁ = f z := by
  obtain ⟨f,H⟩ := opal W G A a x L u w (p.nodup_iff.mpr (List.nodup_finRange _)) i (p.mem_iff.mpr (List.mem_finRange i))
  let J := (innerSL ℂ (ω a)).comp (ContinuousLinearMap.apply ℂ (K a).space (ω a))
  refine ⟨J.toLinearMap.comp f, fun z => ?_⟩
  rw [bannerLink,H]; rfl
def métier : MultilinearMap ℂ (Vol G u) ℂ := MultilinearMap.mk' (weigh W G ω A a x L u)
  (fun w i r s => by obtain ⟨f,H⟩ := azure W G ω A a x L u p w i; rw [H,H,H,map_add])
  (fun w i c r => by obtain ⟨f,H⟩ := azure W G ω A a x L u p w i; rw [H,H,map_smul])
#print axioms métier
omit p
abbrev Chasm := ∀ i, Fin (G.P (u i)).amount
def line (q : Chasm G u) : Palette G u := fun i => EuclideanSpace.basisFun (Fin (G.P (u i)).amount) ℂ (q i)
def swirl (q : Chasm G u) : ℂ := ∏ i, w i (q i)
include p
lemma lacquer : ⟪L,w⟫₁ = ∑ q : Chasm G u, swirl G u w q * ⟪L,line G u q⟫₁ := by
  let f := métier W G ω A a x L u p
  let E (i : Fin n) (j : Fin (G.P (u i)).amount) := w i j • EuclideanSpace.basisFun (Fin (G.P (u i)).amount) ℂ j
  have H := f.map_sum E
  rw [show (fun i => ∑ j, E i j) = w from funext fun i => (EuclideanSpace.basisFun _ ℂ).sum_repr (w i)] at H
  refine H.trans (Finset.sum_congr rfl fun q _ => ?_)
  exact f.map_smul_univ (fun i => w i (q i)) (line G u q)
omit p
lemma tav {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → Palette G u)
    (v : E) (e : AnalyticAt ℝ f v) (q : Chasm G u) :
    AnalyticAt ℝ (fun x => swirl G u (f x) q) v := by
  unfold swirl
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  let L₀ := (PiLp.proj (p := 2) (β := fun _ : Fin (G.P (u i)).amount => ℂ) (𝕜:=ℝ) (q i))
  exact (L₀.analyticAt _).comp (analyticAt_pi_iff.mp e i)
#print axioms lacquer
/- `Capable` tracks view-open Point positions. `longitude` then *all* at once. -/
def capable := Injective (clockV a x)
def chart := L.Perm (Each n) ∧ ProofOrder x a L
lemma chart_unique {M : List (Fin n)} (h : chart a x L) (k : chart a x M) : L=M := List.Perm.eq_of_pairwise
  (fun i j _ _ (u : x i a < x j a) (v : x j a < x i a) => (not_lt_of_ge u.le v).elim) h.2 k.2 (h.1.trans k.1.symm)
lemma capable_iff : capable a x ↔ ∃ L : List (Fin n), chart a x L := by
  refine ⟨SortApp _, ?_⟩
  rintro ⟨L,p,h⟩
  have u : (L.map (clockV a x)).Nodup := List.Pairwise.nodup (List.pairwise_map.mpr h)
  exact List.nodup_ofFn.mp (show (List.ofFn (clockV a x)).Nodup from (by rw [List.ofFn_eq_map]; exact (p.map _).nodup_iff.mp u))
lemma earth (h : chart a x L) : ∀ᶠ y in 𝓝 x, chart a y L := by
  filter_upwards [(PEye a L).mem_nhds h.2] with y hy using ⟨h.1,hy⟩
lemma capable_open (n : ℕ) : IsOpen {x : Points n| capable a x} := isOpen_iff_mem_nhds.mpr fun x h => by
  obtain ⟨L,H⟩ := (capable_iff a x).1 h
  exact (earth a x L H).mono fun y hy => (capable_iff a y).2 ⟨L,hy⟩
def longitude := ∀ a : Axis, capable a x
lemma longitude_open (n : ℕ) : IsOpen {x : Points n| longitude x} := isOpen_iff_mem_nhds.mpr fun _ h =>
  eventually_all.mpr fun a => (capable_open a n).mem_nhds (h a)
open scoped Classical
-- Point-sensor traffic. Pulled only when actual layout valid.
def ticket : ℂ := if h : capable a x then weigh W G ω A a x (((capable_iff a x).mp h).choose) u w else 0
lemma honor (h : chart a x L) : ticket W G ω A a x u w = ⟪L,w⟫₁ := by
  rw [ticket, dif_pos ((capable_iff a x).2 ⟨L,h⟩), chart_unique a x _ (Exists.choose_spec _) h] -- proof irr.
lemma purse {U : Set (Shrine K)} (hp : ∀ a b : Axis,b ≠ a → Philos (σ:=Fin n) W ω a b U)
    (hc : ∀ i, saucer (W i) (ω i)=ω i) (g : Stamp W G A U)
    (ha : capable a x) (hb : capable b x) : ticket W G ω A a x u w=ticket W G ω A b x u w := by
  by_cases z : b = a
  · rw [z]
  obtain ⟨L,p⟩ := (capable_iff a x).1 ha
  obtain ⟨M,q⟩ := (capable_iff b x).1 hb
  rw [honor W G ω A a x L u w p, honor W G ω A b x M u w q]
  let K' := sailK G u w
  exact Cords W ω a b L (G.credit K') (imprint G A ∘ K') x.ofLp U (hp _ _ z) (hc _) (hc _)
    (fun i => g.pay (K' i)) M (p.1.trans q.1.symm) (p.1.nodup_iff.mpr (List.nodup_finRange _))
    ((mapsIn x G A K' L a).1 p.2) ((mapsIn x G A K' M b).1 q.2)
lemma dock (h : capable a x) : ContinuousAt (fun p : Points n × Palette G u => ticket W G ω A a p.1 u p.2) (x,w) := by
  obtain ⟨L,H⟩ := (capable_iff a x).1 h
  let f (q : Chasm G u) (p : Points n × Palette G u) : ℂ := weigh W G ω A a p.1 L u (line G u q)
  have Y (q) : ContinuousAt (f q) (x,w) := by
    unfold f weigh
    simp_rw [utop]
    exact (grounded _ _ x _ _ _ H.2).comp (f:=Prod.fst) (x := (x,w)) continuous_fst.continuousAt
  apply ContinuousAt.congr_of_eventuallyEq (f:=fun y => ∑ q, swirl G u y.2 q * f q y)
    (tendsto_finsetSum _ fun q _ => ((tav G u Prod.snd _ analyticAt_snd q).continuousAt).mul (Y q))
  filter_upwards [continuous_fst.continuousAt.eventually (earth a x L H)] with y hy using
    (honor W G ω A a _ L u _ hy).trans (lacquer W G ω A a _ L u H.1 _)
lemma terra {U : Set (Shrine K)} (hp : ∀ b,b ≠ a → Philos (σ:=Fin n) W ω a b U)
    (hc : ∀ i, saucer (W i) (ω i)=ω i) (g : Stamp W G A U)
    (ha : longitude x) : AnalyticAt ℝ (fun p : Points n × Palette G u => ticket W G ω A a p.1 u p.2) (x,w) := by
  choose M H using fun i => (capable_iff i x).1 (ha i)
  let f (q : Chasm G u) (p : Points n × Palette G u) : ℂ := weigh W G ω A a p.1 (M a) u (line G u q)
  have Y (q) : AnalyticAt ℝ (f q) (x,w) := by
    let K' := sailK G u (line G u q)
    have Eve := lyric W ω (G.credit K') (imprint G A ∘ K') x.ofLp a M U hp hc (fun i => g.pay (K' i))
      (fun i => (mapsIn x G A K' (M i) i).1 (H i).2) (fun b => (H a).1.trans (H b).1.symm)
      ((H a).1.nodup_iff.mpr (List.nodup_finRange _))
    let Z := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)).toContinuousLinearMap
    have e : AnalyticAt ℝ (fun z : Points n => weigh W G ω A a z (M a) u (line G u q)) x := Eve.comp (f:= Z) (Z.analyticAt x)
    exact e.comp (f:=Prod.fst) (x := (x,w)) analyticAt_fst
  refine AnalyticAt.congr (f:=fun y => ∑ q, swirl G u y.2 q * f q y)
    (Finset.analyticAt_fun_sum _ (fun q _ => (tav G u Prod.snd _ analyticAt_snd q).mul (Y q))) (EventuallyEq.symm ?_)
  filter_upwards [continuous_fst.continuousAt.eventually (earth a x (M a) (H a))] with y hy using
    (honor W G ω A a _ (M a) u _ hy).trans (lacquer W G ω A a _ (M a) u (H a).1 _)
#print axioms dock
#print axioms terra
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon
