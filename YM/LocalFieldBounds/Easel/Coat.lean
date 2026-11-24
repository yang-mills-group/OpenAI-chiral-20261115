import YM.LocalFieldBounds.Easel.Fold

/-!
# Choiring
-/
open Function Filter MeasureTheory Metric Set
open scoped Topology Classical
noncomputable section
namespace YM.LocalFieldBounds.Easel
open GarnetAct.Cut

/-- Quadrature schedules. A finite mending chosen with no operator
questions; 'chopping' authenticates, even allowing zero cells. -/
structure Coat (F : Curtain) (n : ℕ) where
  Job : Type
  list : Fintype Job
  note : Job → Paper
  ink : Job → ℝ
  stays : ∀ i, note i ∈ F.boxS
  chopping : ∃ code : Paper → Job,
    (∀ i, MeasurableSet (code ⁻¹' {i})) ∧
    (∀ p ∈ F.boxS, dist (note (code p)) p < 1/(n+1:ℝ)) ∧
    ∀ i, ink i = F.ppm.real (code ⁻¹' {i})

attribute [instance] Coat.list

namespace Coat
variable {F : Curtain} {n : ℕ}

private lemma choice {B : Type} [Fintype B] [Nonempty B] [MeasurableSpace B]
    (g : B → Paper) (r : ℝ) (s : Finset B) :
    ∃ t : Paper → B, Measurable t ∧
      ∀ x, (∃ i∈s, x∈ ball (g i) r) → dist (g (t x)) x < r := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary B, measurable_const, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨t,h,u⟩ := ih
    refine ⟨fun x => if x ∈ ball (g a) r then a else t x,
      Measurable.ite measurableSet_ball measurable_const h,?_⟩
    rintro x ⟨b,hb,hx⟩
    dsimp only
    by_cases v : x ∈ ball (g a) r
    · rw [if_pos v, dist_comm]; exact v
    rw [if_neg v]
    refine u x ⟨b,(Finset.mem_insert.mp hb).resolve_left ?_,hx⟩
    intro w; exact v (w ▸ hx)

lemma weave (F : Curtain) (n : ℕ) : Nonempty (Coat F n) := by
  let r := 1/(n+1:ℝ)
  obtain ⟨s,h⟩ := F.ownsK.elim_finite_subcover
    (fun i : F.boxS => ball (i.val:Paper) r)
    (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr
      ⟨⟨x,hx⟩,mem_ball_self (by change 0 < 1/(n+1:ℝ); positivity)⟩)
  let g (i:s):Paper := i.val.val
  have cover (x : Paper) (hx : x ∈ F.boxS) :
      ∃ i ∈ (Finset.univ:Finset s), x ∈ ball (g i) r := by
    obtain ⟨i,hi,hi'⟩ := Set.mem_iUnion₂.mp (h hx)
    exact ⟨⟨i,hi⟩, Finset.mem_univ _, hi'⟩
  letI : Nonempty s := by
    obtain ⟨x,hx⟩ := F.inhabits.exists
    exact ⟨(cover x hx).choose⟩
  obtain ⟨t,e,m⟩ := choice g r Finset.univ
  exact ⟨
    { Job := s
      list := inferInstance
      note := g
      stays := fun i => i.val.property
      ink := fun i => F.ppm.real (t ⁻¹' {i})
      chopping := ⟨t,fun i => e (measurableSet_singleton _),fun x hx => m x (cover _ hx), fun _ => rfl⟩ }⟩
attribute [instance] weave

section app
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (C : Coat F n)
abbrev offer (f : Paper → H) := ∑ i, C.ink i • f (C.note i)

lemma weight (i : C.Job) : 0 ≤ C.ink i := by
  obtain ⟨t,-,-,w⟩ := C.chopping; rw [w]; exact measureReal_nonneg

lemma snapshot (f : Paper → H) (t : Paper → C.Job) (meas : ∀ i, MeasurableSet (t ⁻¹' {i}))
    (w : ∀ i, C.ink i = F.ppm.real (t ⁻¹' {i})) :
    Integrable (fun x => f (C.note (t x))) F.ppm ∧
    (∫ x, f (C.note (t x)) ∂ F.ppm) = C.offer f := by
  let g (i) := (t ⁻¹' {i}).indicator (fun _ => f (C.note i))
  have h : (fun x => f (C.note (t x))) = fun x => ∑ i, g i x := by
    ext x
    rw [Finset.sum_eq_single (t x) _ (by simp)]
    · exact (indicator_of_mem (show x ∈ t ⁻¹' {t x} from rfl) (fun _ => f (C.note (t x)))).symm
    · exact fun y _ h => indicator_of_notMem (show x ∉ t ⁻¹' {y} from Ne.symm h) (fun _=> f (C.note y))
  have v (i : C.Job) (_:i∈ Finset.univ) : Integrable (g i) F.ppm :=
    (integrable_const _).indicator (meas i)
  have u (i) : ∫ x, g i x ∂ F.ppm = C.ink i • f (C.note i) := by
    unfold g
    rw [integral_indicator (meas i), setIntegral_const, w]
  constructor
  · rw [h]; exact integrable_finsetSum _ v
  · rw [h, integral_finsetSum _ v]; simp_rw [u]

lemma tender : ∑ i, C.ink i = 1 := by
  obtain ⟨t,h,-,w⟩ := C.chopping
  simpa [offer] using (C.snapshot (fun _ => (1:ℝ)) t h w).2.symm


theorem calibration (C : ∀ n, Coat F n) {f : Paper → H} (hf : Continuous f) :
    Tendsto (fun n => (C n).offer f) atTop (𝓝 (∫ x, f x ∂ F.ppm)) := by
  have ht : Integrable f F.ppm := by
    obtain ⟨a,h⟩ := (F.ownsK.image hf.norm).bddAbove
    exact Integrable.of_bound hf.aestronglyMeasurable a
      (F.inhabits.mono fun x hx => h ⟨x,hx,rfl⟩)
  refine Metric.tendsto_nhds.2 (fun e he => ?_)
  obtain ⟨r,hr,h⟩ := Metric.uniformContinuousOn_iff.1
    (F.ownsK.uniformContinuousOn_of_continuous hf.continuousOn)
    (e/2) (half_pos he)
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)] with n hn
  obtain ⟨t,hp,p,w⟩ := (C n).chopping
  rw [dist_eq_norm, ← ((C n).snapshot f t hp w).2,
    ← integral_sub ((C n).snapshot f t hp w).1 ht]
  refine (norm_integral_le_of_norm_le_const (C:=e/2) ?_).trans_lt ?_
  swap;  · simpa using (half_lt_self he)
  filter_upwards [F.inhabits] with x hx
  rw [←dist_eq_norm]
  exact (h _ ((C n).stays _) x hx ((p _ hx).trans hn)).le

end app
end Coat
end YM.LocalFieldBounds.Easel
