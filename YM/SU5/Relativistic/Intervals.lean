import YM.SU5.FiniteGaugeData.Tower.GermEngine

/-!
# Calibration of charts. Use a common physical line on all axes, mesh marks.
``ordered'': permit touching endpoints. Later `Admitted` stencils include
reserve collars in those slabs (auxiliary FiniteGaugeData resolution notion).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeshClock
open scoped Classical Topology NNReal ENNReal
variable {M : Mesh}

abbrev Stamp (M:Mesh) := ↥(marks M)
lemma MeshRead (x : Stamp M): ∀ᶠ s:ℕ in atTop, ∃ i, notch M s i=x:=by
  obtain ⟨s,i,rfl⟩:= notch_exists M x
  filter_upwards [eventually_ge_atTop s] with k h; exact ⟨_,notch_up M s k h _⟩
def Precise (n:ℕ) (x:Stamp M) : Prop:= x∈ Set.range (notch M n)
lemma ReadPrecise (x:Stamp M) : ∀ᶠ s in atTop, Precise s x:= MeshRead x
lemma Precise.collected {n:ℕ} {x : Stamp M} (p:Precise n x) {m:ℕ} (h:n ≤ m) : Precise m x:= by
  obtain ⟨a,rfl⟩:= p; exact ⟨_, notch_up M n m h a⟩
noncomputable def tags (n:ℕ)(x:Stamp M):ℤ:= if h:Precise n x then h.choose else 0
lemma tags_on {x : Stamp M} (n:ℕ)(p:Precise n x): notch M n (tags n x)=x:= by unfold tags; rw [dif_pos p]; exact p.choose_spec

lemma tags_lock (M:Mesh) (n:ℕ)(i:ℤ): tags n (notch M n i)=i:= notch_tight M n (tags_on n ⟨i,rfl⟩)
lemma stamp_le (M:Mesh) (n:ℕ)(i j:ℤ) : notch M n i ≤ notch M n j ↔ i≤ j := bell_le M n i j
lemma stamp_lt (M:Mesh) (n:ℕ)(i j:ℤ) : notch M n i < notch M n j ↔ i< j := lt_iff_lt_of_le_iff_le (stamp_le M n j i)
lemma stamp_neg (M:Mesh) (n:ℕ)(i:ℤ) : notch M n (-i) = - notch M n i := by
  apply eq_neg_of_add_eq_zero_left; rw [←notch_add,neg_add_cancel, notch_zero]
lemma stamp_sub (M:Mesh) (n:ℕ)(i j:ℤ) : notch M n (i-j)= notch M n i - notch M n j := by
  rw [sub_eq_add_neg,notch_add,stamp_neg,sub_eq_add_neg]
lemma mark_time (M:Mesh) (n i:ℕ) : ((notch M n (i:ℤ)):ℝ)= (whenly M n i:ℝ) := natural_time M n i
/-- Heat gap (registered end to registered start). Used only when b ≥ a unless stated. -/
def heatGap (a b:Stamp M):ℝ≥0:= ((b:ℝ)-a.val).toNNReal
lemma heatGap_stamp {a b:ℤ}{W:ℕ}(h:a+(W:ℤ)=b)(n:ℕ) : heatGap (notch M n a) (notch M n b)= whenly M n W:=by
  rw [←h]; unfold heatGap; simp [notch_add,mark_time M] -- tune
lemma heatGap_zero (a:Stamp M) : heatGap a a=0:= by simp [heatGap]
lemma heatGap_concat {a b c:Stamp M}(h:a≤b)(p:b≤c): heatGap a b+heatGap b c= heatGap a c:=by
  apply NNReal.eq; rw [NNReal.coe_add]; simp only [heatGap, Real.coe_toNNReal _ (sub_nonneg.mpr (show a.val≤b.val from h)),Real.coe_toNNReal _ (sub_nonneg.mpr (show b.val ≤ c.val from p)),Real.coe_toNNReal _ (sub_nonneg.mpr (show a.val ≤ c.val from h.trans p))]; abel
structure Slab (M:Mesh) where
  lower : Stamp M
  upper : Stamp M
  thick : lower < upper
namespace Slab
variable (W V:Slab M)
def lines (n:ℕ) : Prop:= Precise n W.lower ∧ Precise n W.upper
lemma grids : ∀ᶠ n:ℕ in atTop, W.lines n:= (ReadPrecise _).and (ReadPrecise _)
lemma lines_above {n m:ℕ}(a:n≤m)(w:W.lines n): W.lines m := ⟨w.1.collected a,w.2.collected a⟩
lemma thickness {n:ℕ}(p:W.lines n) : tags n W.lower < tags n W.upper:= (stamp_lt M n _ _).mp (by rw [tags_on n p.1,tags_on n p.2]; exact W.thick)
end Slab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Slab.grids
