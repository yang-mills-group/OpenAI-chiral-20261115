import GaugeFieldConstruction.Certification
/-!
# Reading and its exact spaces
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Cauchy.Row.Record
open Set Function Vouchers Submodule Certificate Raw Module
variable {X Z α β γ : Type*} {R : Record X Z} {A : Labels α} {B : Labels β} {C' : Labels γ}

lemma reading_add {x : α → J X} {y : β → J X} (h : R.Reading A x) (p : R.Reading B y) :
    R.Reading (A.directSum B) (Sum.elim x y) := by
  constructor
  intro s w u hu i
  cases i with
  | inl a => exact h.moving s w u hu a
  | inr b => exact p.moving s w u hu b

section Sums
variable [Fintype α] [Fintype β]
lemma space_sum (x : α → J X) (y : β → J X) : space (Sum.elim x y)=space x ⊔ space y := by
  simp only [space,Fintype.range_linearCombination]; rw [← span_union]
  congr; simp

lemma allowed_add {x : α → J X} {y : β → J X} (h : R.Reading A x) (p : R.Reading B y) :
    R.allowed C' (space x ⊔ space y)= R.allowed C' (space x) ⊔ R.allowed C' (space y) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [← space_sum, paid_span C' (reading_add h p), paid_span C' h,paid_span C' p]
    rintro v ⟨r,hr,rfl⟩
    let a (z : α × γ) := r (Sum.inl z.1,z.2)
    let b (z : β × γ) := r (Sum.inr z.1,z.2)
    have he : dot (Sum.elim x y) r = dot x a + dot y b := by
      ext1 i; rw [dot_apply, Pi.add_apply,dot_apply,dot_apply,Fintype.sum_sum_type]; rfl
    rw [he]; apply Submodule.add_mem_sup
    · exact ⟨a,fun g i=> hr g (Sum.inl i.1,i.2),rfl⟩
    exact ⟨b,fun g i=> hr g (Sum.inr i.1,i.2),rfl⟩
  · unfold allowed; exact inf_le_inf_left _ (Submodule.pi_mono fun _ _ _ h =>
       show _∈space x ⊔ space y from (show space x≤_ from le_sup_left) h)
  unfold allowed; exact inf_le_inf_left _ (Submodule.pi_mono fun _ _ _ h=>
       show _∈space x ⊔ space y from (show space y≤_ from le_sup_right) h)

variable [DecidableEq α] [DecidableEq β]
lemma document {f : α → J X} (h : R.Reading A f) (l : List (α × β)) (hu : Picked (A.tensorProd B) l) :
    R.allowed B (space f)=line (l.map (Record.column B A f)) := by
  rw [Record.span_columns B h l hu, line]; congr; ext i; simp
lemma document_pick {f : α → J X} (h : R.Reading A f) (l : List (α × β)) (hu : Picked (A.tensorProd B) l)
    (b : List Bool) (hw : Scan0 (l.map (Record.column B A f)) b) : R.allowed B (space f)=
      line (pick b (l.map (Record.column B A f))) := by
  rw [document h _ hu]; simpa only [bot_sup_eq] using accumulated _ b ⊥ hw
lemma erase {f : α→ J X} (h : R.Reading A f) (hu : Picked (A.tensorProd B) []) :
    R.allowed B (space f)=⊥ := by rw [document h _ hu]; simp [line]
end Sums
section Rank
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
lemma lined (u : List V) [DecidableEq V] : line u=span ℂ (u.toFinset : Set V) := by
  unfold line; congr; ext p; simp; -- tweak
lemma finite_line (u : List V) : FiniteDimensional ℂ (line u) := by
  classical
  rw [lined]; infer_instance
lemma counted (l : List V) (b) (h : Scan0 l b) : finrank ℂ (line l)=b.count true := by
  have hr := counts l b ⊥ h; rwa [bot_sup_eq,finrank_bot,Nat.zero_add] at hr
lemma line_map (l : List V) (f : V →ₗ[ℂ] W) : map f (line l)=line (l.map f) := by
  classical
  rw [lined,map_span,lined]; congr; ext i; simp
lemma line_combine (l r : List V) : line (l++r)=line l⊔line r := by
  classical
  rw [lined, lined, lined, ← span_union]; congr; ext i; simp
end Rank
end YM.GaugeFieldConstruction.Cauchy.Row.Record
