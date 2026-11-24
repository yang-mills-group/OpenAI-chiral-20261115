import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

namespace YM.SU5.FiniteGaugeData.Audit1102
open MeasureTheory ProbabilityTheory

private theorem shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun z : (A × B) × (C × D) =>
      ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have s₁ := measurePreserving_prodAssoc a b (c.prod d)
  have s₂ := (MeasurePreserving.id a).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc b c d))
  have swapBC : MeasurePreserving (Prod.swap : B × C → C × B) (b.prod c) (c.prod b) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have s₃ := (MeasurePreserving.id a).prod (swapBC.prod (MeasurePreserving.id d))
  have s₄ := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have s₅ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc a c (b.prod d))
  exact s₅.comp (s₄.comp (s₃.comp (s₂.comp s₁)))

/-- Combine two independent coordinate readings in each of two independent input laws. -/
theorem product_readings {X Y A B C D : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → A} {g : X → B} {s : Y → C} {t : Y → D}
    (hf : Measurable f) (hg : Measurable g) (hs : Measurable s) (ht : Measurable t)
    (hx : IndepFun f g μ) (hy : IndepFun s t ν) :
    IndepFun (Prod.map f s) (Prod.map g t) (μ.prod ν) := by
  have m₁ : MeasurePreserving (fun x => (f x,g x)) μ ((μ.map f).prod (μ.map g)) :=
    ⟨hf.prodMk hg, hx.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have m₂ : MeasurePreserving (fun y => (s y,t y)) ν ((ν.map s).prod (ν.map t)) :=
    ⟨hs.prodMk ht, hy.map_prod_eq_prod_map_map hs.aemeasurable ht.aemeasurable⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map (hf.prodMap hs).aemeasurable
    (hg.prodMap ht).aemeasurable).2
  rw [← Measure.map_prod_map μ ν hf hs, ← Measure.map_prod_map μ ν hg ht]
  exact ((shuffle (μ.map f) (μ.map g) (ν.map s) (ν.map t)).comp (m₁.prod m₂)).map_eq

/-- Transfer independence of two measurements through equality of the full output laws. -/
theorem transfer_readings {X Y V A B : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → V} {g : Y → V} (hf : Measurable f) (hg : Measurable g)
    (h : μ.map f = ν.map g) {p : V → A} {q : V → B}
    (hp : Measurable p) (hq : Measurable q) (hi : IndepFun (p ∘ g) (q ∘ g) ν) :
    IndepFun (p ∘ f) (q ∘ f) μ := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (hp.comp hf).aemeasurable
    (hq.comp hf).aemeasurable).2
  change μ.map ((fun v => (p v,q v)) ∘ f) = (μ.map (p ∘ f)).prod (μ.map (q ∘ f))
  rw [← Measure.map_map (hp.prodMk hq) hf, ← Measure.map_map hp hf, ← Measure.map_map hq hf,
    h, Measure.map_map (hp.prodMk hq) hg, Measure.map_map hp hg, Measure.map_map hq hg]
  exact hi.map_prod_eq_prod_map_map (hp.comp hg).aemeasurable (hq.comp hg).aemeasurable

end YM.SU5.FiniteGaugeData.Audit1102
