import YM.RG.Bounded
import Mathlib.MeasureTheory.Integral.Pi

/- Bounded Borel Fubini and pinned product expectation. Writes with normalized measures
may freely use dummy normalized variables. No conditional law on a positive-measure orbit. -/
set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace YM.CF.BProof.Law
open Function Set RG MeasureTheory Filter
open scoped BigOperators Topology Classical ENNReal
variable {E I B A C D : Type*} [Fintype I][DecidableEq I] [MeasurableSpace A] [MeasurableSpace B][MeasurableSpace C][MeasurableSpace D]
variable (S:Finset I) (μ:I→ Measure B)[∀ i, IsProbabilityMeasure (μ i)]
variable (W V : I→B)

/-- insertion into slot; pin slots outside. -/
def patch (W V:I→B)(i:I) := if i∈S then W i else V i
lemma patch_pres : MeasurePreserving (Function.uncurry (patch (B:=B) S)) ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ):=by
 let g(i:I):=i∈S; let Q:= MeasurableEquiv.piEquivPiSubtypeProd (fun _:I=>B) (· ∈ S); let a:=Measure.pi fun i:{i:I//i∈ S}=>μ i; let b:=Measure.pi fun i:{i:I//i∉ S}=>μ i
 have he : MeasurePreserving Q (Measure.pi μ) (a.prod b):= by unfold Q a b; convert! measurePreserving_piEquivPiSubtypeProd μ (· ∈ S) using 2 <;> congr!
 haveI : IsProbabilityMeasure a:=by unfold a; infer_instance
 haveI : IsProbabilityMeasure b:=by unfold b; infer_instance
 let H : MeasurePreserving (fun p : (I→B)×(I→B) => Q.symm ((Q p.1).1,(Q p.2).2)) ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := (he.symm Q).comp ((measurePreserving_fst (μ:=a) (ν:=b)).comp he |>.prod ((measurePreserving_snd (μ:=a) (ν:=b)).comp he))
 convert H using 1; ext x i; by_cases h:i∈ S<;> simp [Function.uncurry,patch,Q,h]
@[fun_prop] lemma patch_m : Measurable (Function.uncurry (patch (B:=B) S)):= by unfold Function.uncurry patch; apply measurable_pi_lambda; intro i; split <;> fun_prop
lemma patch_on : Set.EqOn (patch S W V) W S:= fun x h=> if_pos h
lemma patch_off : Set.EqOn (patch S W V) V (↑(Sᶜ)):=(fun x hx=> if_neg (Finset.mem_compl.mp hx))

variable {ν : Measure A}{β: Measure B}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma pull {f : B→E}{q:A→B}(h:Envelope f)(g:Measurable q) : Envelope (f ∘ q) := by obtain ⟨C,hC⟩:=h.cost; exact ⟨h.meas.comp g,C,fun _=> hC _⟩
lemma pay {ν:Measure A} [IsFiniteMeasure ν] {f:A→E}(h:Envelope f) : Integrable f ν := by obtain ⟨C,hC⟩:=h.cost; exact Integrable.of_bound h.meas.aestronglyMeasurable C (Eventually.of_forall hC)
lemma apply_pres {g:A→B}{f:B→E} (p:MeasurePreserving g ν β)(h:Measurable f): (∫ x,f (g x) ∂ν)= ∫ y,f y ∂β:=by rw [← p.map_eq]; exact (integral_map p.measurable.aemeasurable h.aestronglyMeasurable).symm -- tune rw
lemma fund {f:A× B→E} (β:Measure B)[IsFiniteMeasure β](h:Envelope f) : Envelope (fun x=> ∫ y,f (x,y) ∂β):=by
 obtain ⟨C,hC⟩:=h.cost; refine ⟨h.meas.stronglyMeasurable.integral_prod_right'.measurable,C*β.real univ,fun x=> norm_integral_le_of_norm_le_const (Eventually.of_forall fun i=> hC _)⟩
lemma refresh {f:(I→B)→E}(h:Envelope f) : (∫ x,f x ∂(Measure.pi μ))= ∫ w, ∫ v,f (patch S w v) ∂(Measure.pi μ) ∂(Measure.pi μ):=by
 rw [←apply_pres (patch_pres S μ) h.meas]; exact integral_prod (f∘(Function.uncurry (patch S))) (pay (pull h (patch_m S)))
lemma income {f:A→E}{β:Measure A}{C:ℝ}[IsProbabilityMeasure β](h:∀ᵐ x∂β,‖f x‖≤C): ‖∫ x,f x ∂β‖≤C:=by simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const h -- tune
end YM.CF.BProof.Law
