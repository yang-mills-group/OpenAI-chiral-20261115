import YM.CF.DPress.FD.Law.Order
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Set Lattice MeasureTheory ProbabilityTheory Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {X Y Z I J:Type*}[Fintype I][Fintype J][MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z] {n:Side}{r:ℕ}
namespace OrderF
variable [MeasurableSpace I][MeasurableSingletonClass I]
-- Vision extension measure
abbrev extend (V:Vision n r I) : OrderF (fun i j: Site n=>r<separation i j) V.c.PM where
 see := V.set
 more:= V.le
 pair S T h F K _ _ f k:= by rw [pm_apply,pm_apply,pm_apply]; simp only [Set.mem_inter_iff]; rw [V.c.region (V.dim S T h) _ _ f k]; rw [ENNReal.ofReal_mul (V.c.size _)] -- eta pattern fails
end OrderF
namespace BasicIid
open OrderF
abbrev few (S:Finset I)(X:I→Y): (↥S→Y):= fun i=> X i.val
lemma key {S:Finset I}{x y:I→ Y}: few S x=few S y↔ EqOn x y S:= by refine ⟨fun h i p=>congrFun h ⟨i,p⟩,fun h=> funext fun i=>h i.property⟩
variable [Nonempty Y]{μ: I→Measure Y} [∀ i,IsProbabilityMeasure (μ i)]
abbrev P2 (I:Type*)(x y:I):Prop:= x≠y
private lemma piSets {A:Set (I→ Y)}{D:Finset I}(f: Uses (·∈ A) (ruleFx (few D)))(t:MeasurableSet A):∃ S:Set (↥D→Y),MeasurableSet S∧A=few D ⁻¹' S:=by
 let F(x:↥D→Y):= fun i:I=> if p:i∈D then x ⟨i,p⟩ else Classical.arbitrary Y; have h:Measurable F:=measurable_pi_lambda _ (fun i=> by unfold F; split; exact measurable_pi_apply _; exact measurable_const); exact ⟨F ⁻¹' A,h t, Set.ext fun i=> Eq.to_iff (f i (F (few D i)) (funext (fun x=> by dsimp only [few,F]; rw [dif_pos x.property])))⟩
lemma P2U {S T:Finset I} : Meeting (P2 I) S T ↔ Disjoint S T:=by
 refine ⟨fun t=>Finset.disjoint_left.mpr (fun i x p=> t i x i p rfl), fun t i x j p u=>Finset.disjoint_left.mp t x (u.symm ▸ p)⟩
abbrev orb(μ:I→Measure Y)[∀ i,IsProbabilityMeasure (μ i)] : OrderF (P2 I) (Measure.pi μ) where
 see S := ruleFx (few S)
 more S T v x y g:=key.mpr ((key.mp g).mono (Finset.coe_subset.mpr v))
 pair S T h F K x y f g:=by
    have ht: IndepFun (few (Y:=Y) S) (few T) (Measure.pi μ):=(iIndepFun_pi (μ:=μ) (X:=fun _=>id) (fun _=>aemeasurable_id)).indepFun_finset S T (P2U.mp h) (fun i=> measurable_pi_apply _)
    obtain ⟨s,v,rfl⟩:= piSets f x; obtain ⟨t,h,rfl⟩:= piSets g y; exact indepFun_iff_measure_inter_preimage_eq_mul.mp ht s t v h
lemma ears(t:J→I)(h:Injective t) (μ:Measure Y)[IsProbabilityMeasure μ] : MeasurePreserving (fun x:I→Y=> x ∘ t) (Measure.pi (fun _:I=>μ)) (Measure.pi fun _:J=> μ):=by
 refine OrderF.abide (orb fun _:I=> μ) (fun i=>{t i}) (fun i x=>x (t i)) (fun i=> measurePreserving_eval (fun _=>μ) _) (fun i x y p=>congrFun (show few ({t i}: Finset I) x=few _ y from p) ⟨_,Finset.mem_singleton_self _⟩) (fun i j v=> P2U.mpr ?_)
 simp; exact fun l=> v (h l)
end BasicIid
end YM.CF.DPress.FD
