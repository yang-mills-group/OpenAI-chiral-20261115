import YM.CF.Vp929.Borel.Aerial
import YM.CF.Vp929.Borel.Vast
set_option autoImplicit false
set_option maxHeartbeats 660000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory
open Mesh Lattice Atlas Skye Cane Spire Scroll SU Cube Lat Aerial
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
namespace Sample
variable (n:Side) {I:Type*} [Nonempty I][Fintype I][MeasurableSpace I][MeasurableSingletonClass I][StandardBorelSpace I]
def MinTag(S:Finset (Seat n))(w: Pri n):ℝ:= w (greet S w)
lemma meast(S:Finset (Seat n)): Measurable (MinTag n S) := Skye.mealM (F:=fun a:Pri n=>greet S a) (fun i=> mastM _ (measurableSet_singleton i)) (G:=fun i x=>x i) (fun i=> measurable_pi_apply i)
def letU(S:Finset (Seat n)): Measure ℝ:= (μ n).map (MinTag n S)
instance (S:Finset (Seat n)): IsProbabilityMeasure (letU n S):= Measure.isProbabilityMeasure_map (meast n S).aemeasurable
instance (S:Finset (Seat n)) : NullSingletonClass (letU n S):=by
 -- even empty. greet always some seat.
 constructor; intro x; unfold letU; rw [Measure.map_apply (meast n S) (measurableSet_singleton _)]; apply measure_mono_null (t:=⋃i:Seat n,(fun j:Pri n=>j i) ⁻¹' {x}); · intro v k; apply Set.mem_iUnion.mpr; exact ⟨greet S v,k⟩
 apply measure_iUnion_null; intro i; have h: MeasurePreserving (fun v:Pri n=>v i) (μ n) pale:= measurePreserving_eval _ _; rw [h.measure_preimage (measurableSet_singleton x).nullMeasurableSet,MeasureTheory.measure_singleton]
lemma swirl (S: Finset (Seat n))(t:Sweep n)(h:S.Nonempty): letU n (S.map (boxA t).symm.toEmbedding)=letU n S:=by
 let E:= boxA t; let T:= S.map E.symm.toEmbedding; let f(x:Pri n) := x ∘ E; have ht: MeasurePreserving f (μ n) (μ n) := by have h:= measurePreserving_piCongrLeft (fun _:Seat n=> pale) E.symm; convert h using 1 <;> (first|rfl|skip); ext; simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,f]
 have V(x:Pri n): MinTag n T (f x)=MinTag n S x:=by
    have P:= mastP T (Finset.map_nonempty.mpr h) (f x); let Q:= mastP S h x; let a:= greet S x; let b:=greet T (f x); apply le_antisymm; · exact (P.2 (E.symm a) (Finset.mem_map_of_mem _ Q.1)).trans_eq (show f x (E.symm a)=x a by simp [f])
    change x a ≤ x (E b); exact Q.2 _ (show E b∈S from by simpa [T,b] using P.1)
 unfold letU; change (μ n).map (MinTag n T)=_; nth_rw 1 [← ht.map_eq]; rw [Measure.map_map (meast n T) ht.measurable, show MinTag n T∘f=MinTag n S from funext V]
variable (p:Ticket I)
private def token(μ:Measure ℝ)[IsProbabilityMeasure μ][NullSingletonClass μ]:ℝ→I:=(samplerY p.Law μ).choose
def samp(S:Finset (Seat n)):ℝ→I:= token p (letU n S)
lemma stint(S:Finset (Seat n)) : MeasurePreserving (samp n p S) (letU n S) p.Law:= (samplerY p.Law _).choose_spec
lemma tokens(S:Finset (Seat n))(t:Sweep n): samp n p (S.map (boxA t).symm.toEmbedding)=samp n p S :=by
 by_cases h:S.Nonempty; swap; · rw [not_nonempty_iff_eq_empty.mp h]; simp
 have z:∀ (x y:Measure ℝ) [IsProbabilityMeasure x] [IsProbabilityMeasure y] [NullSingletonClass x] [NullSingletonClass y], x=y → token p x=token p y:= by intro x y X Y A B e; subst x; rfl
 exact z _ _ (swirl n S t h)
end Sample
end YM.CF.VolumeCape.Borel
