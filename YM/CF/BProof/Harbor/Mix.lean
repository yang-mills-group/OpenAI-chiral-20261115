import YM.CF.BProof.Harbor.Value
import YM.Push.GRID_APPROXIMATION.Product
import YM.CF.BProof.Vogue.Coil
-- basic weighted operator transforms (no normalized state). step probabilities & mask errors
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
namespace Wager
variable {X Y I E D: Type}[Fintype I][DecidableEq I][MeasurableSpace X][MeasurableSpace Y]
variable {μ:Measure X}[IsFiniteMeasure μ]{r:X→ℝ}
attribute [local instance] measureVal billVal
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
lemma atMost (F:X × Y→ E) (p:∀ y: Y,Envelope fun x=> F (x,y))[Fintype Y][MeasurableSingletonClass Y] :Envelope F:=by
 have hx:Measurable F:= mealM (F:=Prod.snd) (fun i=>measurable_snd (measurableSet_singleton i)) (G:=fun i (x:X×Y)=>F (x.1,i)) (fun i=>(p i).meas.comp measurable_fst)
 choose c v using fun y=>(p y).cost; refine ⟨hx,∑ i,|c i|,fun i=>(v i.2 i.1).trans ((le_abs_self ..).trans (Finset.single_le_sum (f:=fun i=>|c i|) (fun i _=>abs_nonneg _) (mem_univ _)))⟩ -- infer args
lemma usual (p:Envelope (r: X→ℝ))(F:X× Y→ E)(he:Envelope F)(μ:Measure X)[IsFiniteMeasure μ] : Envelope (fun y:Y=>avg μ r fun x=>F (x,y)):= by apply Law.fund μ (f:=fun x : Y × X=> r x.2 • F (x.2,x.1)); exact fee (Law.pull (q:=Prod.swap) he measurable_swap) (Law.pull (q:=Prod.snd) p measurable_snd)
abbrev meanS {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (μ:Measure X)(F:X→E):= ∫ x,F x∂μ
lemma usualM (F:X× Y→ E)(he:Envelope F)(μ:Measure X)[IsFiniteMeasure μ] : Envelope (fun y:Y=>meanS μ fun x=>F (x,y)):= Law.fund μ (f:=F∘Prod.swap) (Law.pull (q:=Prod.swap) he measurable_swap)
lemma mean_f [MeasurableSingletonClass X][Finite X] (F:X→E): Envelope F:=by
 letI := Fintype.ofFinite X
 exact ⟨measurable_of_countable _,∑ i, ‖F i‖, fun i=> Finset.single_le_sum (fun i _=>norm_nonneg _) (mem_univ _)⟩
lemma fund_s (μ:Measure X) [IsFiniteMeasure μ] (U:Submodule ℝ E){φ:X→ E}(p:Envelope φ)(h:∀ x, φ x∈U): meanS μ φ∈ U:= by rw [meanS,←one (φ:=φ) μ]; exact abr μ U p (Envelope.const 1) h
end
lemma factorM {F G:X→Op I}(p:Envelope F)(h:Envelope G)(e:∀ i j k:I, meanS μ (fun x=> F x i k * G x k j)=meanS μ (fun x=>F x i k) * meanS μ (fun x=>G x k j)) : meanS μ (fun x=>F x*G x)= meanS μ F * meanS μ G:=by unfold meanS; rw [←one μ (φ:=fun i=>F i*G i),←one (φ:=F),←one (φ:=G)]; apply factor p h (show Envelope (1:X→ℝ) from Envelope.const 1); intro i j k; simp_rw [one]; exact e i j k
section Pair
variable (μ:Measure X)[IsProbabilityMeasure μ](f g:X→ℂ)
lemma shake(Z:X×X→X× X)(h:MeasurePreserving Z (μ.prod μ) (μ.prod μ))(s:Measurable f) (t:Measurable g)(e:∀ x,f (Z x).1*g (Z x).1=f x.1*g x.2): meanS μ (fun x=> f x*g x)=meanS μ f*meanS μ g:=by
 let F(x:X× X):= f x.1*g x.1; rw [meanS,← Law.apply_pres (f:=fun x=> f x*g x) (measurePreserving_fst (μ:=μ) (ν:=μ)) (s.mul t),← Law.apply_pres (f:=F) h ((s.mul t).comp measurable_fst)]; change (∫ x,f (Z x).1*g (Z x).1 ∂ μ.prod μ)=_; simp_rw [e]; exact integral_prod_mul ..
end Pair
end Wager
end YM.CF.BProof.Bide
