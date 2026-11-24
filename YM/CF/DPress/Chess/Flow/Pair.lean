import YM.CF.DPress.Chess.Flow.Street
import Mathlib.Probability.Independence.Integration
set_option autoImplicit false
noncomputable section
-- Pair independence for unions measured by restriction setoids.
namespace YM.CF.DPress.Chess.Transit
open Function Filter Lattice RG MeasureTheory ProbabilityTheory Push.GridApprox FD Set
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal
variable {X Y Z:Type*}[MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z]
variable {μ:Measure X}{ν:Measure Y}{S T:Setoid X}{A B:Setoid Y}
def Pairm (μ:Measure X)(S T: Setoid X):Prop:=∀ F K: Set X,MeasurableSet F→MeasurableSet K→Uses (·∈ F) S → Uses (·∈ K) T→ μ (F∩K)= μ F*μ K
lemma Pairm.extract {f:X→Y}{g:X→Z} (p:Pairm μ S T)(h:Measurable f)(t:Measurable g)(e:Uses f S)(v:Uses g T): IndepFun f g μ:=by
 refine indepFun_iff_measure_inter_preimage_eq_mul.mpr fun A B u w=> p _ _ (h u) (t w) ?_ ?_; exact (fun x y p=>by change (f x∈ A)=(f y∈A); rw [e _ _ p]); exact (fun x y p=>by change (g x∈B)=(g y∈B); rw [v _ _ p])
abbrev Pairm.ofOrd {X' : Type*}[Fintype X']{R: X'→X'→Prop}(U:OrderF R μ){S T:Finset X'} (p:FD.Meeting R S T): Pairm μ (U.see S) (U.see T):=fun X Y u v i j=> U.pair S T p _ _ u v i j
abbrev joins {X Y:Type*}(F:Setoid X)(G:Setoid Y) : Setoid (X×Y) := Cash.join F G
lemma Pairm.symm(p:Pairm μ S T): Pairm μ T S:=fun x y u v f e=>by rw [inter_comm, mul_comm]; exact p _ _ v u e f
abbrev Respects {X Y:Type*}(S:Setoid X)(T:Setoid Y)(f:X→Y):Prop:= ∀ i j,S.r i j→ T.r (f i) (f j)
lemma Pairm.map {f:X→ Y}(p: Pairm μ S T)(h: MeasurePreserving f μ ν)(e: Respects S A f)(v:Respects T B f): Pairm ν A B:=by intro F Z x y i j; rw [←h.map_eq,Measure.map_apply h.measurable x,Measure.map_apply h.measurable y,Measure.map_apply h.measurable (x.inter y),preimage_inter]; exact p _ _ (h.measurable x) (h.measurable y) (fun x y t=>i _ _ (e x y t)) (fun x y t=> j _ _ (v x y t))
abbrev cropX {X Y:Type*}(F: Set (X×Y))(x:X): Set Y:= Prod.mk x ⁻¹' F
lemma Pairm.joint [IsProbabilityMeasure μ][IsProbabilityMeasure ν](p:Pairm μ S T)(t: Pairm ν A B): Pairm (μ.prod ν) (joins S A) (joins T B):=by
 intro D C g h i j; let Z(K:Set (X×Y))(x:X):= ν (cropX K x); have ht{F:Setoid X}{K:Setoid Y}{D:Set (X×Y)}(t:Uses (·∈D) (joins F K)): Uses (Z D) F:=fun x y p=> congrArg ν (Set.ext fun i=> Eq.to_iff (t (x,i) (y,i) ⟨p,K.iseqv.refl i⟩)); have hh(x:X):Z (D∩C) x=Z D x*Z C x:= t _ _ (measurable_prodMk_left g) (measurable_prodMk_left h) (fun y z t=> i (x,y) (x,z) ⟨S.iseqv.refl _,t⟩) (fun y z t=> j (x,y) (x,z) ⟨T.iseqv.refl _,t⟩)
 rw [Measure.prod_apply (g.inter h),Measure.prod_apply g,Measure.prod_apply h]; change (∫⁻ x, Z (D∩C) x∂μ)= (∫⁻ x,Z D x ∂μ)*∫⁻ x,Z C x∂μ; simp_rw [hh]; have he(F:Set (X×Y))(u:MeasurableSet F):Measurable (Z F):=measurable_measure_prodMk_left u; exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (he D g) (he C h) (p.extract (he D g) (he C h) (ht i) (ht j))
section
variable {R:Type*}[NormedRing R][NormedAlgebra ℝ R][CompleteSpace R][MeasurableSpace R][BorelSpace R][SecondCountableTopology R]{f g:X→ R}
lemma Pairm.money [IsProbabilityMeasure μ](p:Pairm μ S T)(h: Envelope f)(t:Envelope g)(u:Uses f S)(v: Uses g T): (∫ x,f x * g x ∂μ)= (∫ x,f x∂μ)*(∫ x,g x∂μ):=by
 have hi{x: X→R}(h:Envelope x):Integrable x μ:= Integrable.of_bound (h.meas.aestronglyMeasurable) _ (Eventually.of_forall h.cost.choose_spec); exact (p.extract h.meas t.meas u v).integral_bilin (hi h) (hi t) (ContinuousLinearMap.mul ℝ R)
end
end YM.CF.DPress.Chess.Transit
