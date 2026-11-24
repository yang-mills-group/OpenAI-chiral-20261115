import YM.CF.BProof.Weights.Pawn
import YM.CF.BProof.Garden.Fruit
/-! Sphere measure for the contour argument. No n-dependent size constants in later transfers.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Payment
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Branch Hearth Angular Mapping Scree
open Moment RG Wilson Charge Release Release.Locale Release.hot Gauss Garden Law
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {s N:Side}(Y:Yard (More N))(y:ℝ)
abbrev Extras(N:Side):= Ids N × Fields N
abbrev petals(N:Side): Measure (Extras N):= (depot N).prod (gardenF N)
abbrev Sphere := Pawn Y × Extras N
abbrev Dish := Locale.House Y × hot.Field Y × Config SU.group (More N) × Extras N
def chase : Measure (Dish Y) := (lobby Y).prod ((Release.pixels Y y).prod ((Cloud (More N) y).prod (petals N)))
instance ridesP (Y:Yard s)(y:ℝ): IsProbabilityMeasure (Release.pixels Y y):=by
 haveI t : IsProbabilityMeasure (Day.mark (trunc y) (Roll.Place Y)) := Day.prob _ _ (pow_pos (pow_pos (coin_pos ..) _) _) -- tune
 apply MeasureTheory.Measure.pi.instIsProbabilityMeasure -- tune
lemma chase_p(h:xi y ≤1): IsProbabilityMeasure (chase Y y):=by
 have he:= cloud_unit SU.group _ (show 0<xi y from coin_pos ..) h; letI:= he; unfold chase; infer_instance
variable (p:Y.Glyph)(S:Finset Y.Col)
def wrap (x:Dish Y): Sphere Y:= (⟨S,uncurry x.2.1,x.1,x.2.2.1,p⟩,x.2.2.2)
lemma wrap_m : Measurable (wrap Y p S):= by
 apply Measurable.prodMk; swap; exact measurable_snd.comp (measurable_snd.comp measurable_snd)
 refine (Pawn.volume Y).measurableEmbedding.measurable_comp_iff.mp ?_; let g (x:Dish Y):= x.2.1; change Measurable (fun x:Dish Y=> ((S,p),(uncurry (g x),x.1),x.2.2.1)); unfold uncurry g; fun_prop
abbrev globeP := Measure.map (wrap Y p S) (chase Y y)
def globe : Measure (Sphere Y):= ∑ p:Y.Glyph,∑ S:Finset Y.Col, globeP Y y p S
lemma sampled : MeasurePreserving (wrap Y p S) (chase Y y) (globeP Y y p S) := ⟨wrap_m Y p S,rfl⟩
variable (h:xi y≤1)
include h
lemma globe_p : IsProbabilityMeasure (globeP Y y p S):= by haveI:= chase_p Y y h; exact Measure.isProbabilityMeasure_map (wrap_m Y p S).aemeasurable
lemma globe' : IsFiniteMeasure (globe Y y):=by
 letI pv(p:Y.Glyph)(S:Finset Y.Col) : IsProbabilityMeasure (globeP Y y p S):= globe_p Y y p S h -- h?
 unfold globe; infer_instance
variable (F:Sphere Y→ℂ)(f:Envelope F)
include f
lemma childF : (∫ x,F x ∂globeP Y y p S)= ∫ a,∫ b,∫ c,∫ z,∫ v, F (wrap Y p S (a,b,c,z,v)) ∂gardenF N ∂depot N ∂Cloud (More N) y ∂pixels Y y ∂lobby Y :=by
 haveI:= cloud_unit SU.group _ (show 0<xi y from coin_pos ..) h; haveI:= chase_p Y y h; let q:=F ∘wrap Y p S; let T:= chase Y y; have hh:Envelope q:= Law.pull f (wrap_m ..)
 rw [← Law.apply_pres (sampled Y y p S) f.meas]; change (∫ x,q x ∂chase Y y)=_; unfold chase; rw [integral_prod q (Law.pay hh)]; apply integral_congr_ae; apply Eventually.of_forall; intro a
 let A:= hot.Field Y; let B:= Config SU.group (More N); let H: Envelope (fun i:A × B × Extras N=> q (a,i)):= Law.pull (q:=fun i:A × B × Extras N=>(a,i)) hh (measurable_const.prodMk measurable_id) -- tune high
 dsimp only; rw [integral_prod _ (Law.pay H)]; apply integral_congr_ae; apply Eventually.of_forall; intro b
 let L:Envelope (fun i:B× Extras N=> q (a,b,i)):= Law.pull (q:=fun i:B × Extras N=>(b,i)) H (measurable_const.prodMk measurable_id); dsimp only; rw [integral_prod _ (Law.pay L)]; apply integral_congr_ae; apply Eventually.of_forall; intro c; exact integral_prod _ (Law.pay (Law.pull L (q:=fun i:Extras N=>(c,i)) (measurable_const.prodMk measurable_id)))
lemma category : (∫ x, F x ∂globe Y y)=∑ p:Y.Glyph,∑ s:Finset Y.Col,∫ x,F x ∂globeP Y y p s:=by
 letI pa(p:Y.Glyph)(S:Finset Y.Col) : IsProbabilityMeasure (globeP Y y p S):= globe_p Y y p S h -- tune
 unfold globe; rw [integral_finsetSum_measure]; swap; · intro p _; exact Law.pay f
 apply sum_congr rfl; intro p _; rw [integral_finsetSum_measure]; intro s _; exact Law.pay f
end YM.CF.BProof.Payment
