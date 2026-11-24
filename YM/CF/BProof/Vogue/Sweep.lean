import YM.CF.BProof.Vogue.Bean
import YM.CF.Skye.Pine
-- joint frame and component packet: sweep picked at minimum location. real tags may
-- be consumed nonlocal within component.
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter Set MeasureTheory ProbabilityTheory Skye Spire Lattice -- Sweep
open scoped Topology BigOperators NNReal ENNReal Classical
variable {I J K:Type*}[Fintype I] {n:Side}
private lemma rowgem {X Y Z:Type*}[MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z]
    (μ:Measure X)(ν:Measure Y)(π:Measure Z)[SFinite μ][SFinite ν][SFinite π](f:X→Y→Z)(u:Measurable (uncurry f))(p:∀ i, MeasurePreserving (f i) ν π): MeasurePreserving (fun x:X×Y=>(x.1,f x.1 x.2)) (μ.prod ν) (μ.prod π):=by
 let F(x:X×Y):=(x.1,f x.1 x.2); have hg:Measurable F:= measurable_fst.prodMk u
 refine ⟨hg,Measure.ext fun s hs=>?_⟩; rw [Measure.map_apply hg hs,Measure.prod_apply (hg hs),Measure.prod_apply hs]; apply lintegral_congr; intro x; exact (p x).measure_preimage (show NullMeasurableSet ((Prod.mk x) ⁻¹' s) π from (measurable_prodMk_left hs).nullMeasurableSet) -- name?
abbrev Root (n:Side) := Seat n→ SU.E
abbrev Halo (n:Side) := Seat n→ℝ
abbrev Spin (n:Side) := Seat n→Sweep n
abbrev haloM(n:Side):Measure (Halo n):=Measure.pi fun _:Seat n=> pale
abbrev rootM(n:Side):Measure (Root n):=Measure.pi fun _:Seat n=> SU.group.probHaar
def entries {n}(x:Ids n):Spin n:=fun i=>(x i).2.1
abbrev spinM(n:Side) (I:Type*)[Fintype I]:Measure (I→Sweep n):=Measure.pi fun _=>paperMeas (Sweep n)
lemma icicle (n:Side):MeasurePreserving (fun x:Ids n=>((priorP x,entries x),frameP x)) (depot n) (( (haloM n).prod (spinM n (Seat n))).prod (rootM n)):=by
 let μ:= paperMeas (Sweep n); let B:= SU.group.probHaar
 haveI : IsProbabilityMeasure μ:=by unfold μ; infer_instance
 have ht:= measurePreserving_arrowProdEquivProdArrow _ _ (Seat n) (fun _=> μ) (fun _=> SU.group.probHaar); have hp:=measurePreserving_arrowProdEquivProdArrow _ _ (Seat n) (fun _=>pale) (fun _=> μ.prod SU.group.probHaar)
 exact ((measurePreserving_prodAssoc (haloM n) (spinM n (Seat n)) (rootM n)).symm).comp (((MeasurePreserving.id (haloM n)).prod ht).comp hp)

lemma seek {α β γ:Type*}[MeasurableSpace α][Countable β][MeasurableSpace β][MeasurableSingletonClass β][MeasurableSpace γ] (f:α→β)(h:Measurable f)(F:α→β→γ)(g:Measurable F): Measurable fun x=>F x (f x):= Skye.mealM (F:=f) (fun i=>h (measurableSet_singleton _)) (fun i=>(measurable_pi_apply i).comp g)

variable (S:I→ Finset (Seat n))(g:∀ i,(S i).Nonempty)(p:Pairwise (Disjoint on S))
def petals (x:Halo n)(y:Spin n)(i:I): Sweep n:= y (greet (S i) x)
lemma petals_c: Measurable (Function.uncurry (petals S)):=by
 apply measurable_pi_lambda; intro i; exact seek _ ((mastM (S i)).comp measurable_fst) (fun x:Halo n × Spin n=>x.2) measurable_snd
variable [Fintype K][Nonempty K][MeasurableSpace K][MeasurableSingletonClass K]
local instance nZ (L:Type*)[Fintype L][Nonempty L] : NeZero (Fintype.card L):= ⟨Fintype.card_pos.ne'⟩ -- defeq default.Fin instance caution `Fintype.equivFin` classical DecEq.
def Taste(K:Type*)[Fintype K][Nonempty K](S:Finset J)(x:J→ℝ):K:= (Fintype.equivFin K).symm (∑ i∈S,pitch (Fintype.card K) (x i)) -- could use custom MVP
lemma taste_c {K:Type*}[Fintype K][Nonempty K][MeasurableSpace K](S:Finset J) : Measurable (Taste K S):= by
 unfold Taste; apply (measurable_of_countable ((Fintype.equivFin K).symm)).comp; exact Finset.measurable_sum _ fun i _=> (pitch_p _).measurable.comp (measurable_pi_apply i) -- tune
lemma tasteP(K:Type*)[Fintype K][Nonempty K][MeasurableSpace K][MeasurableSingletonClass K]:Measurable (fun t:Ids n=> fun i=> Taste K (S i) (priorP t)):=by apply measurable_pi_lambda; intro i; exact (taste_c _).comp primeV

include p g
lemma pill :MeasurePreserving (uncurry (fun x:Halo n=>fun y:Spin n=> ((fun i=> Taste K (S i) x), petals S x y))) ((haloM n).prod (spinM n (Seat n))) ((Measure.pi fun _:I=>paperMeas K).prod (spinM n I)):=by
 have he(i:Halo n): MeasurePreserving (petals S i) (spinM n (Seat n)) (spinM n I):=coupon (J:=Seat n) (Sweep n) (fun j=> greet (S j) i) (fun j k eq=> by_contra fun v=> Finset.disjoint_left.mp (p v) (mastP _ (g j) i).1 ((show greet (S j) i = greet (S k) i from eq).symm ▸ (mastP _ (g k) i).1))
 let e:= (Fintype.equivFin K).symm; have hv:MeasurePreserving (fun x:I→Fin (Fintype.card K) => e ∘ x) (Measure.pi fun _=>paperMeas (Fin (Fintype.card K))) (Measure.pi fun _:I=>paperMeas K):= measurePreserving_pi _ _ (f:=fun _=>e) (fun _=>orderMP e) -- e coerces
 exact ((hv.comp (beans_exp (Fintype.card K) S g p)).prod (MeasurePreserving.id _)).comp (rowgem (haloM n) (spinM n (Seat n)) _ _ (petals_c S) he)
lemma value_p : MeasurePreserving (fun x:Ids n=>(((fun i=> Taste K (S i) (priorP x)), (petals S (priorP x) (entries x))), frameP x)) (depot n) (((Measure.pi fun _:I=>paperMeas K).prod (spinM n I)).prod (rootM n)):= ((pill S g p).prod (MeasurePreserving.id _)).comp (icicle n)
end YM.CF.BProof.Vogue
