import YM.CF.Vp929.Borel.Sample
set_option autoImplicit false
set_option maxHeartbeats 730000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory
open Mesh Lattice Atlas Skye Cane Spire Scroll SU Cube Lat Aerial Sample
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
namespace Sample
variable (n:Side) {I:Type*} [Nonempty I][Fintype I][MeasurableSpace I][MeasurableSingletonClass I][StandardBorelSpace I]
variable (p:Ticket I)(R:Sweep n→Equiv.Perm I)(v:∀s,MeasurePreserving (R s) p.Law p.Law)

abbrev pos (w: Wave n)(i:Seat n):ℝ:=(w i).1
def behold(S:Finset (Seat n))(w:Wave n): ℝ × Sweep n:= w (greet S (pos n w))
def memo (S:Finset (Seat n))(w: Wave n) : I:= R (behold n S w).2 (samp n p S (behold n S w).1)
lemma viewing(S:Finset (Seat n)):Measurable (behold n S):= mealM (F:=fun v:Wave n=> greet S (pos n v)) (fun X=>(mastM _|>.comp (measurable_pi_lambda _ fun k=>measurable_fst.comp (measurable_pi_apply k))) (measurableSet_singleton X)) (G:=fun i x=>x i) (fun i=>measurable_pi_apply i)
lemma glance (S:Finset (Seat n))(u:S.Nonempty)(a b:Wave n)(h:∀i∈ S,a i=b i): behold n S a=behold n S b:=by unfold behold; rw [mastL _ _ (pos n b) (fun i v=> congrArg Prod.fst (h i v)), h _ (mastP _ u _).1]
lemma memoM(S:Finset (Seat n)):Measurable (memo n p R S):=by
 let H:Measurable fun x:I×Sweep n=>R x.2 x.1:= measurable_of_countable _; exact H.comp ((((stint n p S).1.comp (measurable_fst.comp (viewing n S)))).prodMk (measurable_snd.comp (viewing n S)))
lemma pair(S:Finset (Seat n)): MeasurePreserving (behold n S) (valsw n) ((letU n S).prod (paperMeas _)):=by
 let f:=behold n S; let t:=paperMeas (Sweep n); have H(x:Pri n): MeasurePreserving (fun w:Dir n=> w (greet S x)) (ν n) t:= measurePreserving_eval _ _
 have h:Measure.map (f ∘ coset n) ((μ n).prod (ν n))=Measure.map (Prod.map (MinTag n S) (id:Sweep n→ _)) ((μ n).prod t):= by
    apply mixedMap _ _ _ ((viewing n S).comp (cosetM n).1) ((meast n _).prodMap measurable_id)
    intro y; nth_rw 1 [← (H y).2]; rw [Measure.map_map (show Measurable (fun z:Sweep n => (Prod.map (MinTag n S) id (y,z))) from measurable_const.prodMk measurable_id) (H y).1]; rfl
 have e:= cosetM n; refine ⟨viewing n S,?_⟩; change Measure.map f _=_; rw [← e.2,Measure.map_map (viewing n S) e.1, h]; exact ((show MeasurePreserving (MinTag n S) _ _ from ⟨meast n _,(rfl:(μ n).map (MinTag n S)=letU n S)⟩).prod (MeasurePreserving.id t)).2
include v
lemma law(S:Finset (Seat n)): MeasurePreserving (memo n p R S) (valsw n) p.Law:=by
 let t:=paperMeas (Sweep n); let F(a: Sweep n×I):= R a.1 a.2; have ht:MeasurePreserving F (t.prod p.Law) p.Law:= by
    refine ⟨measurable_of_countable _, Eq.trans (mixedMap _ _ _ (show Measurable F from measurable_of_countable _) (show Measurable (Prod.snd : Sweep n×I→I) from measurable_snd) fun x=>?_ ) (show (t.prod p.Law).map _=_ from (measurePreserving_snd (μ:=t)).map_eq)⟩
    have he:= (v x).2; change p.Law.map _ = p.Law.map id; rw [Measure.map_id]; exact he
 let u:= (stint n p S); have hh:= ht.comp (Measure.measurePreserving_swap (μ:=p.Law)); exact hh.comp ((u.prod (MeasurePreserving.id t)).comp (pair n S))
end Sample
end YM.CF.VolumeCape.Borel
