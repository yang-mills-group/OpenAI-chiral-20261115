import YM.CF.Vp929.Borel.Tape
import YM.CF.Vp929.Roof.Bright
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory
open Mesh Lattice Atlas Skye MeasureTheory Cane Spire Scroll SU Cube Lat
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
namespace Aerial
variable (n:Side)
abbrev Pri:=Seat n→ℝ
abbrev Dir:= Seat n→Sweep n
abbrev Frame:=Seat n→SU.E
abbrev Wave:=Seat n→(ℝ× Sweep n)
def μ: Measure (Pri n):=Measure.pi fun _=> pale
def ν: Measure (Dir n):=Measure.pi fun _=> paperMeas (Sweep n)
def valsf: Measure (Frame n):=Measure.pi fun _=> group.probHaar
def valsw: Measure (Wave n):=Measure.pi fun _=> pale.prod (paperMeas _)
instance : IsProbabilityMeasure (μ n):= inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
instance : IsProbabilityMeasure (ν n):= by unfold ν; infer_instance
instance : IsProbabilityMeasure (valsf n):= by unfold valsf; infer_instance
instance : IsProbabilityMeasure (valsw n):= by unfold valsw; infer_instance
abbrev coset (x:Pri n×Dir n)(i: Seat n):= (x.1 i,x.2 i)
abbrev merge (x:Frame n×Wave n)(i: Seat n) : Bone n:= ((x.2 i).1,(x.2 i).2,x.1 i)
lemma cosetM:MeasurePreserving (coset n) ((μ n).prod (ν n)) (valsw n):= loomPair ..
lemma mergeM:MeasurePreserving (merge n) ((valsf n).prod (valsw n)) (depot n):=by
 let f (a: SU.E × (ℝ×Sweep n)): Bone n:= (a.2.1,a.2.2,a.1); have h:= loomPair (I:= Seat n) group.probHaar (pale.prod (paperMeas (Sweep n)))
 let T:=pale.prod (paperMeas (Sweep n)); have t:MeasurePreserving f (group.probHaar.prod T) (parcel n):=(measurePreserving_prodAssoc ..).comp (Measure.measurePreserving_swap (ν:=pale.prod (paperMeas _)))
 exact (measurePreserving_pi (f:=fun _:Seat n=> f) _ _ (fun _=> t)).comp h
-- apply map using outer law param. useful pipeline.
lemma mixedMap{X Y Z A:Type*}[MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z][MeasurableSpace A](μ:Measure X)(ν:Measure Y)(ν':Measure Z)[SFinite ν][SFinite ν'] {f:X×Y→A}{g:X×Z→A}(hf:Measurable f)(hg:Measurable g)(p:∀ x,Measure.map (fun y=> f (x,y)) ν=Measure.map (fun z=>g (x,z)) ν') : (μ.prod ν).map f=(μ.prod ν').map g:=by
 refine Measure.ext fun s hs=>?_ ; rw [Measure.map_apply hf hs,Measure.map_apply hg hs,Measure.prod_apply (hf hs),Measure.prod_apply (hg hs)]; apply lintegral_congr; intro x; have ht:=congrArg (fun M:Measure A=> M s) (p x); exact (Measure.map_apply (hf.comp (measurable_const.prodMk measurable_id)) hs).symm.trans (ht.trans (Measure.map_apply (hg.comp (measurable_const.prodMk measurable_id)) hs))
end Aerial
end YM.CF.VolumeCape.Borel
