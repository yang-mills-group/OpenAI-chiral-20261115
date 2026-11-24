import GaugeFieldConstruction.Eddies
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One
open scoped Topology ContDiff BigOperators
open HopeC
-- translation payment glue. `z=ordered actual cover origins`. t is invR, c pitch
variable (H G:HopeC E4)(i j x y:E4)(c t:ℝ)
abbrev billMark (x i:E4)(c:ℝ)(a:E4):E4:=c • (i+a)-x
def diagram (x i:E4)(c:ℝ):HopeC E4:= HopeC.lift H (billMark x i c) (by unfold billMark; fun_prop)
-- i,j primitive stencil origins actual in measures
lemma drill (p: SmoothGap)(n:ℕ)(w:Sold t n p)(M:Set E4)(m:0∉ M)(f: PathsZ (diagram H x i c) (diagram G y j c) M (t • (y-x)) t)(r: 0≤t): let A:=diagram H x i c; let B:=diagram G y j c; let P:=Ferry (addQ (point i) H) (addQ (point j) G); 0∉P.site ∧ (∫ u, eye (c • u) p∂P.μ)=(t:ℂ)^n*(∫ v:E4×E4, eye (t • (y-x)+t • (v.2-v.1)) p∂(pairs A B).μ):=by
 intro A B P; let R(a:E4)(x:E4):=a+x; let J(v:E4×E4):=-(R i v.1)+R j v.2; have he:Continuous J:=by unfold J R; fun_prop
 have hp:P=HopeC.lift (pairs H G) J he:=by unfold P; rw [parallel,parallel]; apply commuted -- tune
 let T:=Prod.map (billMark x i c) (billMark y j c); have ht:Continuous T:=by unfold T billMark; fun_prop
 have hv:pairs A B=HopeC.lift (pairs H G) T ht:=boatQ ..
 let V(v:E4×E4):= t • (y-x)+t • (v.2-v.1); have I(u:E4×E4): V (T u)=t • (c • J u):=by
    change t • (y-x)+t • ( (c •(j+u.2)-y)-(c •(i+u.1)-x)) = _; rw [← smul_add]; unfold J R; module
 have hi (l)(e:l∈(pairs A B).site): V l≠0:=fun h=> m (h ▸ (f l.1 e.1 l.2 e.2 t ⟨r,le_rfl⟩))
 have hj(l)(q:l∈ P.site): c • l≠0:=by
    rw [hp] at q; obtain ⟨y,g,e⟩:=q; rw [← e]; intro Z; apply hi (T y) (by rw [hv]; exact Set.mem_image_of_mem T g); rw [I y,Z,smul_zero]
 refine ⟨fun p=> hj 0 p (smul_zero c),?_⟩; rw [hp, hv]; rw [rolled,rolled,← integral_const_mul]; · exact integral_congr_ae (Eventually.of_forall fun u=> by change eye _ _=(t:ℂ)^n * eye (V (T u)) p; rw [I,w])
 · refine fun z e=> ((healthy p (hi z (by rw [hv]; exact e))).continuousAt.comp (f:=V) ?_).continuousWithinAt; unfold V; fun_prop
 exact fun z e=> ((healthy p (hj z (by rw [hp]; exact e))).continuousAt.comp (f:=fun v=>c • v) (by fun_prop)).continuousWithinAt
end YM.GaugeFieldConstruction.Wick.Yacht
end
