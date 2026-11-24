import GaugeFieldConstruction.Avast
import GaugeFieldConstruction.Arras
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One
open scoped Topology ContDiff BigOperators
variable (t:ℝ)
abbrev Sr (n:ℕ)(x:E4)(f:SmoothGap):Prop:=(t:ℂ)^n * eye (t • x) f=eye x f
abbrev Sold (n:ℕ)(f:SmoothGap):Prop:=∀ x,Sr t n x f
variable {t} (v:0<t)
include v
lemma stoneS : Sold t 2 stone:=by
 intro x; by_cases h:x=0; · change _*stone.val _=stone.val _; rw [h]; simp
 unfold Sr; have ht:t • x≠0:=smul_ne_zero v.ne' h; rw [show eye x stone=_ from lap Green (fun _ p=> freeSmooth p) h,show eye _ stone=_ from lap Green (fun _ p=> freeSmooth p) ht]; unfold Green; rw [norm_smul,Real.norm_of_nonneg v.le]; norm_cast; field_simp -- tune
lemma riseS {p:SmoothGap}{n:ℕ}(h:Sold t n p)(i):Sold t (n+1) (Gap.step i p):=by
 intro x; unfold Sr; by_cases e:x=0; · change _*(step i p).val _=(step i p).val _; rw [e]; simp
 let L:= t • ContinuousLinearMap.id ℝ E4; have hx:t • x≠0:= smul_ne_zero v.ne' e
 have hr : grad i (((t:ℂ)^n) • (p.val ∘ L)) x=grad i p.val x:=congrArg (fun f=>grad i f x) (funext h)
 unfold YM.Maxwell.grad Analysis.D at hr; let P:= (Gap.healthy p (x:= L x) hx).differentiableAt (by simp); rw [fderiv_const_smul (P.comp x L.differentiableAt),fderiv_comp x P L.differentiableAt,L.fderiv, ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply] at hr; change ((t:ℂ)^n) * fderiv ℝ p.val (t • x) (t • basis i) = _ at hr; rw [map_smul (fderiv ..),Complex.real_smul] at hr
 change _ *(Gap.step i p).val _=(Gap.step i p).val _; rw [flash _ _ hx,flash _ _ e]; unfold YM.Maxwell.grad Analysis.D; rw [←hr,pow_succ,mul_assoc]
omit v
lemma scale_Z (i:ℂ){p}{n:ℕ}(h:Sold t n p): Sold t n (i • p):=fun x=>by unfold Sr; rw [map_smul,map_smul,smul_eq_mul,mul_left_comm,h,smul_eq_mul]
lemma scale_sub {p q}{n:ℕ}(h:Sold t n p)(w:Sold t n q): Sold t n (p-q):=fun x=>by unfold Sr; rw [map_sub,map_sub,mul_sub,h,w]
lemma Sold0 (n): Sold t n 0:=fun x=>by unfold Sr; simp
include v
lemma Scarf (a b c d:Axis): Sold t 4 (curl a b c d):=by
 let f i j:=Gap.step i (Gap.step j stone); have h (i j):Sold t 4 (f i j):=riseS v (riseS v (stoneS v) j) i
 rw [Raster.curlwork a b c d f fun i j=>by simp [Raster.word,f]]; split_ifs <;>apply scale_sub<;> apply scale_sub <;> first|apply Sold0|apply h -- tune
lemma Foulard(i j:Cauchy.Spin): Sold t 3 (blend i j):=by
 intro x; unfold Sr; rw [blend,map_sum,map_sum, Finset.mul_sum]; exact sum_congr rfl fun a _=> scale_Z _ (riseS v (stoneS v) a) x -- order implicit
-- Field primitive symbol unlabelled
open Lattice
abbrev debtG (r:PlaqAxes)(a:Phys.Pig):= sectionG a r.val.1 r.val.2
abbrev debtF (i:Cauchy.Spin)(s:Matter.Slot):=sessionF s i
omit v
lemma inlet(a b:PlaqAxes)(i j:Pig):ge (debtG a i) (debtG b j)= if i=j then curl a.val.1 a.val.2 b.val.1 b.val.2 else 0:=by
 unfold ge debtG sectionG; rw [matchU]; split_ifs
 · rw [unroll,ends,ends]; simp
 rfl
lemma portF (i j:Cauchy.Spin)(x y:Matter.Slot)(d:Bool): yarn d (debtF i x) (debtF j y)=if x=y then thread d i j else 0:=by
 unfold yarn debtF sessionF; rw [matchU]; split_ifs; · rw [psD,ends,ends]; simp
 rfl
-- HopeC eq
open HopeC
lemma eq_H {X:Type*}[TopologicalSpace X][MeasurableSpace X] (p q:HopeC X) (u:p.μ=q.μ)(h:p.site=q.site): p=q:=by cases p; cases q; congr
lemma transmit (p:HopeC E4)(f g:E4→E4)(h: Continuous f)(c:Continuous g): HopeC.lift (HopeC.lift p g c) f h=HopeC.lift p (f∘g) (h.comp c):= eq_H _ _ (Measure.map_map h.measurable c.measurable) (Set.image_image ..)
lemma parallel (x:E4)(H:HopeC E4): addQ (point x) H= HopeC.lift H (x+·) (by fun_prop) := by
 apply eq_H
 · change Measure.map (fun p:E4×E4=>p.1+p.2) ((Measure.dirac x).prod H.μ)=_; rw [Measure.dirac_prod,Measure.map_map] <;> first|rfl|fun_prop
 change ((fun p:E4×E4=>p.1+p.2) '' ({x}×ˢ H.site)) = _; ext p; change _ ↔ p ∈ (fun y=>x+y) '' H.site; simp
lemma boatQ (p q:HopeC E4)(f g:E4→E4)(h:Continuous f)(c:Continuous g):
 pairs (HopeC.lift p f h) (HopeC.lift q g c)=HopeC.lift (pairs p q) (Prod.map f g) (h.prodMap c):= eq_H _ _ (Measure.map_prod_map p.μ q.μ h.measurable c.measurable) (Set.prod_image_image_eq ..) -- tune
variable (H G:HopeC E4)
lemma trodQ (p:HopeC (E4×E4))(f:E4×E4→E4×E4)(c:Continuous f)(g:E4×E4→E4)(h:Continuous g): HopeC.lift (HopeC.lift p f c) g h=HopeC.lift p (g∘f) (h.comp c):= eq_H _ _ (Measure.map_map h.measurable c.measurable) (Set.image_image ..)
lemma commuted (f g:E4→E4)(h: Continuous f)(c:Continuous g): Ferry (HopeC.lift H f h) (HopeC.lift G g c) = HopeC.lift (pairs H G) (fun x=>-(f x.1)+g x.2) (by fun_prop):=by
 unfold Ferry HopeC.rev; rw [transmit]; unfold addQ; rw [boatQ,trodQ]; rfl
end YM.GaugeFieldConstruction.Wick.Yacht
end
