import YM.SU5.Cheer.Cost
import YM.SU5.Cordial.Balloon
/-! # Crisp Momentum sector scaling (Mink units). -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex MeasureTheory Measure Mink Spectral OS OS.Semigroup.Balloon Boundary Probe
open scoped Real Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H : Hilbert} (S:OS.Semigroup H timeAxis)(x:H)(z:ℝ) (p:ℝ≥0)(r:ℝ≥0)
local notation "P"=> S.ℚmeasure
local notation "μ"=> (P).diagonal x
local notation "p↑"=> (p:ℝ)
def zoom (z:ℝ) (x:E4):E4:= z • x
def press (p:ℝ)(s:Set E4):= (zoom p)⁻¹' s
@[fun_prop] lemma eligible(p:ℝ): Continuous (zoom p):=by unfold zoom; fun_prop
lemma pressured{s:Set E4}(h:MeasurableSet s):MeasurableSet (press z s):= h.preimage ((eligible z).measurable)
def outlay : Narrow:= ⟨(μ).map (zoom z),by infer_instance⟩
lemma zoom_room (s:Set E4)(h:MeasurableSet s): ((outlay S x z):Measure E4) s= (μ) ((zoom z) ⁻¹' s) := Measure.map_apply (eligible z |>.measurable) h
lemma radiant (u:0≤z): Brilliant (outlay S x z):=by
 refine (ae_map_iff (eligible z |>.measurable.aemeasurable) ((isClosed_le continuous_const Mink.clock_cont).measurableSet)).mpr ?_
 filter_upwards [S.bright x] with i t; rw [zoom,clock_mul]; exact mul_nonneg u t
def shore (v:Space3): Cross timeAxis:= ⟨position v 0,time_position _ _⟩
private lemma shoreT(v:Space3): time (shore v).val=0:=(shore v).2
private lemma coastR (v:Space3)(p:E4): inner ℝ p (shore v).val=inner ℝ (spatial p) v:= by rw [pairing,shoreT, mul_zero, add_zero, show spatial (shore v).val=v from spatial_position ..]
-- Floor with discount
private lemma zoom_cash (p₀:E4)(v:Space3): tendsK v ((r:ℝ):ℂ) (zoom p↑ p₀) = plane p₀ (((p↑ • shore v : Cross timeAxis)): E4) * ↑(tinct timeAxis (p*r) p₀):=by
 unfold tendsK plane tinct zoom; rw [Submodule.coe_smul_of_tower, Mink.rest_mul,Mink.clock_mul,real_inner_smul_left,real_inner_smul_right,coastR,Complex.ofReal_exp,← Complex.exp_add]; push_cast; unfold time; ring_nf -- tune
lemma back (v:Space3) : FLap (outlay S x p↑) v ↑(r:ℝ) = inner ℂ x (S.U (p↑ • shore v) (S.E (p*r) x)):= by
 rw [FLap,during]
 refine (integral_map (eligible p↑|>.measurable.aemeasurable) (?_ : AEStronglyMeasurable (tendsK v ((r:ℝ):ℂ)) ((μ).map (zoom p↑)))).trans (integral_congr_ae (ae_of_all _ (fun i=>zoom_cash ..)))
 exact (airy v _).aestronglyMeasurable
lemma slogan (b:E4): inner ℂ x (S.unit.translation (zoom z b) x)=charFun ((outlay S x z):Measure E4) b:= by
 rw [← S.joint,charFun_apply,charFun_apply]; symm; change (∫ y:E4, plane y b ∂(μ).map (zoom z)) = _
 refine (integral_map (eligible z|>.measurable.aemeasurable) ?_).trans ?_
 · exact (show Continuous (fun y:E4=>plane y b) by unfold plane; fun_prop).aestronglyMeasurable
 apply integral_congr_ae (ae_of_all _ fun y=>?_); unfold plane zoom; rw [real_inner_smul_left,real_inner_smul_right]
lemma zoom_inside {z:ℝ}(h:0<z) : (zoom z) ⁻¹' inside= inside:= by ext v; change ‖_‖< _ ↔ ‖_‖<_; rw [zoom,Mink.rest_mul, Mink.clock_mul,norm_smul,Real.norm_of_nonneg h.le,mul_lt_mul_iff_right₀ h] -- ambiguity
lemma norm_region (s:Set E4)(h : MeasurableSet s): ‖(P).region (press z s) x‖^2 = ((outlay S x z):Measure E4).real s:= ((P).same (pressured z h) x).symm.trans (congrArg (fun e:ℝ≥0∞=>e.toReal) (zoom_room S x z s h).symm)
variable{z}
lemma outside (u: 0<z): ‖(P).region insideᶜ x‖^2=((outlay S x z):Measure E4).real insideᶜ:=by
 rw [← norm_region S x z (insideᶜ) open_inside.isClosed_compl.measurableSet, press, preimage_compl,zoom_inside u]
lemma orth_inside : (P).region inside x + (P).region insideᶜ x = x:= by
 -- simple squared normals of complement
 let y:=(P).region inside x; let v:=(P).region insideᶜ x; let ν:=(P).diagonal x; let q:= open_inside.measurableSet; let k:= q.compl
 have he: ‖x‖^2= ‖y‖^2+‖v‖^2:=by rw [← real_univ S x,← (P).same q x,← (P).same k x]; exact (measureReal_add_measureReal_compl q).symm -- y unfolding
 have hx:inner ℂ y v=0:=by
    unfold y v; nth_rw 1 [← (P).real q]; rw [ContinuousLinearMap.adjoint_inner_left,←ContinuousLinearMap.comp_apply,(P).joins q k,inter_compl_self,(P).none,ContinuousLinearMap.zero_apply,inner_zero_right]
 have hy:(inner ℂ x y).re= ‖y‖^2:= ((congrArg Complex.re ((P).at_pair q x).symm).trans ((P).same q x)); have hv:(inner ℂ x v).re=‖v‖^2:= (congrArg Complex.re ((P).at_pair k x).symm).trans ((P).same k x)
 have ht:‖x-(y+v)‖^2=0:=by rw [norm_sub_sq (𝕜:=ℂ), norm_add_sq (𝕜:=ℂ), hx,inner_add_right]; change _ - 2*(inner ℂ x y + inner ℂ x v).re + (‖y‖^2 +2*(0:ℂ).re + ‖v‖^2)=_; rw [he, add_re,hy,hv,Complex.zero_re]; ring
 exact (sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero ht))).symm
end YM.Cheer
#print axioms YM.Cheer.back
#print axioms YM.Cheer.orth_inside
#print axioms YM.Cheer.outside
