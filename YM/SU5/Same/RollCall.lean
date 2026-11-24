import YM.SU5.Same.EnergySheet
/-! # Fourier test of the vacuum vectors -- no further smoothing.
    (helper arithmetic)
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe Complex
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical
open Multiplier Roy SNAG
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert} {a:Axis}(S:OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "θ" => S.ℚmeasure.diagonal

abbrev onward : Test4 →L[ℂ] Test4 := ((pref E4):ℂ) • port
-- ∫ e^{ipx}  f(x) , full radian convention
lemma onward_cost (f:Test4)(x:E4): onward f x =∫ y,plane x y * f y:=by
 change ((pref E4):ℂ)* port f x=_; rw [port_eq]; rw [Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,mul_inv_cancel₀ prepos.ne',Complex.ofReal_one,one_mul]; apply integral_congr_ae; filter_upwards with y; rw [plane_dot y]
lemma cut_onward (f:Test4): SNAG.cut (onward f) = f:= by
 change ((normer E4):ℂ) • hat _=_; rw [show onward f= ((pref E4):ℂ) • port f from rfl,map_smul,travels,smul_smul,←Complex.ofReal_mul,inv_mul_cancel₀ prepos.ne',Complex.ofReal_one,one_smul]
lemma onward_cut (f:Test4): onward (SNAG.cut f)=f:= by
 rw [show SNAG.cut f=((normer E4):ℂ) • hat f from rfl,map_smul, show onward (hat f)= ((pref E4):ℂ) • port (hat f) from rfl,Probe.comes,smul_smul,←Complex.ofReal_mul,inv_mul_cancel₀ prepos.ne',Complex.ofReal_one,one_smul]
abbrev planks (b:E4) : H.Op := S.unit.translation b
lemma roll_tag (f:Test4):Tag (f:E4→ℂ):= ⟨f.continuous.measurable, SchwartzMap.seminorm ℝ 0 0 f, apply_nonneg .., f.norm_le_seminorm ℝ⟩

-- can exchange finite measure and our full Test4. includes width measure(s) esp diagonal
lemma flight_ledger {μ:Measure E4}[IsFiniteMeasure μ](f: Test4) :
    Integrable (Function.uncurry (fun b p:E4=> f b * plane p b)) (volume.prod μ):=by
 let F:= Function.uncurry (fun b p:E4=> f b * plane p b); let g:= (f.integrable (μ:=volume)).norm
 have h : Integrable (fun b:E4×E4=> ‖f b.1‖ * (fun p:E4=> (1:ℝ)) b.2) (volume.prod μ):= g.mul_prod (integrable_const _)
 apply h.mono' (μ:=volume.prod μ) (Continuous.aestronglyMeasurable (f.continuous.comp continuous_fst|>.mul (plane_cont.comp (Homeomorph.prodComm ..|>.continuous))))
 exact ae_of_all _ fun x=> show ‖F x‖ ≤ ‖f x.1‖*1 from by simp [F,uncurry]

lemma rolls_member (f:Test4): Registers S.ℚmeasure (f:E4→ℂ) (listen S.unit f):=by
 refine ⟨roll_tag f,fun x=>?_⟩; let g:= SNAG.cut f; let ν:=S.ℚmeasure.diagonal x
 let v (b p:E4) := g b * plane p b
 change inner ℂ x (∫ b:E4, g b • S.unit.translation b x)=_
 rw [← integral_inner (SNAG.over S.unit f x)]
 have he(b:E4): inner ℂ x (g b • S.unit.translation b x)=∫ p,v b p ∂ν:=by
    unfold v; rw [integral_const_mul, inner_smul_right]; exact congrArg (g b*·) ((Picket.story S _).awakes x)
 change (∫ b:E4, inner ℂ x (g b • S.unit.translation b x))=(∫ p:E4,f p ∂ν); simp_rw [he]; have hv: Integrable (Function.uncurry v) (volume.prod ν):= flight_ledger g
 rw [integral_integral_swap hv]; refine integral_congr_ae (ae_of_all _ (fun p=> ?_))
 apply Eq.trans ?_ (SNAG.light f p)
 exact integral_congr_ae (ae_of_all _ (fun x=> mul_comm ..))

abbrev collect (f:Test4) : H.Op:= SNAG.send S.unit (onward f)
lemma collect_member (f:Test4): Registers S.ℚmeasure (onward f:E4→ℂ) (collect S f):= rolls_member S _
lemma collect_eq (f:Test4)(x:H) : collect S f x= ∫ b, f b • S.unit.translation b x := by unfold collect; rw [SNAG.sending,cut_onward]
lemma collect_int (f:Test4)(x:H): Integrable (fun b:E4=> f b • S.unit.translation b x):=by nth_rw 1 [← cut_onward f]; exact SNAG.over S.unit (onward f) x
lemma dayShift (f:Test4)(t:E4)(x:H): planks S t (collect S f x)= collect S (ahead t f) x:=by
 rw [collect_eq,collect_eq,←ContinuousLinearMap.integral_comp_comm (planks S t) (collect_int S f x), ←integral_add_left_eq_self (fun b:E4=> ahead t f b • S.unit.translation b x) t]; apply integral_congr_ae; filter_upwards with b
 rw [map_smul, ahead_at, add_sub_cancel_left]; exact congrArg (f b • ·) (DFunLike.congr_fun (S.unit.sends t b) x)
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms rolls_member
