/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Souk.Home
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open YM.Push.Loops (det_contDiff det_variation logdet_variation inv_contDiffAt inv_variation traceFee)
lemma mixed_L [DecidableEq ι] {X : E → Matrix ι ι ℝ} {x : E} (hx : ContDiffAt ℝ 2 X x) (hu : IsUnit (X x).det)
    (v w : E) : iteratedFDeriv ℝ 2 (fun y => Real.log (X y).det) x ![v,w] =
      traceFee (X x) (fderiv ℝ X x v) (fderiv ℝ X x w) (iteratedFDeriv ℝ 2 X x ![v,w]) := by
  let Y y := Real.log (X y).det
  let M := X x
  let T := fun x => (X x)⁻¹
  let P := fun x => fderiv ℝ X x w
  have h : (fun y => fderiv ℝ Y y w) =ᶠ[𝓝 x] fun y => (T y * P y).trace := by
    have he := ((det_contDiff.of_le le_top).contDiffAt.comp x hx).continuousAt.eventually (isOpen_ne.mem_nhds hu.ne_zero)
    filter_upwards [he,hx.eventually (by norm_num)] with y hy hg
    exact logdet_variation (hg.differentiableAt (by norm_num)) (isUnit_iff_ne_zero.mpr hy) w
  have ht := ((inv_contDiffAt _ hu).differentiableAt (by norm_num)).hasFDerivAt.comp x
    (hx.differentiableAt (by norm_num)).hasFDerivAt
  have hp := ((hx.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  let τ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have hh := τ.hasFDerivAt.comp x (ht.mul' hp)
  have H : fderiv ℝ (fun y => (T y * P y).trace) x = _ := hh.fderiv
  have hd := ((((show ContDiffAt ℝ 2 Y x from (((det_contDiff.of_le le_top).contDiffAt).comp x hx).log hu.ne_zero)).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ Y) x v w = _
  rw [show fderiv ℝ (fderiv ℝ Y) x v w = fderiv ℝ (fun y => fderiv ℝ Y y w) x v by rw [show _ = _ from hd.fderiv]; simp [Y],
    h.fderiv_eq, H]
  simp only [ContinuousLinearMap.comp_zero, zero_add, Function.comp_apply, ContinuousLinearMap.comp_apply,
    _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.flip_apply, traceFee, iteratedFDeriv_two_apply]
  erw [inv_variation _ hu]
  change (_ + -(M⁻¹ * _ * M⁻¹) * _).trace = _
  rw [neg_mul, trace_add, trace_neg]
  rfl

variable {X:Fish ι→Neige.Shelf τ}{x:Fish ι}
lemma Jewel.logM(h:Jewel X x C Q)(hp:C ≤ 1/2)(i:ℕ)(hi:i<2)(j:Fin (i+1)→ι):
 let f(y):=1+X y
 let y:=fun x=>Real.log (f x).det
 IsUnit (f x).det ∧ ContDiffAt ℝ 2 y x ∧ |Uniform.entry y x j| ≤ 6*Q:=by
 intro f y; have hv : ‖paintO (τ:=τ) (f x-1)‖≤1/2:=by rw [show f x-1=X x from by unfold f; abel]; exact h.upper.value.trans hp
 have ht : ‖paintO (τ:=τ) ((f x).transpose-1)‖ ≤ 1/2:=by rw [show (f x).transpose-1=(X x).transpose from by unfold f; rw [transpose_add,transpose_one]; abel]; exact h.turn.value.trans hp
 have hX:ContDiffAt ℝ 2 X x:=by simpa using steep h.upper
 have hf:ContDiffAt ℝ 2 f x:=contDiffAt_const.add hX
 obtain ⟨hK,hu⟩:= low_invP _ hv; have ht': ‖paintO (τ:=τ) ((f x)⁻¹).transpose‖ ≤ 2:=by rw [Matrix.transpose_nonsing_inv]; exact (low_invP _ ht).2 -- tune
 refine ⟨hK,(((det_contDiff.of_le le_top).contDiffAt).comp x hf).log hK.ne_zero,?_⟩
 have hs:0 ≤ Q:= (notes_nn _).trans (h.cents i hi j)
 have he(m:ℕ)(hm:m<2)(v:Fin (m+1)→ι): pS (m+1) f v x=pS (m+1) X v x:=by
    unfold pS Uniform.entry f; erw [iteratedFDeriv_add_apply contDiffAt_const (steep (h.upper.order (show m+1 ≤ 2 from by omega)))]; erw [iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,zero_add]
 interval_cases i
 · unfold Uniform.entry; rw [iteratedFDeriv_one_apply,show y=(fun y=>Real.log (f y).det) from rfl,logdet_variation (hf.differentiableAt (by norm_num)) hK]; rw [show fderiv ℝ f _ _= pS 1 X j x from ?_]; apply (fee_abs _).trans; exact (buy_mul ht' (h.cents 0 (by decide) j)).trans (by linarith only [hs]); rw [← he 0 (by decide) j]; unfold pS Uniform.entry; rw [iteratedFDeriv_one_apply]; rfl
 unfold Uniform.entry; change |iteratedFDeriv ℝ 2 _ x _| ≤ _; let a:=j 0; let b:=j 1; let v:=bolt a; let w:=bolt b; have hh: (fun k=> Uniform.bolt (j k))=![v,w]:= by ext1 k; fin_cases k <;>rfl
 unfold y; rw [hh,mixed_L hf hK,traceFee]; apply (abs_sub ..).trans -- tune
 have h₁ : fderiv ℝ f x v=pS 1 X ![a] x:=by rw [←he 0 (by decide) ![a]]; unfold pS Uniform.entry; rw [iteratedFDeriv_one_apply]; rfl
 have h₂ : fderiv ℝ f x w=pS 1 X ![b] x:=by rw [←he 0 (by decide) ![b]]; unfold pS Uniform.entry; rw [iteratedFDeriv_one_apply]; rfl
 rw [h₁,h₂,← hh,show iteratedFDeriv ℝ 2 f x _= _ from he 1 (by decide) j]; refine (add_le_add ((fee_abs _).trans (buy_mul ht' (h.cents 1 (by decide) j))) ((fee_abs _).trans (pay_mul (pay_mul (buy_mul ht' (h.cents 0 (by decide) ![a])) hu) ((scaleS (i:=1) h.upper (by decide) ![b]).trans hp)))).trans (by linarith only [hs])
end YM.CF.Souk
