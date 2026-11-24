import GaugeFieldConstruction.Zerofoil
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators
open GaussianFourier Maxwell Analysis
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
abbrev dotbill (p:E4)(w:List Axis):ℂ:= (w.map (fun i=>I*(p i:ℂ))).prod
lemma stip (p:E4)(w:List Axis): ‖dotbill p w‖ ≤ ‖p‖^w.length:=by induction w with
 | nil=> simp [dotbill]
 | cons i v ih=> unfold dotbill; rw [List.map_cons,List.prod_cons,norm_mul,norm_mul,Complex.norm_real,Complex.norm_I,one_mul,List.length_cons,pow_succ']; exact mul_le_mul (PiLp.norm_apply_le ..) ih (norm_nonneg _) (norm_nonneg _)
variable (w:List Axis) (t:ℝ)
abbrev kip (p:E4):ℂ:= dotbill p w*(Hη t p:ℂ)
lemma kip_int (h:0<t)(u:w.length≤2):Integrable (kip w t) volume:=by
 have he:Continuous fun p:E4=> dotbill p w:=by
    induction w with
    | nil => exact continuous_const
    | cons i v ih=> change Continuous (fun p:E4=>I*↑(p i)*dotbill p v); refine Continuous.mul (by fun_prop) (ih (by rw [List.length_cons] at u; omega))
 apply ((heat_known _ h).1.add (Hη_int h)).mono' (f:=kip w t) (by unfold kip Hη veil; exact (he.measurable.mul (by fun_prop)).aestronglyMeasurable)
 filter_upwards [NZφ] with p v; let z:=Hη t p; have hp:0<‖p‖:=norm_pos_iff.mpr v; have hh: 0<z:=div_pos (Real.exp_pos _) (pow_pos hp 2)
 rw [kip,norm_mul,Complex.norm_real,Real.norm_of_nonneg hh.le]; change _*z≤ veil t p+ z; rcases le_total 1 ‖p‖ with e|e
 · apply ((mul_le_mul_of_nonneg_right ((stip p w).trans (pow_le_pow_right₀ e u)) hh.le).trans_eq (mul_div_cancel₀ _ (pow_pos hp 2).ne')).trans; exact le_add_of_nonneg_right hh.le -- tune
 exact (mul_le_of_le_one_left hh.le ((stip p w).trans (pow_le_one₀ hp.le e))).trans (le_add_of_nonneg_left (Real.exp_pos _|>.le))
abbrev retK (x:E4):ℂ:= (πnorm:ℂ)*(∫ p:E4, rider x p * kip w t p)
lemma insideK (h:0<t)(u:w.length≤2)(x:E4): Integrable (fun p:E4=>rider x p * kip w t p) volume:= ((kip_int w t h u).bdd_mul (by unfold rider; fun_prop) (Eventually.of_forall fun p=> (unitR x p).le)) -- check
lemma cell_t (h:0<t){x:E4}(v:x≠0): retK [] t x=(Woof x t:ℂ):=by unfold retK kip dotbill; simp only [List.map_nil,List.prod_nil,one_mul]; rw [hedge h,← Complex.ofReal_mul,Woof_K h _ v]
abbrev jog (x:E4)(a:Axis)(s:ℝ):= x+s • basis a
lemma jog_price (x p:E4)(a:Axis)(s:ℝ): HasDerivAt (fun s=> rider (jog x a s) p) (I*↑(p a)*rider (jog x a s) p) s:=by
 have he: HasDerivAt (fun z=>inner ℝ (jog x a z) p) (p a) s:=by
    have ht:= ((hasDerivAt_id' s).smul_const (basis a)).const_add x
    have hw:= ht.inner ℝ (hasDerivAt_const s p)
    simpa [jog] using hw
 unfold rider
 convert! ((he.ofReal_comp.const_mul I).cexp) using 1; dsimp; ring -- tune
lemma segment_T (h:0<t)(a:Axis)(u:(a::w).length ≤ 2) (x:E4)(s:ℝ): HasDerivAt (retK w t ∘ jog x a) (retK (a::w) t (jog x a s)) s:=by
 let J(v:List Axis)(x:E4)(p:E4):ℂ:= rider x p * kip v t p
 have he(p:E4)(s:ℝ): HasDerivAt (fun z=> J w (jog x a z) p) (J (a::w) (jog x a s) p) s:=by
    have ht:=(jog_price x p a s).mul_const (kip w t p); apply ht.congr_deriv; unfold J kip dotbill; simp only [List.map_cons,List.prod_cons]; ring
 have h'(z:ℝ):=insideK w t h (by rw [List.length_cons] at u; omega) (jog x a z)
 exact ((hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun z p=>J w (jog x a z) p) (F':=fun z p=>J (a::w) (jog x a z) p) (x₀:=s) univ_mem (Eventually.of_forall fun i=>(h' i).aestronglyMeasurable) (h' _) ((insideK _ t h u _).aestronglyMeasurable) (bound:=fun p=> ‖kip (a::w) t p‖) (Eventually.of_forall (fun i v _=> by unfold J; rw [norm_mul,unitR, one_mul])) (kip_int _ _ h u|>.norm) (Eventually.of_forall fun i z _=> he i z)).2.const_mul _)
def regD (w:List Axis) (f:E4→ℝ): E4→ℝ:=(w.foldr grad f)
lemma quietC (f:E4→ℝ)(p:E4)(v:ContDiffAt ℝ ∞ f p): ContDiffAt ℝ ∞ (regD w f) p:=by induction w with
 | nil=> exact v
 | cons i j u=> exact dSmooth u (basis i) (by simp)
lemma at_jog {x:E4} (a:Axis)(f:E4→ℝ)(p: DifferentiableAt ℝ f x): HasDerivAt (fun z=> f (jog x a z)) (grad a f x) 0:=by
 have hp:= ((hasDerivAt_id' (0:ℝ)).smul_const (basis a)).const_add x
 rw [one_smul] at hp; have hv:jog x a 0=x:=by simp [jog]
 exact p.hasFDerivAt.comp_hasDerivAt_of_eq _ hp hv.symm -- tune
lemma Woof_M (x:E4)(p:x≠0): ContDiffAt ℝ ∞ (fun x=>Woof x t) x:=by unfold Woof; refine (freeSmooth p).mul (contDiffAt_const.sub ?_); exact (((contDiff_norm_sq (E:=E4) ℝ).neg.div_const (4*t)).exp).contDiffAt
lemma cell_K (h:w.length≤2)(b:0<t)(x:E4)(p:x≠0): retK w t x=(regD w (fun x=>Woof x t) x:ℂ):=by
 induction w generalizing x with
 | nil=> exact cell_t t b p
 | cons a j u=>
    have he:= segment_T j t b a h x 0; rw [show jog x a 0=x by simp [jog]] at he
    refine HasDerivAt.unique he ?_
    let J:= regD j (fun x=>Woof x t); have hp:= (at_jog a J ((quietC j _ x (Woof_M t x p)).differentiableAt (by decide))).ofReal_comp
    refine hp.congr_of_eventuallyEq ?_
    have hx:Tendsto (jog x a) (𝓝 0) (𝓝 x):=by simpa [jog] using (show Continuous (jog x a) from by unfold jog; fun_prop).tendsto 0
    exact (hx.eventually (eventually_ne_nhds p)).mono (fun i hp'=>u (by rw [List.length_cons] at h; omega) _ hp')
end YM.StressFHeat
end
