import YM.SU5.Same.DayBreak
/-! # Two-point spectrum prices (all cross-terms; eventually on the CP18 election)
  Do not discard the region geometry for this interpretation. It is spatial
  departure at Vantage p and strict relative Eu time, not retesting as a Mink real smear
  at that very offset. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe Complex
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical ComplexConjugate
open Multiplier Roy
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(X Y:ℝ→ H)
local notation "P" => S.ℚmeasure
local notation "θ" => S.ℚmeasure.diagonal
local notation "μ₀" => homeMeasure S X
local notation "w" a:max => Y a
-- remove final shift. Use *any* real Mink time **added** to that imaginary allowance.
def separationPrice (b : E4)(t:ℝ): ℂ:= inner ℂ (X (t/2)) (planks S b (Y (t/2)))
def momentPrice (μ:Measure E4) (b:E4)(t:ℝ) : ℂ:=
    ∫ p, ↑(Real.exp (-t * p a)) * plane p b ∂μ -- axis implicit?
local notation "β" => coloring
local notation "ψ" => coloringE
-- convenient density API. Use positivity etc. at exponent inside.
lemma normalPrices (p:E4)(t:ℝ≥0) : (coloringE a t p).toReal = coloring a t p:= ENNReal.toReal_ofReal (sq_nonneg _)
@[fun_prop] lemma color_meas(t:ℝ≥0) : Measurable (coloringE a t):= ENNReal.measurable_ofReal.comp (Roy.favorC t|>.pow 2|>.measurable)

-- relative-time unshift on the POS profile. Doesn't use > to assert at z.re=0 when testing lower half rays.
lemma currency_coat (p:E4)(x:0≤p a)(t:ℝ)(u:0<t): coloring a (t/2).toNNReal p= Real.exp (-t*p a):=by
 unfold coloring Roy.favor; rw [sq,←Real.exp_add,max_eq_right x, Real.coe_toNNReal _ (half_pos u|>.le)]; congr 1; ring
variable (hX:SatinJets.Positive S X) -- proof of coherence only
include hX
lemma coat_cost (t:ℝ≥0)(u:0<t)(g:E4→ℂ): (∫ p,g p ∂(θ) (X (t:ℝ)))= ∫ p,(↑(β a t p):ℂ) * g p ∂μ₀:=by
 rw [exact_density S X hX t u, integral_withDensity_eq_integral_toReal_smul (color_meas t) (Eventually.of_forall (fun _=> ENNReal.ofReal_lt_top))]; apply integral_congr_ae (Eventually.of_forall fun p=>?_); rw [normalPrices,Complex.real_smul]
lemma coat_finance (t:ℝ≥0)(u:0<t)(g:E4→ℂ)(Hf:Integrable g ((θ) (X (t:ℝ)))) :
    Integrable (fun p=> (↑(β a t p):ℂ)*g p) μ₀:= by
 rw [exact_density S X hX t u,integrable_withDensity_iff_integrable_smul' (color_meas t) (Eventually.of_forall fun _=> ENNReal.ofReal_lt_top)] at Hf; simp_rw [normalPrices, Complex.real_smul] at Hf; exact Hf
lemma strict_coat_at (b:E4)(t:ℝ)(u:0<t):
    Integrable (fun p=> (↑(Real.exp (-t*p a)):ℂ) * plane p b) μ₀:=by
 let s:= (t/2).toNNReal
 have ht:0 < s:=Real.toNNReal_pos.mpr (half_pos u)
 have he:= coat_finance S X hX s ht (plane · b) ((Picket.story S b).price.rent (P) (X (s:ℝ))); exact he.congr ((home_carried S X).mono fun p f=> congrArg (fun x:ℝ=> (↑x:ℂ)*plane p b) (currency_coat p f t u)) -- congr direction?
lemma separation_price (b:E4) (t:ℝ)(u:0<t): separationPrice S X X b t= momentPrice (a:=a) (homeMeasure S X) b t:=by
 let s:= (t/2).toNNReal; let x:= X (s:ℝ); have hx:x=X (t/2):= congrArg X (Real.coe_toNNReal _ (half_pos u|>.le))
 unfold separationPrice; rw [← hx]; apply ((Picket.story S b).awakes x).trans
 refine (coat_cost S X hX s (Real.toNNReal_pos.mpr (half_pos u)) (plane · b)).trans ?_
 exact integral_congr_ae ((home_carried S X).mono fun p f=> congrArg (fun x:ℝ=> (x:ℂ)*plane p b) (currency_coat p f t u))
omit hX
lemma cont_ask (t:ℝ) : Continuous (fun b=> separationPrice S X Y b t):= continuous_const.inner ((S.unit).moves _)

-- W^+ real boundary, tempered. PVM here for same X. Positive-time Fourier support (use separate lemma elsewhere).
lemma test_budget (t:ℝ)(f:Test4) : Integrable (fun b=> f b* separationPrice S X Y b t):= by
 let M:= ‖X (t/2)‖* ‖Y (t/2)‖; let g(b:E4):= separationPrice S X Y b t;
 apply ((SchwartzMap.integrable f).norm.mul_const M).mono' ((f.continuous.mul (cont_ask S X Y t)).aestronglyMeasurable) -- fix include unused guard
 exact Eventually.of_forall fun b=> (norm_mul (f b) (g b)).trans_le (mul_le_mul_of_nonneg_left ( (norm_inner_le_norm ..).trans_eq (congrArg (‖X (t/2)‖*·) (S.unit.unitary b _))) (norm_nonneg _))

-- canopy averaging at true Eu offset. no need hY for one-ray test. assumes neither spatial continuity past Semigroup nor spectrum cone
lemma under_ask (t:ℝ)(f:Test4):
    (∫ b, f b * separationPrice S X X b t)= ∫ p,onward f p ∂(θ) (X (t/2)) := by
 let u:= X (t/2)
 apply Eq.trans ?_ ((collect_member S f).awakes u); rw [collect_eq,← integral_inner (collect_int S f _)]
 unfold separationPrice; simp_rw [inner_smul_right]; rfl

-- true continuation under the integral, carries all the way! call W^+ at point test
abbrev ventPrice (μ:Measure E4)[μ.HasTemperateGrowth] : Test4 →L[ℂ] ℂ := (SchwartzMap.integralCLM ℂ μ).comp onward
def feelDiag (h:TemperedAtEdge H X): Test4→L[ℂ] ℂ:= letI := tempered_home S X h; ventPrice (homeMeasure S X)
lemma feelDiag_eq (h:TemperedAtEdge H X) (f:Test4) : feelDiag S X h f= ∫ p,onward f p ∂μ₀:= rfl
-- diagonal to heat-down. integrable because requested h. Pointwise over Schwartz inputs.
include hX
lemma progress (h:TemperedAtEdge H X)(f:Test4):
    Tendsto (fun t:ℝ=> ∫ b, f b * separationPrice S X X b t) (𝓝[>] 0) (𝓝 (feelDiag S X h f)):=by
 letI: (μ₀).HasTemperateGrowth:= tempered_home S X h
 let F := (𝓝[>] (0:ℝ)); let s (t:ℝ):=(t/2).toNNReal; let g:=onward f; let L(t:ℝ)(p:E4):= (↑(β a (s t) p):ℂ)*g p
 rw [feelDiag_eq S X h f]; refine Tendsto.congr' ?_ (show Tendsto (fun i=> ∫ p, L i p∂μ₀) F _ from ?_); swap
 · refine tendsto_integral_filter_of_dominated_convergence (fun p:E4=> ‖g p‖) (Eventually.of_forall fun i=> (Continuous.aestronglyMeasurable ((continuous_ofReal.comp (continuous_color (s i))).mul g.continuous))) (Eventually.of_forall fun i=> Eventually.of_forall fun p=> ?_) (SchwartzMap.integrable g (μ:=μ₀)|>.norm) (Eventually.of_forall fun p=>?_) -- double bound?
   · unfold L; rw [norm_mul]; apply mul_le_of_le_one_left (norm_nonneg _); rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (favorL _ _).1.le (favorL _ _).2
   have he: Continuous (fun i=>L i p):=by unfold L s coloring favor; fun_prop
   have hx:L 0 p=g p:=by simp [L,s,coloring,favor]
   exact (he.tendsto' _ _ hx).mono_left nhdsWithin_le_nhds
 filter_upwards [self_mem_nhdsWithin] with i p; let t:=s i; have he:0<t:= Real.toNNReal_pos.mpr (half_pos p); apply Eq.trans _ (under_ask S X i f).symm
 refine (coat_cost S X hX t he (g:E4→ℂ)).symm.trans ?_; rw [show (t:ℝ)=i/2 from Real.coe_toNNReal _ (half_pos (show 0 < i from p)|>.le)] -- notation uses dot
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms separation_price
#print axioms progress
