import YM.SU5.Same.RollCall
import YM.SU5.Same.BrightMeasure
/-!
# Removing the time heat from the actual limiting profiles.

No analytic assertions about spacelike regions. Norm in the **same** G
in unpadding approach, even covariance under the S real translations.
-/
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
variable {H:Hilbert} {a:Axis}(S:OS.Semigroup H a)(X:ℝ→ H)
local notation "P" => S.ℚmeasure
local notation "θ" => S.ℚmeasure.diagonal
local notation "Z" n:max => wing S X n
local notation "μ₀" => homeMeasure S X

abbrev earnings (i:ℕ)(f:Test4): H := collect S f (wing S X i)
lemma earnings_in (i:ℕ)(f:Test4): earnings S X i f ∈ booth S i:= (member S).mpr
   ((project_commute S (collect_member S f) i (Z i)).trans (congrArg (fun z:H=> collect S f z) (wing_fixed S X i)))
abbrev heldSalary (f:Test4)(i:ℕ) : booth S i:= ⟨_,earnings_in S X i f⟩
lemma payDay (f:Test4)(i:ℕ): ‖earnings S X i f‖^2 = ∫ p, ‖onward f p‖^2∂(θ) (Z i):= (collect_member S f).squareCost (Z i)
variable (h:TemperedAtEdge H X)
include h
lemma earnsDay (f:Test4) : HasSum (fun i:ℕ=> ‖earnings S X i f‖^2) (∫ p:E4,‖onward f p‖^2∂μ₀):=by
 letI:(μ₀).HasTemperateGrowth:= tempered_home S X h
 simp_rw [payDay]; refine hasSum_integral_measure (MemLp.integrable_norm_pow (show MemLp (onward f : E4→ℂ) (↑(2:ℕ):ℝ≥0∞) μ₀ from ?_) (by norm_num)); exact SchwartzMap.memLp (onward f) _ μ₀
lemma aSide (f:Test4):Summable (fun i:ℕ=>earnings S X i f):= ((orth_cells S).summable_iff_norm_sq_summable (heldSalary S X f)).2 (earnsDay S X h f).summable

def awakeLM : Test4→ₗ[ℂ] H where
 toFun f:=∑' i:ℕ, earnings S X i f
 map_add' f g:= by
    have e(i):earnings S X i (f+g)=earnings S X i f+earnings S X i g:=by unfold earnings collect; rw [map_add,map_add]; rfl
    simp_rw [e]; exact (aSide S X h f).tsum_add (aSide S X h g)
 map_smul' c f:= by
    have e(i):earnings S X i (c • f)=c • earnings S X i f:=by unfold earnings collect; rw [map_smul,map_smul]; rfl
    simp_rw [e,tsum_const_smul'']; rfl

lemma earns_norm (f:Test4): ‖awakeLM S X h f‖^2= ∫ p:E4,‖onward f p‖^2∂μ₀:= by
 let p:= (aSide S X h f).hasSum; let e:= earnsDay S X h f
 refine tendsto_nhds_unique (l:=atTop) (f:=fun s:Finset ℕ=> ‖∑ i∈s, earnings S X i f‖ ^2) ((show Tendsto (fun s:Finset ℕ=>∑ i∈s, earnings S X i f) atTop (𝓝 (awakeLM S X h f)) from p).norm.pow 2) ((show Tendsto _ _ _ from e).congr (fun i=>(OrthogonalFamily.norm_sum (orth_cells S) (heldSalary S X f) i).symm))
-- pull back the Rayleigh norm. take care full coefficient α.
abbrev salarySquare : Test4→L[ℂ]MeasureTheory.Lp ℂ 2 (homeMeasure S X):=
 letI:=tempered_home S X h; (SchwartzMap.toLpCLM ℂ ℂ 2 (homeMeasure S X)).comp onward
lemma expense_eq (f:Test4): ‖salarySquare S X h f‖= ‖awakeLM S X h f‖:=by
 letI : (μ₀).HasTemperateGrowth:= tempered_home S X h
 change ‖SchwartzMap.toLpCLM ℂ ℂ 2 μ₀ (onward f)‖=_
 rw [SchwartzMap.toLpCLM_apply,SchwartzMap.norm_toLp' (by simp) (by simp)]; simp only [ENNReal.toReal_ofNat, ← one_div (2:ℝ), ← Real.sqrt_eq_rpow]; simp_rw [Real.rpow_two,← earns_norm S X h f]; exact Real.sqrt_sq (norm_nonneg (awakeLM S X h f))

lemma awake_cont : Continuous (awakeLM S X h):=by
 let V:= awakeLM S X h; let L:=salarySquare S X h; apply continuous_of_continuousAt_zero
 change Tendsto V (𝓝 0) (𝓝 (V 0)); rw [map_zero]; apply tendsto_zero_iff_norm_tendsto_zero.mpr
 refine Tendsto.congr (f₁:=fun f:Test4=> ‖L f‖) (fun f=>expense_eq S X h f) ?_
 simpa only [map_zero,norm_zero] using (L.continuous.tendsto 0).norm

/-- Genuine Schwartz-continuous complex-linear f(x)-smeared field, into KET space. -/
def awake : Test4→L[ℂ] H:= ⟨awakeLM S X h,awake_cont S X h⟩
lemma hasAwake(f:Test4):HasSum (fun i:ℕ=> earnings S X i f) (awake S X h f):= (aSide S X h f).hasSum
lemma expense_inner (f g:Test4) : inner ℂ (awake S X h f) (awake S X h g)=∫ x, star (onward f x)* onward g x∂μ₀:=by
 let F:= salarySquare S X h; let A:=awake S X h
 have hv(f:Test4): ‖F f‖= ‖A f‖:=expense_eq S X h f
 refine Eq.trans ?_ (show inner ℂ (F f) (F g)=_ from ?_)
 · change inner ℂ (A f) (A g)=_; rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four];
   simp_rw [← map_smul F,← map_add F,←map_sub F,hv,map_add,map_sub,map_smul]
 letI: (μ₀).HasTemperateGrowth:= tempered_home S X h
 refine Eq.trans ?_ (integral_congr_ae (Eventually.of_forall (fun p=> (show inner ℂ (onward f p) (onward g p)=star (onward f p)*onward g p from mul_comm ..))))
 change inner ℂ (SchwartzMap.toLpCLM ℂ ℂ 2 μ₀ (onward f)) _=_
 rw [SchwartzMap.toLpCLM_apply, show F g=SchwartzMap.toLp  (onward g) 2 μ₀ from rfl]; exact SchwartzMap.inner_toL2_toL2_eq _ _ (μ₀)

-- actual heat approach (not just energies at points cost in candidate measure).
variable (Z₁:SatinJets.Positive S X)
include Z₁
omit h in
lemma forward_earnings (t:ℝ≥0)(u:0<t)(i:ℕ)(f:Test4): S.E t (earnings S X i f)= collect S f (cell S i (X t)):=by
 unfold earnings
 rw [show S.E t (collect S f (wing S X i))= collect S f (S.E t (wing S X i)) from DFunLike.congr_fun ((costT S t).jointly (collect_member S f)).eq (Z i), wing_earns S X Z₁ t u i]
-- check h assumption omitted forward via include h leak
lemma awake_on_axis (t:ℝ≥0)(u:0<t)(f:Test4): S.E t (awake S X h f)= collect S f (X t):=by
 apply HasSum.unique ( (hasAwake S X h f).mapL (S.E t)); have he := (voting S (X t)).mapL (collect S f); simp_rw [forward_earnings S X Z₁ t u]; exact he -- shadow (g∘f)
lemma rise_heat (f:Test4) : Tendsto (fun t:ℝ=> collect S f (X t)) (𝓝[>] 0) (𝓝 (awake S X h f)):=by
 let x:= awake S X h f; have hx:Tendsto (fun t:ℝ=> S.E t.toNNReal x) (𝓝[>] 0) (𝓝 (S.E 0 x)):= ((S.continuousE x).tendsto 0).comp (show Tendsto Real.toNNReal (𝓝[>] (0:ℝ)) (𝓝 0) from ((show Real.toNNReal 0=0 from by simp) ▸ continuous_real_toNNReal.continuousWithinAt))
 rw [S.eZero, ContinuousLinearMap.id_apply] at hx
 refine hx.congr' ((show ∀ᶠ t:ℝ in 𝓝[>] 0, t∈Set.Ioi 0 from self_mem_nhdsWithin).mono fun t v=> ?_); exact (awake_on_axis S X h Z₁ t.toNNReal (Real.toNNReal_pos.mpr v) f).trans (congrArg (fun t:ℝ => collect S f (X t)) (Real.coe_toNNReal t (show 0<t from v).le))
lemma transportation (b:E4) (f:Test4): S.unit.translation b (awake S X h f)= awake S X h (ahead b f):=by
 apply tendsto_nhds_unique_of_eventuallyEq (((S.unit.translation b).continuous.tendsto _).comp (rise_heat S X h Z₁ f)) (rise_heat S X h Z₁ (ahead b f)); exact Eventually.of_forall fun i=> dayShift S f b (X i)
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms expense_inner
#print axioms rise_heat
#print axioms transportation
