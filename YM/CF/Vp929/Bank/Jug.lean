import YM.CF.Vp929.Bank.Cup
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Appel.Rate
open Function Filter Set Lattice RG Precision Pressure MeasureTheory Metric ProbabilityTheory
 AnalyticBridge.LocalGaussianLaws AnalyticBridge.Annulus1AD Next.Fluctuations Next.SectorChange Reine
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal Classical
variable {G:Gauge} {h t a C:ℝ} {z:ℂ}
local notation "κ" => Fintype.card G.ColorIndex
local notation "|ν|" => pitched G t h
local notation "|μ|" => feast G h
local notation "τ" => t^2
def cupX (z:ℂ)(y:G.Color):= Complex.exp ((1-z)*((‖y‖^2/2:ℝ):ℂ))
def jug (G:Gauge)(h:ℝ)(z:ℂ):=∫ x:G.Color,cupX z x∂feast G h
local notation "J" => jug G h

def cupB (t h:ℝ)(x:G.Color):= cup (t^2) x/n_cup (G:=G) (t^2) h
def flask (G:Gauge)(h:ℝ)(z:ℂ)(x:G.Color):= cupX z x/jug G h z
variable (ht:0<t) (hp:0<h)

lemma cupX_real (s:ℝ)(y:G.Color):cupX (s:ℂ) y=(cup s y:ℂ):= by simp [cupX,cup]
lemma jug_real (s:ℝ): J (s:ℂ)=(n_cup (G:=G) s h :ℂ):= by unfold jug; simp_rw [cupX_real,integral_complex_ofReal]; rfl
lemma feast_ae : ∀ᵐ (x:G.Color)∂ |μ|, x ∈ closedBall 0 h:= Measure.ae_smul_measure (ae_restrict_mem isClosed_closedBall.measurableSet) _
lemma pitched_mp_map : MeasurePreserving (fun x:G.Color=> t⁻¹ • x) (feast G (t*h)) |ν|:= ⟨by fun_prop,rfl⟩
include ht hp
lemma pitched_p : IsProbabilityMeasure |ν|:= by
 haveI:= feast_nn G (mul_pos ht hp); exact Measure.isProbabilityMeasure_map (μ:=feast G (t*h)) ((pitched_mp_map (G:=G) (h:=h)).measurable.aemeasurable)
lemma cupB_pos (x:G.Color):0< cupB t h x:= div_pos (cup_pos _ _) (n_pos_local ht hp)
lemma pitched_ae: ∀ᵐ x:G.Color∂ |ν|, x∈closedBall 0 h:= by
 rw [pitcher_eq ht hp]; exact withDensity_absolutelyContinuous |μ| _ feast_ae
lemma pitched_cont_int {E:Type} [NormedAddCommGroup E]{f:G.Color→E} (e:Continuous f): Integrable f |ν|:= by
 haveI:= pitched_p (G:=G) ht hp; have H:= e.continuousOn.integrableOn_compact (μ:=|ν|) (isCompact_closedBall (0:G.Color) h); rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem (pitched_ae ht hp)] at H
lemma pitched_ant {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f:G.Color→E):(∫ x,f x∂|ν|)=∫ x,(cupB t h x) • f x∂|μ|:= by
 rw [pitcher_eq ht hp,integral_withDensity_eq_integral_toReal_smul]; swap; exact ((cup_comp _).measurable.div_const _).ennreal_ofReal; change (∫ x,(ENNReal.ofReal (cupB t h x)).toReal • f x∂|μ|)=_; simp_rw [ENNReal.toReal_ofReal (cupB_pos ht hp _).le]
 exact Eventually.of_forall fun _=> ENNReal.ofReal_lt_top
omit ht in
lemma jug_entire: Differentiable ℂ (jug G h):= by
 haveI:= feast_nn G hp; intro z; let K:=closedBall (0:G.Color) h; let D:=ball z 1; let P :Set (ℂ×G.Color):=(closedBall z 1)×ˢ K; let f(p:ℂ×G.Color):= cupX p.1 p.2; have hm: Continuous f:=by unfold f cupX; fun_prop
 have U:IsCompact P:= (isCompact_closedBall ..).prod (isCompact_closedBall ..); have M z:Continuous (cupX (G:=G) z):=by unfold cupX;fun_prop
 obtain ⟨B,H⟩:=(U.image hm.norm).bddAbove; apply (YM.CF.VolumeRate.integrate_holo (α:=G.Color) (μ:=|μ|) (v:=fun _=> B) (U:=D) isOpen_ball (_ : ∀ᵐ _∂_, _) (fun z _=>(M z).aestronglyMeasurable) (integrable_const _)).differentiableAt (ball_mem_nhds z zero_lt_one)
 filter_upwards [feast_ae (G:=G)] with i hi; exact ⟨(show Differentiable ℂ (fun z=> cupX z i) by unfold cupX; fun_prop).differentiableOn,fun x hx=> H ⟨(x,i),mk_mem_prod (ball_subset_closedBall hx) hi,rfl⟩⟩
section estimates
lemma abs_cupB (z:ℂ)(hz:z.re=t^2) (x:G.Color): ‖flask G h z x/(cupB t h x:ℂ)‖ = ‖J (t^2:ℝ)‖/ ‖J z‖ := by
 have P:=cup_pos (t^2) x; have Q:=n_pos_local (G:=G) ht hp; have U:‖cupX z x‖=cup (t^2) x:=by unfold cupX cup; rw [Complex.norm_exp,Complex.mul_re]; simp only [Complex.sub_re,hz,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
 unfold flask; rw [norm_div,norm_div, U, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cupB_pos ht hp x).le,jug_real, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg Q.le]; unfold cupB
 grind
local notation "w" => ‖z-((t^2:ℝ):ℂ)‖
local notation "D" => w*(2/a)
private def punch (a:ℝ)(x:G.Color):=Real.exp (a*‖x‖^2)
private def η (t:ℝ)(z:ℂ)(x:G.Color):= Complex.exp ((((t^2:ℝ):ℂ)-z)*((‖x‖^2/2:ℝ):ℂ))
private lemma make_η: J z/ J (t^2:ℝ) = ∫ x,η (G:=G) t z x ∂|ν|:= by
 rw [pitched_ant ht hp, jug_real, jug, ← integral_div]
 let U:= n_cup (G:=G) (t^2) h; refine integral_congr_ae (Eventually.of_forall fun x=>?_); dsimp only; rw [Complex.real_smul,cupB,Complex.ofReal_div]; have H: cupX z x=(cup (t^2) x:ℂ)*η t z x:= by rw [← cupX_real]; unfold cupX η; rw [←Complex.exp_add]; congr 1; ring
 rw [H]; ring
private lemma pitched_push (u:G.Color→ℝ): (∫ i,u (t•i)∂|ν|)=∫ i,u i∂feast G (t*h):= by
 let e:= (Cay.dialK t ht.ne' G.Color).toHomeomorph.toMeasurableEquiv; change (∫ i,u (e i) ∂(feast G (t*h)).map e.symm)=_; rw [e.symm.measurableEmbedding.integral_map]; simp
variable (ha:0<a) (u: 1/2 ≤ t^2) (V:‖z-((t^2:ℝ):ℂ)‖≤ a/2)
include ha u V
private lemma price_η(x:G.Color) : ‖η t z x-1‖ ≤ D*punch a (t•x) := by
 let L:= ‖x‖^2/2; let U:=‖t • x‖^2; have hP:L≤U:= by unfold U L; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.le,mul_pow]; nlinarith
 let y:= (((t^2:ℝ):ℂ)-z)*(L:ℂ); have e:‖y‖=w*L:=by dsimp [y]; rw [norm_mul,norm_sub_rev,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (by unfold L; positivity)]
 have hv:‖Complex.exp y-1‖ ≤ ‖y‖*Real.exp ‖y‖:= by simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp y 1
 have hu:0≤L:= by unfold L; positivity
 let m:=a/2*U; have q:m ≤ Real.exp m:= by linarith [Real.add_one_le_exp m]
 change ‖Complex.exp y-1‖ ≤ D*Real.exp (a*U); rw [show a*U=m+m by unfold m;ring,Real.exp_add]; refine hv.trans ?_; rw [e]; have p:w*L≤ m:=mul_le_mul V hP hu (by positivity); rw [←mul_assoc]; exact mul_le_mul (by
   calc
    _ ≤ w*U:=mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ = D*m:= by unfold m; field_simp
    _ ≤ D*Real.exp m:=mul_le_mul_of_nonneg_left q (by positivity)) (Real.exp_le_exp.mpr p) (Real.exp_pos _).le (by positivity)
/-- Local relative estimate (complex or real). Also gives real/complex ratio for cost transfer. -/
theorem relative_norm (hc : (∫ i:G.Color, Real.exp (a*‖i‖^2)∂feast G (t*h)) ≤ C) : ‖J z/J (t^2:ℝ)-1‖ ≤ D*C:=by
 haveI:= pitched_p (G:=G) ht hp; let f:=η (G:=G) t z; have hg:Integrable f |ν|:= pitched_cont_int ht hp (by unfold f η; fun_prop); let g(i:G.Color):=punch a (t•i)
 have hk:Integrable g |ν|:= pitched_cont_int ht hp (by unfold g punch; fun_prop)
 rw [make_η ht hp]; change ‖(∫ i,f i ∂|ν|)-1‖ ≤ D*C; rw [show (1:ℂ)=(∫ _x:G.Color,(1:ℂ)∂|ν|) by simp]
 rw [← integral_sub hg (integrable_const _)]; refine (norm_integral_le_integral_norm ..).trans ((integral_mono ((hg.sub (integrable_const _)).norm) (hk.const_mul D) fun x=> price_η ht hp ha u V x).trans ?_)
 rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left ((pitched_push ht hp (punch (G:=G) a)).trans_le hc) (by positivity)
end estimates
end YM.CF.Appel.Rate
