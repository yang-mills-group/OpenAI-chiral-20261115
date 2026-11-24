import YM.CF.Pso.Dual
import YM.CF.Reine.Aeon
import YM.CF.Appel.Move
import YM.CF.Vp929.Analysis.Integrate
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Appel.Rate
open Char Summit Neige Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet ProbabilityTheory
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine AnalyticBridge.Annulus1AD
 AnalyticBridge.NonflatCovarianceLocality.Matching Next.Fluctuations Next.SectorChange Reine
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal Classical
section lift
variable {α β:Type} [MeasurableSpace α] [MeasurableSpace β]
lemma liftDensity (e:α≃ᵐβ) (μ:Measure α)(f:α→ℝ≥0∞): (μ.withDensity f).map e = (μ.map e).withDensity (fun x=> f (e.symm x)):= by
 ext s hs; rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs, e.restrict_map,e.measurableEmbedding.lintegral_map,withDensity_apply _ (e.measurable hs)]; simp
end lift
variable {G:Gauge} (y:G.Color) {h t C:ℝ}
local notation "κ" => Fintype.card G.ColorIndex
local notation "j" => grainS G
local notation "|μ|" => feast G h
/- fixed physical real ball radius = h (master radius is 2h). Scale by t=sqrt(s/Y). -/
private abbrev ϑ (h:ℝ):= (rice G).restrict (closedBall 0 h)
/-- Real single density factor before normalize. Parameter already divided by year. -/
def cup (u:ℝ)(p:G.Color):ℝ:= Real.exp ((1-u)*(‖p‖^2/2))
lemma cup_pos (u:ℝ)(x:G.Color):0<cup u x:= Real.exp_pos _
lemma cup_comp (z:ℝ):Continuous (cup (G:=G) z):= by unfold cup;fun_prop
def n_cup (u:ℝ)(h:ℝ):ℝ:=∫ i:G.Color,cup u i∂feast G h
variable (ht:0<t) (hp:0<h)
include ht
local notation "τ" => ((Cay.dialK t ht.ne' G.Color).toHomeomorph.toMeasurableEquiv)
def pitched (G : Gauge) (t h:ℝ):Measure G.Color:= (feast G (t*h)).map (fun i=> t⁻¹ • i)
private lemma raw: (ϑ (G:=G) (t*h)).map (τ).symm = ENNReal.ofReal (t^κ) • (ϑ (G:=G) h).withDensity (fun x=> ENNReal.ofReal (cup (t^2) x)):=by
 let V:= volume (α:=G.Color); let f(x:G.Color):= peakG G x; let F(x:G.Color):= ENNReal.ofReal (peakG G x); let L: G.Color≃ᵐ G.Color:=τ
 have T: Measure.map L.symm V= ENNReal.ofReal (t^κ) • V:= by
    rw [show (L.symm:G.Color→G.Color)=(fun x=> t⁻¹ • x) from rfl,Measure.map_addHaar_smul V (inv_pos.mpr ht).ne',finrank_euclideanSpace, inv_pow, inv_inv, abs_of_nonneg (by positivity)]
 have g(y:G.Color): f (τ y)=f y * cup (t^2) y:= by
    dsimp only [f,peakG,cup]; rw [mul_assoc,←Real.exp_add]; congr 2; change -‖t • y‖^2 / 2 = _; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.le]; ring
 have q : ((τ).symm ⁻¹' closedBall 0 h)=closedBall 0 (t*h):= by
    ext x; simp only [Set.mem_preimage, mem_closedBall_zero_iff]; change ‖t⁻¹ • x‖≤ h ↔ _; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),inv_mul_le_iff₀ ht]
 unfold ϑ; rw [perk, ←q, ← MeasurableEquiv.restrict_map,liftDensity]; change ((V.map L.symm).withDensity _).restrict _=_; rw [T,withDensity_smul_measure,Measure.restrict_smul,restrict_withDensity isClosed_closedBall.measurableSet,restrict_withDensity isClosed_closedBall.measurableSet,← withDensity_mul]; congr 1; congr 1; funext y; change ENNReal.ofReal (f (τ y))=ENNReal.ofReal (f y)*_; rw [g y,ENNReal.ofReal_mul]; exact mul_nonneg (inv_nonneg.mpr Next.SectorChange.Gaussian.dome_pos.le) (Real.exp_pos _).le
 all_goals first| exact (measurable_const.mul (Real.continuous_exp.measurable.comp (by fun_prop))).ennreal_ofReal| unfold peakG cup; fun_prop| unfold peakG; fun_prop| unfold cup;fun_prop
include G hp
private lemma bright (H: G.Color→ℝ)
 : (∫ i,H i ∂(ϑ (G:=G) (t*h)).map (τ).symm)=(t^κ)*∫ i,cup (t^2) i*H i ∂ ϑ (G:=G) h:= by
 rw [raw ht, integral_smul_measure,ENNReal.toReal_ofReal (by positivity), integral_withDensity_eq_integral_toReal_smul ((cup_comp _).measurable.ennreal_ofReal) (Eventually.of_forall fun x=> ENNReal.ofReal_lt_top)]; simp only [ENNReal.toReal_ofReal (cup_pos _ _).le,smul_eq_mul]
theorem changePoint: point G (t*h) = t^κ* n_cup (G:=G) (t^2) h * point G h:= by
 let f:=cup (G:=G) (t^2); have p:=grain_pos G hp; have hk:=point_p (G:=G) hp
 have T:= bright (G:=G) ht hp (fun _=>1); rw [integral_const,Measure.real,Measure.map_apply_of_aemeasurable (τ).symm.measurable.aemeasurable MeasurableSet.univ] at T
 unfold n_cup feast; rw [integral_smul_measure,ENNReal.toReal_inv]; change _= t^κ*((point G h)⁻¹ * ∫ i,f i ∂ϑ h) * point G h; have H: point G (t*h)=(t^κ)*(∫ i, f i ∂ϑ h):= by simpa [point,ϑ,grainS,f] using T
 rw [H]; field_simp
theorem change_shot (u v:ℝ)(p:0<u)(q:0<v)(hp':Cay.rune v u=t)(L:ChartRatio G): spare L v*point G (t*h)=spare L u*point G h*n_cup (G:=G) (t^2) h:=by
 have hh: spare L u=t^κ*spare L v:= by
    unfold spare; rw [←mul_assoc,←mul_pow]; congr 2; unfold Cay.rune at hp'; have hv:=coupling_pos q; rw [div_eq_iff hv.ne'] at hp'; rw [hp',show 2*Real.pi*(t*coupling v)^2=t^2*(2*Real.pi*coupling v^2) from by ring,Real.sqrt_mul (by positivity),Real.sqrt_sq ht.le]
 rw [changePoint ht hp,hh]; ring
omit ht in
lemma cup_int (z:ℝ):Integrable (cup (G:=G) z) |μ|:= ((cup_comp _).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).smul_measure (ENNReal.inv_ne_top.mpr (grain_pos _ hp).ne')
lemma n_pos_local : 0<n_cup (G:=G) (t^2) h:= by
 have q:=changePoint (G:=G) ht hp; have T:=point_p (G:=G) (mul_pos ht hp); by_contra! e; rw [q] at T; exact T.not_ge (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) e) (point_p hp).le)
lemma pitcher_eq : pitched G t h =(feast G h).withDensity (fun i=>ENNReal.ofReal (cup (t^2) i/n_cup (G:=G) (t^2) h)) := by
 let F:= fun i: G.Color=> ENNReal.ofReal (cup (t^2) i); let b:= n_cup (G:=G) (t^2) h; let V:=ENNReal.ofReal b; have hm:Measurable F:= (cup_comp _).measurable.ennreal_ofReal
 have q:0<b:=n_pos_local ht hp
 have hi(y:ℝ):j y= ENNReal.ofReal (point G y):= (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
 unfold pitched feast; rw [show (fun i:G.Color=>t⁻¹ • i)= ((τ).symm: G.Color→G.Color) from rfl,Measure.map_smul, raw ht,show (fun i:G.Color=> ENNReal.ofReal (cup (t^2) i/n_cup (G:=G) (t^2) h)) = V⁻¹ • F from ?_, withDensity_smul_measure,withDensity_smul _ hm,smul_smul,smul_smul]; congr 1
 · have T:j (t*h)≠0:= (grain_pos G (mul_pos ht hp)).ne'
   refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
   · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr T) ENNReal.ofReal_ne_top
   · refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (grain_pos G hp).ne') (ENNReal.inv_ne_top.mpr (by unfold V; positivity))
   simp only [ENNReal.toReal_mul,ENNReal.toReal_inv]; unfold V; rw [ENNReal.toReal_ofReal q.le,ENNReal.toReal_ofReal (by positivity)]; change (point G (t*h))⁻¹ * _= (point G h)⁻¹*_; change _= (point G h)⁻¹ * b⁻¹; have T: point G (t*h)=t^κ*b*point G h:= changePoint ht hp; rw [T]; have:= point_p (G:=G) hp; field_simp
 unfold V F; funext x; rw [Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_div_of_pos q]; dsimp only [b]; rw [mul_comm]; rfl
end YM.CF.Appel.Rate
