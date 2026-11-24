import YM.CF.Appel.Move
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open Set Topology
open scoped MatrixOrder
-- single polar product truncate. define via density color, prove invariance later
def point (G:Gauge)(v:ℝ):ℝ:=(grainS G v).toReal
lemma point_p (h:0<v):0<point G v:=ENNReal.toReal_pos (grain_pos G h).ne' (measure_ne_top _ _)
lemma bows (h:0<v)(f:LogArray G α → E)(hf:Integrable f (Measure.pi (fun _=> rice G)))(hp:∀ x:LogArray G α,x∉surface G α v→ f x =0):
    Integrable f (tableG G α v) ∧ (∫ x, f x ∂Measure.pi (fun _=> rice G))=(point G v)^Fintype.card α • ∫ x, f x ∂tableG G α v:=by
 let s:=surface G α v; have he:MeasurableSet s:= MeasurableSet.univ_pi fun _=> isClosed_closedBall.measurableSet; have hx : s.indicator f=f:=by
    ext1 x; by_cases hh:x∈s; · exact indicator_of_mem hh f
    rw [indicator_of_notMem hh f,hp x hh]
 let a:= (grainS G v)^Fintype.card α; have ha: a≠0:=pow_ne_zero _ (grain_pos G h).ne'; have hd : a ≠ ⊤ :=ENNReal.pow_ne_top (measure_ne_top (rice G) _) -- tune
 have hm:= meal (α:=α) G h; change a • tableG G α v=_ at hm
 constructor
 · have hv:=hf.integrableOn (s:=s); rw [IntegrableOn,← hm] at hv; exact (integrable_smul_measure ha hd).mp hv -- tune
 calc
    _ = ∫ x in s, f x ∂Measure.pi (fun _=> rice G) := by rw [← integral_indicator he,hx]
    _ = _ := by rw [← hm, integral_smul_measure, point]; unfold a; rw [ENNReal.toReal_pow]
-- linear change
abbrev rollPay(A:Gaussian.Table α)(x: Vec α):= A *ᵥ x
def tiltP(A:Gaussian.Table α)(h:IsUnit (det A)): Vec α≃ᵐ Vec α where
 toFun := rollPay A
 invFun := rollPay A⁻¹
 left_inv i:= by unfold rollPay; rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
 right_inv i:=by unfold rollPay; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
 measurable_toFun := acts_meas _
 measurable_invFun := acts_meas _
lemma sport (A:Gaussian.Table α)(h:IsUnit (det A))(f: Vec α → E)(he:Integrable f): Integrable (fun i=> f (A *ᵥ i)) ∧ (∫ i,f i) = |A.det| • ∫ i,f (A *ᵥ i):=by
 let e:= tiltP A h; let t:= ENNReal.ofReal |(det A)⁻¹|
 have ht : MeasurePreserving e volume (t • volume):=⟨e.measurable, by change Measure.map (rollPay A) _= _; rw [show (rollPay A)=(Matrix.toLin' A:Vec α→ Vec α) from funext fun x=> (Matrix.toLin'_apply A x).symm]; exact Real.map_matrix_volume_pi_eq_smul_volume_pi h.ne_zero⟩
 refine ⟨ht.integrable_comp_of_integrable (he.smul_measure ENNReal.ofReal_ne_top), Eq.symm ?_⟩
 change _ • (∫ i,f (e i))= _; rw [ht.integral_comp',integral_smul_measure,smul_smul]; unfold t; rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h.ne_zero),one_smul]
end YM.CF.Appel
