import YM.CF.Appel.Aid
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
abbrev peakG (G:Gauge)(v:G.Color):ℝ:= (Gaussian.dome G.ColorIndex)⁻¹ * Real.exp (-‖v‖^2/2)
def rice(G:Gauge):Measure G.Color:= stdGaussian G.Color
instance (G:Gauge):IsProbabilityMeasure (rice G):=inferInstanceAs (IsProbabilityMeasure (stdGaussian _))
-- positivity via exact pi and positive GaussianReal support. formula
lemma coins_white (i:Type) [Fintype i][DecidableEq i]: coins i=cloud (1:Gaussian.Table i):=by
 have hp:=paid (1:Gaussian.Table i); rw [CFC.sqrt_one] at hp; simpa using hp
lemma perk (G:Gauge): rice G=volume.withDensity (fun x=>ENNReal.ofReal (peakG G x)):=by
 let v:=G.ColorIndex
 let p:= (MeasurableEquiv.toLp 2 (Vec G.ColorIndex)); have he : MeasurePreserving p volume volume:=PiLp.volume_preserving_toLp G.ColorIndex
 have hm : rice G = (coins G.ColorIndex).map p:=map_pi_eq_stdGaussian.symm
 rw [hm,coins_white,cloud_formula (show (1:Gaussian.Table G.ColorIndex).PosDef from Matrix.PosDef.one)]
 have hf(i): Gaussian.ratio (1:Gaussian.Table G.ColorIndex) i=peakG G (p i):=by
    simp only [Gaussian.ratio,coat, det_one, Real.sqrt_one,mul_one, force, inv_one, Matrix.one_mulVec,peakG]; rw [EuclideanSpace.real_norm_sq_eq]; simp_rw [sq]; rfl
 ext s hs; rw [Measure.map_apply p.measurable hs, withDensity_apply _ (p.measurable hs), withDensity_apply _ hs]
 simp_rw [hf]; exact (he.setLIntegral_comp_preimage_emb p.measurableEmbedding (fun x=>ENNReal.ofReal (peakG G x)) s) -- tune
def grainS(G:Gauge)(v:ℝ):ℝ≥0∞:=rice G (closedBall 0 v)
lemma grain_pos (G:Gauge){v:ℝ}(h:0<v): 0<grainS G v:=by
 let A:=fun x : G.Color=>ENNReal.ofReal (peakG G x); have hm:Measurable A:=by unfold A peakG; fun_prop
 have he :{t | A t ≠ 0}=univ:=Set.eq_univ_of_forall fun i=> (ENNReal.ofReal_pos.mpr (mul_pos (inv_pos.mpr dome_pos) (Real.exp_pos _))).ne'
 apply lt_of_le_of_ne bot_le; unfold grainS; rw [perk]; intro hh
 have ht:= (withDensity_apply_eq_zero hm).mp hh.symm
 rw [he,univ_inter] at ht; exact ((isOpen_ball.measure_pos (volume : Measure G.Color) (show Set.Nonempty (ball 0 v) from ⟨0,mem_ball_self h⟩)).trans_le (measure_mono ball_subset_closedBall)).ne ht.symm
def feast(G:Gauge)(v:ℝ):Measure G.Color:= (grainS G v)⁻¹ • (rice G).restrict (closedBall 0 v)
lemma feast_nn(G:Gauge){v:ℝ}(h:0<v): IsProbabilityMeasure (feast G v):=⟨by unfold feast; rw [Measure.smul_apply,Measure.restrict_apply_univ]; exact ENNReal.inv_mul_cancel (grain_pos G h).ne' (measure_ne_top _ _)⟩
abbrev tableG(G:Gauge)(i:Type) [Fintype i](v:ℝ):Measure (LogArray G i):=Measure.pi fun _=>feast G v
abbrev surface(G:Gauge)(α:Type)[Fintype α](v:ℝ): Set (LogArray G α):=univ.pi (fun _=>closedBall 0 v)
lemma how(G:Gauge){v:ℝ}(h:0<v):IsProbabilityMeasure (tableG G α v):=by haveI:=feast_nn G h; unfold tableG; infer_instance
lemma rice_t(G:Gauge)(α:Type) [Fintype α]: (Measure.pi (fun _:α=> rice G))=(cloud (1:Gaussian.Table (α×G.ColorIndex))).map tape:=by
 rw [←coins_white]; suffices h: MeasurePreserving tape (coins (α×G.ColorIndex)) (Measure.pi (fun _ : α=> rice G)) from h.map_eq.symm
 have ht : MeasurePreserving (fibres (ι:=α) (θ:=G.ColorIndex)) (coins (α × G.ColorIndex)) (Measure.pi (fun _=> coins G.ColorIndex)):=by
    suffices h : MeasurePreserving (fibres (ι:=α) (θ:=G.ColorIndex)).symm (Measure.pi (fun _=>coins G.ColorIndex)) (coins (α × G.ColorIndex)) from h.symm
    haveI : IsProbabilityMeasure (coins G.ColorIndex):=by unfold coins; infer_instance
    constructor
    · exact fibres.symm.measurable
    apply Eq.symm; apply Measure.pi_eq; intro s hs
    rw [Measure.map_apply fibres.symm.measurable (MeasurableSet.univ_pi hs)]
    rw [show fibres.symm ⁻¹' (univ.pi s)=univ.pi (fun i=> univ.pi (fun j=> s (i,j))) from ?_,Measure.pi_pi]; unfold coins; simp_rw [Measure.pi_pi]; rw [Fintype.prod_prod_type]
    ext x; simp [fibres, Set.mem_pi, Function.uncurry]
 haveI:SigmaFinite (coins G.ColorIndex):=by unfold coins; infer_instance
 exact (measurePreserving_pi (μ:= fun _ : α=> coins G.ColorIndex) (ν:=fun _=> rice G) fun _=> (show MeasurePreserving (MeasurableEquiv.toLp 2 (Vec G.ColorIndex)) _ _ from ⟨(MeasurableEquiv.toLp ..).measurable,map_pi_eq_stdGaussian⟩)).comp ht -- tune
lemma meal(G:Gauge){v:ℝ}(h:0<v): (grainS G v)^Fintype.card α • tableG G α v=(Measure.pi (fun _ : α=> rice G)).restrict (surface G α v):=by
 have hx: (grainS G v) ≠0:=(grain_pos G h).ne'; have ht: (grainS G v) ≠⊤:=measure_ne_top _ _; haveI:=feast_nn G h; rw [surface,Measure.restrict_pi_pi]; apply Eq.symm; apply Measure.pi_eq; intro s hs
 rw [Measure.smul_apply,tableG,Measure.pi_pi]
 have hp (i:α): grainS G v * feast G v (s i)= (rice G).restrict (closedBall 0 v) (s i):= by rw [feast,Measure.smul_apply,smul_eq_mul,←mul_assoc, ENNReal.mul_inv_cancel hx ht,one_mul]
 simp_rw [←hp]; rw [Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ]; rfl
end YM.CF.Appel
