import YM.CF.Appel.Boot
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
-- L1 in Z
lemma speed (A:Gaussian.Table α)(h:IsUnit A.det)(f:Vec α → E)(m:Vec α)(s:ℝ)(hs:0<s)(hf:Integrable f):
    let P(x:Vec α):=Real.exp ((x ⬝ᵥ x)/2) • f (m+s • A *ᵥ x) -- parse wrong
    Integrable P (cloud 1) ∧ (∫ i,f i)=(s^Fintype.card α * |A.det| * dome α) • ∫ i,P i ∂cloud 1:=by
 intro P; obtain ⟨he,hp⟩:=paid_scale hs f m; obtain ⟨hq,hT⟩:= sport A h _ (he.mp hf)
 let u (x:Vec α):=f (m+s • (A *ᵥ x)); have hx(x:Vec α): Real.exp (Gaussian.force 1 x /2) • u x=P x:=by simp [P,Gaussian.force,u,Matrix.smul_mulVec]
 obtain ⟨ht,H⟩:=under_cloud Matrix.PosDef.one u; change Integrable _ _ ↔ Integrable (fun x=> Real.exp _ • _) _ at ht; simp_rw [hx] at ht H
 refine ⟨ht.mp hq,?_⟩
 rw [hp,hT,H,smul_smul,smul_smul, Gaussian.coat,det_one,Real.sqrt_one,mul_one]
abbrev MA (α:Type)(G:Gauge):= Gaussian.Table (α×G.ColorIndex)
abbrev spinC (Z:MA α G)(s:ℝ)(m:Prices G α)(x:LogArray G α):= m+s • (Z *ᵥ (tape.symm x))
abbrev spun (Z:MA α G)(s:ℝ)(m:Prices G α)(x:LogArray G α):= tape (spinC Z s m x)
def costU (x:LogArray G α):ℝ:= tape.symm x ⬝ᵥ tape.symm x
abbrev bang (Z:MA α G)(s:ℝ)(m:Prices G α)(f:LogArray G α→E)(x:LogArray G α):= Real.exp (costU x / 2) • f (spun Z s m x)
lemma spare_q (G:Gauge)(α:Type)[Fintype α](s:ℝ)(hs:0<s): s^Fintype.card (α×G.ColorIndex)*Gaussian.dome (α×G.ColorIndex)= ((Real.sqrt (2*Real.pi*s^2))^Fintype.card G.ColorIndex)^Fintype.card α:=by
 rw [← pow_mul,Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]; unfold Gaussian.dome; rw [mul_pow,mul_comm, Fintype.card_prod, Nat.mul_comm]
lemma spin_ledger (Z:MA α G)(hZ:IsUnit Z.det)(s:ℝ)(m:Prices G α)(f:LogArray G α→E)(hs:0<s)(hf:Integrable f) (h:0<v)(ht:∀ x, f (spun Z s m x)≠0 → x∈surface G α v) : Integrable (bang Z s m f) (tableG G α v) ∧ (∫ i,f i)=(|Z.det| * ( (Real.sqrt (2*Real.pi*s^2)) ^ Fintype.card G.ColorIndex * point G v)^ Fintype.card α) • ∫ i,bang Z s m f i ∂tableG G α v:=by
 let A:= bang Z s m f; let g:= f ∘ tape
 obtain ⟨hp',hr⟩:=speed Z hZ g m s hs (tape_volume.integrable_comp_of_integrable hf); have hp(x:Prices G α): Real.exp ((x ⬝ᵥ x)/2) • g (m+s • Z *ᵥ x)=A (tape x):=by unfold g A bang costU; simp only [spinC,spun, Matrix.smul_mulVec,Function.comp_apply,tape.symm_apply_apply]
 let μ := Measure.pi (fun _:α=>rice G); have hu : MeasurePreserving (tape (G:=G) (ι:=α)) (cloud 1) μ:=⟨tape.measurable,by unfold μ; convert! (rice_t G α).symm using 6 <;> first | rfl | exact Subsingleton.elim _ _⟩; dsimp only at hp' hr; simp_rw [hp] at hp' hr
 obtain ⟨hh,H⟩:= bows h A ((hu.integrable_comp_emb tape.measurableEmbedding).mp hp') (fun x hh=>by unfold A bang; rw [show f _=0 from not_not.mp (mt (ht _) hh), smul_zero]); refine ⟨hh,?_⟩
 rw [← tape_volume.integral_comp' f]; refine hr.trans ?_; rw [hu.integral_comp' A,H, smul_smul]; congr 1; rw [mul_pow,show s ^ _ * |Z.det|=|Z.det| *s^ _ from mul_comm ..,mul_assoc |Z.det|,spare_q G α s hs,mul_assoc]
end YM.CF.Appel
