import YM.CF.Neige.Walk
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open SectorNext.Vacuum.FlatTree NormedSpace Next.SectorChange.Rows
variable (F:Forest S.ratio)(h:S.patch.Branches S.kernel G) (i:ℝ) {u t z:ℝ}{o₁:Signed}
lemma straightX(a:G.Color)(s t:ℝ): G.lieExp ((s-t) • a)=G.lieExp (s•a)*(G.lieExp (t•a))⁻¹:=by
 apply G.mat_injective; rw [← exp_negative]; simp only [G.mat_mul,G.mat_lieExp, map_smul,map_neg]; letI : NormedAlgebra ℚ G.Mat:=.restrictScalars ℚ ℝ _
 let v:= G.colorMat a; rw [sub_smul,sub_eq_add_neg]; apply NormedSpace.exp_add_of_commute; unfold Commute SemiconjBy; simp only [neg_mul,mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_comm s t]
lemma left_const_r {E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B](f:E→ B)(x:E)(y:B)(h:∀ s:ℝ,f (s•x)=y): fderiv ℝ f 0 x=0:=by
 by_cases hf:DifferentiableAt ℝ f 0
 · have he:= Push.side f hf x; simp_rw [h] at he; exact he.unique (hasDerivAt_const ..)
 rw [fderiv_zero_of_not_differentiableAt hf]; rfl
def increase (t:Site f→ℝ)(a:G.Color)(s:ℝ)(x:Site f):= G.lieExp ((s*t x)•a)
lemma vjor (a:G.Color)(t:Site f→ℝ)(s:ℝ): increment (replica S.ratio 1) (s • SectorNext.Vacuum.FlatTree.climb (fun i=> t i • a))=gauge (increase t a s) 1:=by
 rw [replica_one]; funext i; simp only [SectorNext.Vacuum.FlatTree.climb,Lattice.gauge,increment,increase,Pi.one_apply,mul_one, Pi.smul_apply]; rw [smul_sub,smul_smul,smul_smul, ←sub_smul,straightX]
include h in
lemma lensX (k:S.Choices)(a:G.Color)(t:Site f→ℝ)(ht:∀ i:Site c,t (S.ratio.embed i)=0): Rows.bump T x 1 k (SectorNext.Vacuum.FlatTree.climb fun i=>t i•a)=0:=by
 let w:Directions G f:= SectorNext.Vacuum.FlatTree.climb fun i=> t i•a
 have he(b) (s:Signed) : facade S s (1:Config G c) (b • w) = gauge ((increase t a b)∘ affine s 0) 1 := by unfold w facade; rw [vjor, AnalyticNext.QuarticMatch.Joint.pullGauge]; rw [show pull s 0 (1:Config G f)=1 from funext fun i=>by simp [Lattice.pull,Step.read]]
 have hp(s:Signed)(i:Cell f): plaquetteJet S (1:Config G c) s i w=0:= by
    unfold plaquetteJet; refine left_const_r _ w 0 (fun b=>?_); rw [he,face_gauge]; simp [faceValue,square,travel,Step.read]
 have hK(s:Signed)(i:Bond c)(b:ℝ):predictGroup (1:Config G c) k s i (b•w)= S.prediction 1 (Oriented.choice s k) i:=by
    let F:= increase t a b; unfold predictGroup; rw [he,(choice_gauge h _ _ _).2]; suffices hu:∀ i:Site c,increase t a b (affine s 0 (S.ratio.embed i))=1 by simp only [Lattice.gauge,Function.comp_apply,hu,inv_one,one_mul,mul_one]
    intro i; simp only [affine, add_zero, ← Ratio.signed,increase,ht,mul_zero,zero_smul,G.mat_lieExp_zero] -- signed rewrite
 funext j; obtain ⟨s,j|j⟩:=j; change faceKick T x 1 w s j=0; unfold faceKick; split
 · simp [barrel,hp]
 · rw [hp,smul_zero]
 have hf:blockJet (1:Config G c) k s j w=0:=by
    unfold blockJet; apply left_const_r _ w 0; intro b; simp only [predictorTurn,hK]; rw [show predictGroup _ k s j 0=S.prediction _ _ _ from by simpa only [zero_smul] using hK s j 0,mul_inv_cancel]; simp
 change -(_ • blockJet _ _ _ _ w)=0; rw [hf,smul_zero,neg_zero]
lemma calmK(S:StepData c f)(k:S.Choices)(h:S.patch.Branches S.kernel G): ∀ᶠ x in 𝓝 (0:Bid.Dir G f), (∀ y, S.patch.usesMin S.kernel (expandAt (S.ratio.embed y) (represent x))) ∧∀ i,S.patch.usesBest S.kernel (S.connector (represent x) k.1 i):=by
 have he(i:Bond c): ContinuousAt (Push.deck (G:=G) S i k.1) 0 := continuousAt_pi.mpr fun j=> (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (Push.builds S h _ k.1 j).continuousAt.tendsto
 have hp:∀ i:Bond c,∀ᶠ x in 𝓝 (0:Bid.Dir G f), S.patch.usesBest S.kernel (S.connector (represent x) k.1 i):=by
    intro i; apply (he i).tendsto.eventually (S.patch.best_open.mem_nhds ?_); apply lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1); simpa [Patch.bondCost, Push.deck_zero S h _ k.1] using S.kernel.predictor_cut_pos
 exact (eventually_all.mpr fun i=> Push.threshold S i).and (eventually_all.mpr hp)
include h in
lemma ice_v (s:Signed)(k k':S.Choices): ∀ᶠ a:Directions G f in 𝓝 0,S.prediction (increment 1 a) k=S.prediction (increment 1 a) k':=by
 let Fu:=fun x:Directions G f=> Push.Uniform.tint G (Body 1 f) (link_r _ x)
 have hh : Fu (0:Directions G f)=0:=by unfold Fu; rw [map_zero,map_zero]
 have he : Tendsto Fu (𝓝 0) (𝓝 0):=hh ▸ (((Push.Uniform.tint G (Body 1 f)).continuous.comp (link_r (G:=G) f).continuous).tendsto 0 : Tendsto Fu (𝓝 0) (𝓝 (Fu 0)))
 filter_upwards [he.eventually (calmK S k h),he.eventually (calmK S k' h)] with x hx hk
 rw [←show represent (Fu x)=increment 1 x from congr_arg (increment (1:Config G _)) (arte x)]; let U:= represent (Fu x)
 funext i
 have hu:S.connector U k.1 i=S.connector U k'.1 i:=by
    funext j; simp only [StepData.connector,StepData.frames,Patch.frame]; rw [if_pos (hx.1 _),if_pos (hx.1 _),if_pos (hx.1 _),if_pos (hx.1 _)]
 unfold StepData.prediction
 rw [hu]; unfold Patch.predict; rw [if_pos (hk.2 _),if_pos (hk.2 _)]
include h in
lemma ice_b(s:Signed)(i:Bond c): blockJet (1:Config G c) k s i=blockJet (1:Config G c) k' s i:=by
 unfold blockJet; apply Filter.EventuallyEq.fderiv_eq
 let E:=ice_v h s k k'; have hf : S.prediction (increment (1: Config G f) 0) k=S.prediction (increment 1 0) k':= E.self_of_nhds
 filter_upwards [E] with y hy; unfold predictorTurn predictGroup facade; rw [replica_one]; simp only [(Oriented.carry s h k _).2, (Oriented.carry s h k' _).2]; rw [hy,hf]
end YM.CF.Neige
