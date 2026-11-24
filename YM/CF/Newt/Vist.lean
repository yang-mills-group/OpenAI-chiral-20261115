import YM.CF.Newt.Tree
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ E: Type} [NormedAddCommGroup E][NormedSpace ℝ E] [Fintype ι] [Fintype τ] {C D v K d N X U s r a e:ℝ}{n:ℕ}
open Next.SectorChange (panels shots)
open Next.SectorChange.Rows (gram)
variable {G:Gauge}{P:Patch}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
lemma paint_mul (A B: Matrix ι ι ℝ): paintO (A*B)=(paintO A).comp (paintO B):=by ext1 v; exact (mulVec_mulVec ..).symm
lemma paint_one [DecidableEq ι]: paintO (1: Matrix ι ι ℝ)=ContinuousLinearMap.id ℝ _:=by ext1 v; exact one_mulVec ..
lemma jump_up {ι' ι : Type}[Fintype ι'][Fintype ι] (q : Fish ι→L[ℝ] Fish ι')(p:Fish ι'→L[ℝ] Fish ι)(hp:‖p‖ ≤ 1)(hq:‖q‖ ≤ 1){f:E→ Fish ι' →L[ℝ] Fish ι'}{x:E}(h:Allows n f x C):Allows n (fun y=> (p.comp (f y)).comp q) x C:=by
 let F:= (ContinuousLinearMap.compL ℝ (Fish ι) (Fish ι') (Fish ι)).flip q
 let Q:= (ContinuousLinearMap.compL ℝ (Fish ι') (Fish ι') (Fish ι)) p
 have hf: ‖F‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [one_mul]; exact (ContinuousLinearMap.opNorm_comp_le x q).trans (mul_le_of_le_one_right (norm_nonneg _) hq))
 have hh : ‖Q‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [one_mul]; exact (ContinuousLinearMap.opNorm_comp_le p x).trans (mul_le_of_le_one_left (norm_nonneg _) hp))
 exact (h.linear (F.comp Q) ((F.opNorm_comp_le _).trans (mul_le_one₀ hf (norm_nonneg _) hh))).mono (one_mul _).le

def gall (R:Tube G T)(x:ℝ)(k:T.Choices)(F:Forest T.ratio)(B:Mast G c): Fish (Key F G) →L[ℝ] Fish (Key F G):=
 let V:=field (1:Config G c) (reader G c (hull G c B))
 let P:=panels (G:=G) (x:=x) (bareStores T) F
 let W:=gram R x V k (shots T x) (bareStores T) F
 paintO (((panelPi P W 0).transpose).submatrix (pageX F x) (pageX F x))
open FreeResolvent.TestD (drain)
lemma gallery(F:Forest T.ratio)(x:ℝ)(k:T.Choices)(B:Mast G c) (he:Estimate n d v r e K (bareStores T) F R x (1:Config G c) k (reader G c (hull G c B)))(h:0<d)(hz:0≤K)(hp:‖B‖≤1):
 Allows n (gall R x k F) B (composeCost n (activation G n 0 d*K) (Uniform.shade G)):=by
 let H:= barePi R x F k; have hv :=(he.windowJets 0 le_rfl).polar hz le_rfl; rw [show drain 0=1 by unfold drain; simp,mul_one] at hv
 let f(u: Directions G c):= (paintO ((H (reader G c u)).transpose)); have ht:= (polar_cash (A:=fun b=> (H b).transpose) (hull G c B) (v:=d) hv.transpose hz h) -- tune
 have hc:Allows n (hull G c) B (Uniform.shade G):= Jet.allows_linear hull_n (((hull G c).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans hull_n))
 let L:= leaveX (G:=G) F x; let I:=visitX (G:=G) F x
 apply (jump_up L I (visit_n ..) (leave_n ..) (ht.comp hc)).germ
 filter_upwards with y
 rw [gall,tableVisit]; ext i j; rfl
lemma blemish(F:Forest T.ratio)(x:ℝ)(k:T.Choices)(he:Estimate n d v r e K (bareStores T) F R x (1:Config G c) k 0)(h:0<d)(hz:0 ≤ K):
 ‖ContinuousLinearMap.id ℝ _-(gall R x k F 0).comp (gabs R x k F 1)‖ ≤ K*Real.exp (-v*radiusB x):=by
 let W:= gram R x 1 k (shots T x) (bareStores T) F; let P:=panelPi (panels (bareStores T) F) W 0; let V:=pageX (G:=G) F x; let p:=V.symm
 have hh: W.transpose=W:=by unfold W Next.SectorChange.Rows.gram; rw [transpose_mul, transpose_transpose]
 have ht := he.deficitJets 0 le_rfl; rw [show drain 0=1 by unfold drain; simp, mul_one] at ht
 let C:= Uniform.townCost G
 let K':= K*Real.exp (-v*radiusB x)
 have hf:‖paintO ((W*P-1).transpose)‖≤ K':=by
    have hv:=polar_schur ht.transpose
    apply mtr_op (v:=d) (p:= Next.SectorChange.Wisps.front (G:=G) (bareStores T) F) _ _ h.le (mul_nonneg hz (Real.exp_pos _).le); change (FreeResolvent.native c).Schur _ _ d _ _
    simp only [pickedDeficit,panelError, profileGram,field_zero,zero_smul,add_zero] at hv; exact hv
 have hQ : ContinuousLinearMap.id ℝ _-(gall R x k F 0).comp (gabs R x k F 1) = - ((visitX F x).comp ((paintO ((W*P-1).transpose)).comp (leaveX F x))):=by
    rw [gabs,gall,(hull G c).map_zero, (reader G c).map_zero, field_zero]; change _-(paintO ((P.transpose).submatrix V V)).comp (paintO (W.submatrix V V))=_; rw [← paint_mul, ← tableVisit, transpose_sub,transpose_mul,hh, Matrix.transpose_one, submatrix_sub]; change _= -paintO ((P.transpose*W).submatrix V V-(1 : Matrix _ _ ℝ).submatrix V V); rw [← submatrix_mul_equiv (P.transpose) W V V V, map_sub, submatrix_one_equiv,paint_one,neg_sub]
 rw [hQ,norm_neg]; apply ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (visit_n ..))).trans
 exact ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (leave_n ..))).trans hf
end YM.CF.Newt
