import YM.CF.Cay.Rosa
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
open Souk
open Matrix
open Push.Uniform (block)
variable {s C D:ℝ} {k:S.Choices}
lemma burnH {v:Mast G c}(p:Fire T x F k l s n C v): Protected n (fun y=> (μ₁ T F x k q d s l y).transpose) v C:=by
 let A:= jump_up (leaveX F x) (visitX F x) (visit_n ..) (leave_n ..) (p.flame q d).2.1; refine A.germ (Eventually.of_forall fun i=>?_); change _=paintO ((μ₁ T F x k q d s l i).transpose); unfold μ₁; rw [transpose_submatrix,tableVisit]; rfl
lemma heft (z: Directions G f): ‖nub F x z‖≤ ‖z‖:=by
 let Y:LogArray G (Active (bareStores S) x F):= fun i=>z i.val.val; let a:=visitX F x (tape.symm Y); refine (((visitX («G»:=SU.group) F x).le_opNorm (tape.symm Y)).trans ((mul_le_of_le_one_left (norm_nonneg _) (visit_n ..)).trans ?_))
 exact (loomP _).trans ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> (norm_le_pi_norm z i.val.val))
lemma heatDot_p {ι:Type} [Fintype ι](z: Fish ι):‖heatDot z‖ ≤ Souk.costU z:= by
 apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _=> abs_nonneg _); intro k; rw [HD,Real.norm_eq_abs]; unfold dotProduct; rw [sum_mul]; apply (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum _); intro i _; rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm k i)) (abs_nonneg _)
abbrev arrow(e:Bond f)(z:Directions G f):= Pi.single (M:=fun _=>SU.group.Color) e (z e)
abbrev bankU:ℝ:= Fintype.card SU.group.ColorIndex
lemma fuelL(e:Bond f)(z:Directions G f): Souk.costU (nub F x (arrow e z))≤ bankU*‖z e‖:=by
 let U:=nub F x (arrow e z); unfold Souk.costU; rw [Fintype.sum_prod_type]; change (∑ i:F.Free,∑ j:SU.group.ColorIndex, |U (i,j)|) ≤ _
 have he(i:F.Free)(hx:i.val≠e)(j:SU.group.ColorIndex):U (i,j)=0:=by change arrow e z i.val j=0; rw [arrow,Pi.single_eq_of_ne hx]; rfl
 by_cases h:e∈F.trunks
 · rw [Finset.sum_eq_zero fun i _=>Finset.sum_eq_zero fun j _=> by rw [he i (fun k=>i.property (by rw [k]; exact h)) j,abs_zero]]; unfold bankU; positivity
 let t:F.Free:=⟨e,h⟩; rw [Finset.sum_eq_single t]
 refine le_trans (Finset.sum_le_sum (g:=fun _=>‖z e‖) ?_) (by simp [bankU]); intro i _; change |Pi.single (M:=fun _=>SU.group.Color) e (z e) t.val i| ≤ _; rw [show t.val=e from rfl,Pi.single_eq_same]; exact (Real.norm_eq_abs _).symm.trans_le (PiLp.norm_apply_le (z e) i)
 · exact fun b _ p=> Finset.sum_eq_zero fun j _=>by rw [he b (fun k=> p (Subtype.ext k)) j,abs_zero]
 simp
lemma knotH(U:Config G f){v:Mast G c}(p:K.Funds S T)(h:∀ v:Mast G c, ‖v‖<1→ Fire T x F k l s n C v)(hv:‖v‖<1)(ht:0<β)(u z: Directions G f): let P(w:Mast G c):= proxZ T F x k U q d l β s w; let a:=nub F x u; let b:=nub F x z; let t:=pic T x F k l s;
 Allows n (fun w=> fderiv ℝ (P w) 0 u) v (β*coupling β* (Souk.costU a*(2^n*C*(C*s^(l+2))))) ∧ Allows n (fun w=> hdot (P w) 0 u z) v (Souk.costU b * (‖u‖* (C*s^3))) :=by
 intro P a b t; obtain hp:= h v hv; let X(w:Mast G c):=paintO (perturb (μ₁ T F x k q d s l w) (block (clipped T x F k) (t w)))
 have hX:Allows n X v (C*s^3):= (hp.flame q d).2.2.2
 have hB:Allows n (fun w=> X w a) v (‖u‖*(C*s^3)):= hX.linear (ContinuousLinearMap.apply ℝ _ a) (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun k=> (k.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (heft (F:=F) (x:=x) u) (norm_nonneg _)).trans_eq (mul_comm ..)))
 let y:= coupling β; let A:=fun w=> (μ₁ T F x k q d s l w).transpose; let B(w):=Slope (clipped T x F k) (t w)
 have hY:=airK (A:=A) (burnH hp) (show Allows n B v _ from hp.tip)
 have ht':=isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv)
 constructor
 · refine ((((hY.linear _ (heatDot_p a)).smul (-β*y)).germ ?_).mono (le_of_eq (by unfold y; rw [neg_mul,abs_neg,abs_mul,abs_of_pos ht,abs_of_pos (coupling_pos ht)])))
   filter_upwards [ht'] with i hi; rw [HD,smul_eq_mul]; exact (reflected T F x k U q d l β s i (h _ (mem_ball_zero_iff.mp hi)) p ht u z).2.1.symm
 refine ((((hB.linear _ (heatDot_p b)).smul (-1)).germ ?_).mono (le_of_eq (by norm_num))); filter_upwards [ht'] with i hi; rw [HD,neg_one_smul]; exact (reflected T F x k U q d l β s i (h _ (mem_ball_zero_iff.mp hi)) p ht u z).2.2.symm
end YM.CF.Cay
