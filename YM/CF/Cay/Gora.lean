import YM.CF.Cay.Low
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
local notation "ζ"=> Monk G S
open Matrix Far AnalyticBridge.RelativeLogdet
section
variable {ι:Type}[Fintype ι][DecidableEq ι]
lemma sd_dot (A:Matrix ι ι ℝ)(x y:Fish ι)(h:A.transpose=A): y ⬝ᵥ (A *ᵥ x)=x ⬝ᵥ (A *ᵥ y):=by rw [← dotProduct_comm (A *ᵥ x) y]; nth_rw 2 [← h]; rw [Matrix.dotProduct_transpose_mulVec]; exact dotProduct_comm .. -- tune
lemma gradN (H: Matrix ι ι ℝ)(L:E→L[ℝ] Fish ι)(D:Fish ι)(h:H.transpose=H)(x:E): HasFDerivAt (fun x=> ((D ⬝ᵥ L x) - (L x ⬝ᵥ (H*ᵥ L x))/2)) ((heatDot (D- H *ᵥ L x)).comp L) x:=by
 let Y:= (heatDot D).comp L; let X(z):=L z ⬝ᵥ (H*ᵥ L z); let K:= (paintO H).comp L; let G'(i:ι): Fish ι →L[ℝ] ℝ:= ContinuousLinearMap.proj i; let J(i):= (G' i).comp L; let V(i):=(G' i).comp K
 have he:HasFDerivAt X (∑ i:ι,(J i x • V i+ V i x • J i)) x:= by
    have hh(i:ι):HasFDerivAt (fun y=>J i y * V i y) _ x:=(J i).hasFDerivAt.mul (V i).hasFDerivAt
    exact HasFDerivAt.fun_sum fun i _=>hh i
 let M:=(heatDot (H*ᵥ L x)).comp L; have hM: ∑ i:ι,(J i x • V i+ V i x • J i)=M+M:=by
    ext y; simp only [Finset.sum_add_distrib,_root_.sum_apply,_root_.add_apply, _root_.smul_apply,smul_eq_mul]; change L x ⬝ᵥ (H*ᵥ L y)+ H*ᵥ L x ⬝ᵥ L y = heatDot _ _+ heatDot _ _; rw [HD,sd_dot H _ _ h,dotProduct_comm (L y) (H *ᵥ L x)]; rfl -- maybe rew wrong
 have HH: ((heatDot (D- H *ᵥ L x)).comp L)= Y-M:=by ext i; simp only [Y,M,ContinuousLinearMap.comp_apply,HD,sub_dotProduct,_root_.sub_apply]
 rw [HH]; rw [hM] at he; have ht: Y-(2:ℝ)⁻¹ • (M+M)= Y-M:=by module
 rw [← ht]; apply (Y.hasFDerivAt.sub (he.const_smul ((2:ℝ)⁻¹))).congr_of_eventuallyEq; filter_upwards with i; change _=heatDot D (L i)- (2:ℝ)⁻¹ * _; rw [HD]; unfold X; ring
lemma pointA (H:Matrix ι ι ℝ)(L:E→L[ℝ] Fish ι)(D:Fish ι)(h:H.transpose=H)(u v:E): strut (fun x=> (D ⬝ᵥ L x)-(L x ⬝ᵥ (H *ᵥ L x))/2) u v=D ⬝ᵥ L u- (L u ⬝ᵥ (H *ᵥ L v))/2:=by
 let f(x:E):= (D ⬝ᵥ L x)-(L x ⬝ᵥ (H *ᵥ L x))/2; have hf:ContDiff ℝ (2:ℕ) f:=by
    let P:= (paintO H).comp L; let u(i:ι): Fish ι→L[ℝ] ℝ:= ContinuousLinearMap.proj i; have hp:ContDiff ℝ (2:ℕ) (fun x:E=> L x ⬝ᵥ (H *ᵥ L x)):= ContDiff.sum fun i _=>((u i).comp L).contDiff.mul ((u i).comp P).contDiff; unfold f; simp_rw [← HD D]; exact (((heatDot D).comp L).contDiff.sub (hp.div_const _))
 change fderiv ℝ f 0 u + hdot f 0 v u/2= _; rw [hdot, Souk.tierX f v u hf.contDiffAt]; let M:= (heatDot (L u)).comp ((paintO H).comp L); have he:(fun x=> fderiv ℝ f x u)=fun x=> D ⬝ᵥ L u-M x:=by
    funext x; rw [(gradN H L D h x).fderiv]; simp only [ContinuousLinearMap.comp_apply,M,HD,sub_dotProduct]; rw [dotProduct_comm (H*ᵥ _)]; rfl -- tune
 let t:E→ℝ:=fun x=> D ⬝ᵥ L u-M x; have ht : HasFDerivAt t (-M) 0:= M.hasFDerivAt.const_sub _
 rw [(gradN H L D h 0).fderiv,ContinuousLinearMap.comp_apply,HD,map_zero,mulVec_zero,sub_zero,he,ht.fderiv]; change _+(-(heatDot (L u) (H *ᵥ L v)))/2= _; rw [HD]; ring
end
section
variable {s C D ε:ℝ}{i: Along S}{t:Signed}{p:Site c}{A:Monk SU.group S}{K':ℝ}
lemma loomU (M:Monk G S)(e:Bond f): spring (adjust T x q d l β) e M= let L:=wrench M x; let D:=Dira T M.key M.park M.k q d x (M.bush x) l M.V; let W:=fullV T M.key M.park M.k q d x (M.bush x) l M.V; let z:=arrow e M.z; -(coupling β)⁻¹*(L z ⬝ᵥ D) - (L z ⬝ᵥ (W *ᵥ L M.z))/2:=by
 let L:=wrench M x; let D:=Dira T M.key M.park M.k q d x (M.bush x) l M.V; let P:=fullV T M.key M.park M.k q d x (M.bush x) l M.V; let g:=coupling β
 have ht:P.transpose=P:=by unfold P fullV perturb fuseQ baseX Rows.gram; simp [Matrix.mul_assoc]
 have hp:adjust T x q d l β ∘ rough M =(fun z=> ((-g⁻¹) • D) ⬝ᵥ L z-(L z ⬝ᵥ (P *ᵥ L z))/2):=by
    funext z; change -g⁻¹*(D ⬝ᵥ L z)+ (-(L z ⬝ᵥ (P *ᵥ L z))/2)=_; rw [smul_dotProduct,smul_eq_mul]; ring
 change strut _ (arrow e M.z) M.z= _; rw [show adjust _ _ _ _ _ _ ∘ _ = _ from hp, pointA P L _ ht]; dsimp only; rw [smul_dotProduct,smul_eq_mul,dotProduct_comm D]
lemma chalk_x(e:Bond f)(M:ζ): Souk.costU (wrench M x (arrow e M.z)) ≤ bankU*‖M.z‖:=by
 let R:=wrench M x (arrow e M.z); unfold Souk.costU; rw [Fintype.sum_prod_type]; let m(i:M.zoo x):ℝ:=∑ j:SU.group.ColorIndex,|R (i,j)|; have ht (i:M.zoo x)(p:i.val.val ≠ e):m i= 0:=by refine Finset.sum_eq_zero fun j _=>?_ ; change |arrow e M.z i.val.val j|=_; rw [arrow,Pi.single_eq_of_ne p]; exact abs_zero
 by_cases h:∃ i:M.zoo x,i.val.val=e; change (∑ i:M.zoo x,m i)≤ _
 · obtain ⟨i,h⟩:= h; rw [sum_eq_single i]
   · rw [show bankU*‖M.z‖=(∑ j:SU.group.ColorIndex,‖M.z‖) from by simp [bankU]]; refine Finset.sum_le_sum fun j _=>?_ ; change |arrow e M.z i.val.val j|≤_; rw [h,arrow,Pi.single_eq_same]; exact ((Real.norm_eq_abs _).symm.trans_le (PiLp.norm_apply_le _ _)).trans (norm_le_pi_norm ..)
   · exact fun j _ p=>ht j fun hj=>p (Subtype.ext (Subtype.ext (hj.trans h.symm)))
   simp
 push Not at h; change (∑ i:M.zoo x,m i)≤ _; rw [sum_eq_zero fun i _=>ht i (h i)]; unfold bankU; positivity -- tune
lemma terra(e:Bond f)(v:ℝ)(hx:‖A.z‖≤v)(hp:MossX n l x A.key A.park T A.V A.k C d D q): let X:=bankU*v; Allows n (fun i=> spring (adjust T x q d l β) e (A.atop i x)) 0 (|coupling β|⁻¹ * (X* (C*(aimC x*D^2)))+ X*(2^n*(C*lamp x)*v)):=by
 intro X; let U:=Vmove x A.V; let K:= (A.bush x); let J(i):= (A.atop i x); let W(i):= paintO (fullV T A.key A.park A.k q d x K l (U i)); let R:= Dira T A.key A.park A.k q d x K l ∘ U; let z:=wrench A x (arrow e A.z); let Z:=wrench A x A.z; have hZ: ‖Z‖≤ v:= by let z:= loomP (A.bell x); exact z.trans ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hx)).mpr fun i=> (norm_le_pi_norm A.z i.val.val).trans hx)
 obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:=hp.jumps K; have hz: ‖heatDot z‖≤ X:= (heatDot_p ..).trans ((chalk_x (x:=x) e A).trans (mul_le_mul_of_nonneg_left hx (by unfold bankU; positivity)))
 let r:=coupling β; let a:= X*(C*(aimC x * D^2)); have he : Allows n (fun i=> -r⁻¹ • heatDot z (R i)) 0 (|r|⁻¹*a):=by refine (((h4.linear _ hz).smul (-r⁻¹)).mono (le_of_eq (by rw [abs_neg,abs_inv]))) -- tune
 let b:=X*(2^n*(C*lamp x)*v); have hb:Allows n (fun i=> heatDot z (W i Z)) 0 b:= (Newt.appliance (show Allows n W 0 _ from h6) (allows_const _ hZ)).linear _ hz
 refine ((subtract_p he (((hb.smul ((2:ℝ)⁻¹)).mono (mul_le_of_le_one_left hb.nonneg (by norm_num))))).germ ?_); filter_upwards with i; rw [HD, HD, loomU (A.atop i x) e]; change _*_-(2:ℝ)⁻¹ * (z ⬝ᵥ W i Z)=-r⁻¹ * (z ⬝ᵥ R i) - (z ⬝ᵥ W i Z)/2; ring
end
end YM.CF.Cay
