import YM.CF.Cay.Plush
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
local notation "ζ"=>Monk G S
open Matrix AnalyticBridge.RelativeLogdet.Ink Far
variable {s C D M ε:ℝ}{i: Along S}{t:Signed}{Y: Monk G S → ℝ}{p:Site c}{A: Monk SU.group S}{g:Site c→SU.group.El}{R:Directions G c→ Mast G c}{m:ℕ}{K₀ L:ℝ}
lemma tear2(E B:Type)[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B](f:B→ℝ)(h a b:E→B)(p:E)(hx:Allows n h p 1)(ht:Allows n a p 1)(hk:Allows n b p 1)(hy: Allows (n+2) f (h p) C): Allows n (fun v=> hdot f (h v) (a v) (b v)) p (2^n* (2^n*composeCost n C 1))∧ Allows n (fun v=> fderiv ℝ f (h v) (b v)) p (2^n*composeCost n C 1):=by
 have hz:= Newt.appliance (hy.slide.slide.comp hx) ht; constructor
 · refine (Newt.appliance hz hk).mono (Eq.le (by ring))
 exact (Newt.appliance ((hy.slide.order (by omega)).comp hx) hk).mono ((mul_one _).le)
lemma rebate(v:ℝ)(hx:‖A.z‖≤ v)(h:K.Funds S T)(ht:0<w)(hp:1000 ≤ radiusB x)(hl:0<s)(hr:s ≤ ε)(hr':s ≤ 1)(hg:n+4 ≤ r)(hy:separation p (herald S t i)+horn x l ≤ m*radiusB x)(hv:Lamp T s x A p g R m r)(hn: Ready T x)(hu:ShardIncome r x L K₀ w T A.key A.park A.V A.k)(H:∀ y:Mast G c,‖y‖<1→ Fire T x A.park A.k l s r C y)(HZ: |coupling β| * (v*C) ≤ s/2)(HF: KnotP (lava T A.park x A.k l t i) r (D*s) M ε)(e:Bond f): let X:=composeCost n ((D+M)*s^3) 1; Allows n (fun y=>spring (dense T x q d l β t i) e (A.atop y x)) 0 (composeCost n (2^n*X+ 2^n*(2^n*X)) (1/2)):=by
 intro X; let L':=latticeFieldEstimates S g; let P(v):= s⁻¹ • (peer T x A.park A.k q d l β s v); let Z:=arrow e A.z; let B:=L' Z; let W:= L' A.z; have he:‖W‖≤v:= (speed g A).trans hx; have hh:‖B‖≤ v:=by
    refine (speed g (rough A Z)).trans ((le_trans (b:=‖A.z‖) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_) hx)); intro i; change ‖arrow e A.z i‖≤_
    by_cases t:i=e; · subst i; unfold arrow; rw [Pi.single_eq_same]; exact norm_le_pi_norm ..
    unfold arrow; rw [Pi.single_eq_of_ne t,norm_zero]; positivity -- tune t subst
 let Y:=lava T A.park x A.k l t i; let F(v):= Y (s • v); let U(v:Mast G c):Ark T A.park:=(v,0); have hl(q:Mast G c)(hp:‖q‖<1) : Allows r F (U q) ((D+M)*s^3):= tip_a HF hl hr' (by omega) (by unfold U; rw [Prod.norm_def]; exact max_lt hp (by rw [norm_zero]; norm_num)) hr
 have hb:∀ᶠ u in 𝓝 0, spring (dense T x q d l β t i) e (A.atop u x)= (fderiv ℝ F (U (R u)) (P (R u) B))+hdot F (U (R u)) (P (R u) W) (P (R u) B)/2:=by
    filter_upwards [rays h ht hn hp hu hv H (d:=d) (q:=q) (β:=β) hy] with v he; obtain ⟨hx,hφ⟩:=he; let g:=R v; let S:= (P g).comp L'; let Q(z):= F (U g+S z); have hz:dense T x q d l β t i∘ rough (A.atop v x)= Q:=by
       rw [hφ]; funext j; change _= F (U g + P g (L' j)); unfold F P; rw [_root_.smul_apply, smul_add,smul_inv_smul₀ (?_ : s≠0),show s • U g=north T A.park s g from Prod.ext rfl (smul_zero ..)]; exact (show 0<s by assumption).ne'
    obtain ⟨h1,-⟩:= ash_l S (U g) Z F (((hl _ hx).order (show 2≤r by omega)).smooth); obtain ⟨-,h2⟩:= ash_l S (U g) A.z F (((hl _ hx).order (show 2≤r by omega)).smooth); change fderiv ℝ _ 0 Z+ hdot (dense T x q d l β t i∘ rough (A.atop v x)) 0 A.z Z/2= _; rw [hz]; exact congrArg₂ (· + ·) h1 (congrArg (fun (y:Directions G f→L[ℝ] ℝ)=> y Z/2) h2) -- tune
 let x':=R 0; have hQ: ‖x'‖<1:=hv.stage.value.trans_lt (by norm_num); have hG:Allows n U x' 1:= (allows_linear (L:=ContinuousLinearMap.id ℝ _) ContinuousLinearMap.norm_id_le hQ.le).pair (allows_const _ (show ‖(0:Fish (Key A.park G))‖ ≤ 1 from by rw [norm_zero]; norm_num)) -- tune
 have hhK (z:Directions G f)(hp:‖z‖≤ v): Allows n (fun q=> P q z) x' 1:=by
    have h':=hl; have hl:0<s:=by assumption
    refine (((radion (β:=β) (d:=d) (q:=q) (H x' hQ) hp).order (show n≤r by omega)).smul s⁻¹).mono ?_; rw [abs_of_nonneg (inv_nonneg.mpr hl.le),inv_mul_le_iff₀ hl,mul_one]; linarith only [HZ, hl]
 obtain ⟨h1,h2⟩:=tear2 _ _ F U (fun q=> P q W) (fun q=>P q B) x' hG (hhK W he) (hhK B hh) ((hl _ hQ).order (show n+2 ≤ r by omega)); apply (((h2.add ((h1.smul ((2:ℝ)⁻¹)).mono (mul_le_of_le_one_left h1.nonneg (by norm_num)))).comp (f:=R) (hv.stage.order (show n≤r by omega))).germ)
 filter_upwards [hb] with v hp'; rw [hp',smul_eq_mul]; ring
end YM.CF.Cay
