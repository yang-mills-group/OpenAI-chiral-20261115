import YM.CF.Arena.Petal
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
section
variable {p k r:ℕ} {C V s:ℝ} {R: SpaceX G c}{o:Site c}
abbrev vatP (p k n:ℕ)(C V s:ℝ):ℝ:= ((k+1:ℕ):ℝ)*(n.factorial:ℝ)*(V*s^p) + C*s^(k+1)
lemma Urge.gem {x:InputZ G c}(h: Urge R o p k r n σ C V)(hx:‖x‖<1)(hs:0<s)(hu:s≤1)(hV:s≤σ)(hp:k<n)(hk:p ≤ k): Allows n (fun x=> satX R (s • x)) x (vatP p k n C V s):=by
 let L:= s • ContinuousLinearMap.id ℝ (InputZ G c); have hL:‖L‖ ≤ s:=pole0 s (InputZ G c) (InputZ G c) hs.le -- tune
 let H:=satX R; let f:= H∘ L; have h(i: InputZ G c)(hs':‖i‖<1): Allows n H (L i) C:= (show Urge R o p k r n σ C V by assumption).1.ledger _ (((L.le_opNorm i).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))).trans_lt ((mul_lt_of_lt_one_right hs hs').trans_le hV))
 have he(i:InputZ G c)(hs:‖i‖<1):ContDiffAt ℝ (n:ℕ∞ω) f i:= (h i hs).smooth.comp _ L.contDiff.contDiffAt
 have ha(y:InputZ G c)(hs:‖y‖<1)(i:ℕ)(u:i≤n):‖iteratedFDeriv ℝ i f y‖≤ ‖iteratedFDeriv ℝ i H (L y)‖*s^i:=by unfold f; rw [Push.Uniform.iter_lin_at (L:=L) (((h y hs).order u).smooth)]; refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_; rw [prod_const, card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL _) (norm_nonneg _)
 have hD:0 ≤ C:=(h _ hx).nonneg; have hU:= (show Urge R o p k r n σ C V by assumption); have hq: 0 ≤ V:= (norm_nonneg _).trans (hU.2.2 k hk le_rfl)
 let Y:= (n.factorial:ℝ)*(V*s^p); let W:=C*s^(k+1); have hB:0 ≤ Y:=by unfold Y; positivity
 have hx(i)(u:i < p):iteratedFDeriv ℝ i H 0=0:= hU.2.1 i u
 have hG(i:ℕ)(hr:i ≤ k): ‖iteratedFDeriv ℝ i f 0‖ ≤ Y:=by
    apply (ha (0:InputZ G c) (by simp) _ (by omega)).trans; rw [map_zero]
    by_cases ht:i<p; · rw [hx i ht,norm_zero,zero_mul]; exact hB
    have he: ‖iteratedFDeriv ℝ i H 0‖ ≤ (n.factorial:ℝ)*V:=by
       have hp:=hU.2.2 i (by omega) hr; unfold cake at hp; rw [norm_smul,Real.norm_of_nonneg (by positivity)] at hp
       refine (inv_mul_le_iff₀ (show 0<(i.factorial:ℝ) by positivity)).mp hp|>.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.factorial_le (by omega))) hq)
    exact le_trans (mul_le_mul he (pow_le_pow_of_le_one hs.le hu (show p ≤ i by omega)) (pow_nonneg hs.le _) (mul_nonneg (Nat.cast_nonneg _) hq)) (le_of_eq (by unfold Y; ring))
 have low(i:InputZ G c)(u:‖i‖<1)(l:ℕ)(p:k+1 ≤ l)(hL:l≤ n): ‖iteratedFDeriv ℝ l f i‖≤ W:= (ha i u l hL).trans (mul_le_mul ((h i u).norm_le _ hL) (pow_le_pow_of_le_one hs.le hu p) (pow_nonneg hs.le _) hD)
 have hg:{i:ℕ}→i+1 ≤ n→∀ q:ℝ,(∀ y:InputZ G c, ‖y‖<1→‖iteratedFDeriv ℝ (i+1) f y‖ ≤ q)→∀ y:InputZ G c,‖y‖<1→‖iteratedFDeriv ℝ i f y‖ ≤ ‖iteratedFDeriv ℝ i f 0‖ + q:=by
    intro i he' q hp v hv; let F(y:InputZ G c):= iteratedFDeriv ℝ i f y; have hx: (0:InputZ G c) ∈ Metric.ball 0 1:=by simp
    have hg(y:InputZ G c)(hy:y∈Metric.ball 0 1):DifferentiableAt ℝ F y:= (he _ (mem_ball_zero_iff.mp hy)).differentiableAt_iteratedFDeriv (m:=i) (by exact_mod_cast he')
    have he:=Convex.norm_image_sub_le_of_norm_fderiv_le (f:=F) (𝕜:=ℝ) hg (fun i p=>(norm_fderiv_iteratedFDeriv ..).le.trans (hp i (mem_ball_zero_iff.mp p))) (convex_ball ..) hx (mem_ball_zero_iff.mpr hv)
    have hq:0 ≤ q:=(norm_nonneg _).trans (hp 0 (by simp)); rw [sub_zero] at he
    exact (norm_le_norm_sub_add (F v) (F 0)).trans (by linarith [mul_le_of_le_one_right hq hv.le])
 have hi(m):∀ y:InputZ G c, ‖y‖ < 1→ ∀ j, j+m=k+1→ ‖iteratedFDeriv ℝ j f y‖ ≤ m*Y+W:=by
    induction m with
    | zero=> intro y p j h; rw [show j=k+1 from by omega]; simpa using low y p (k+1) le_rfl (by omega)
    | succ m ih=> intro y p j h; have hh:j+1 ≤ n:=by omega
                  apply (hg hh ((m:ℝ)*Y+W) (fun i p=> ih i p (j+1) (by omega)) y p).trans; exact (add_le_add (hG _ (by omega)) le_rfl).trans (le_of_eq (by push_cast; ring))
 have hp'': vatP p k n C V s=(↑(k+1:ℕ):ℝ)*Y+ W:=by unfold vatP Y W; ring
 rw [hp'']; have hvx: ‖x‖<1:=by assumption
 refine ⟨he _ hvx,fun i u=>?_⟩; by_cases ht:k+1 ≤ i; · exact (low _ hvx _ ht u).trans (le_add_of_nonneg_left (by positivity))
 let a:= k+1-i; exact (hi a _ hvx _ (by omega)).trans (add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) hB) le_rfl)
end
end YM.CF.Arena
