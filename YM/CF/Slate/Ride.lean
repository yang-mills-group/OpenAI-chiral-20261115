import YM.CF.Slate.Spool
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
variable {z:E→A}{D s C M:ℝ}{n k i:ℕ}
lemma tip_a {x:E}(p:KnotP z n (D*s) C M)(ht:0<s)(hy:s ≤  1)(hn:3  ≤  n)(hv:‖x‖<1)(hs:s  ≤  M):Allows n (fun x=> z (s • x)) x ((D+C)*s^3):=by
 let L:= s • ContinuousLinearMap.id ℝ E; let f:=z ∘ L; have he:=p.sails; have hM:=ht.trans_le hs; have hL:‖L‖ ≤  s:=pole0 s E E ht.le
 have h{x:E}(hv:‖x‖<1):Allows n z (L x) C:= he _ (((L.le_opNorm x).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))).trans_lt ((mul_lt_of_lt_one_right ht hv).trans_le hs))
 let q':= (D+C)*s^3; have hD:0 ≤ D:= nonneg_of_mul_nonneg_left ((norm_nonneg _).trans p.cap) ht; have hC:0 ≤  C:=(h hv).nonneg; have hp:0  ≤  q':=by unfold q'; positivity
 have hf(y:E)(hv:‖y‖<1):ContDiffAt ℝ (↑n) f y:=(h hv).smooth.comp _ L.contDiff.contDiffAt
 have hh(y:E)(hv:‖y‖<1)(i:ℕ)(hu:3 ≤ i)(hi:i ≤ n) :‖iteratedFDeriv ℝ i f y‖ ≤  C*s^3:=by
    unfold f; rw [Push.Uniform.iter_lin_at ((h hv).smooth.of_le (Nat.cast_le.mpr hi))]; refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_; rw [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul ((h hv).norm_le _ hi) ((pow_le_pow_left₀ (norm_nonneg _) hL _).trans (pow_le_pow_of_le_one ht.le hy hu)) (by positivity) hC
 have hg:{i:ℕ}→i+1 ≤ n→∀ q:ℝ,(∀ y:E, ‖y‖<1→‖iteratedFDeriv ℝ (i+1) f y‖ ≤ q)→∀ y:E,‖y‖<1→‖iteratedFDeriv ℝ i f y‖  ≤  ‖iteratedFDeriv ℝ i f 0‖ + q :=by
    intro i he q hp v hv; let F(y:E):= iteratedFDeriv ℝ i f y; have hx: (0:E) ∈ Metric.ball 0 1:=by simp
    have hg(y:E)(hy:y∈Metric.ball 0 1):DifferentiableAt ℝ F y:= (hf _ (mem_ball_zero_iff.mp hy)).differentiableAt_iteratedFDeriv (m:=i) (by exact_mod_cast he)
    have he:=Convex.norm_image_sub_le_of_norm_fderiv_le (f:=F) (𝕜:=ℝ) hg (fun i p=>(norm_fderiv_iteratedFDeriv ..).le.trans (hp i (mem_ball_zero_iff.mp p))) (convex_ball ..) hx (mem_ball_zero_iff.mpr hv)
    have hq:0 ≤  q:=(norm_nonneg _).trans (hp 0 (by simp)); rw [sub_zero] at he
    exact (norm_le_norm_sub_add (F v) (F 0)).trans (by linarith [mul_le_of_le_one_right hq hv.le])
 have how:‖(0:E)‖<1:=by simp
 have hx(i)(p':i ≤ 2): iteratedFDeriv ℝ i f 0=(iteratedFDeriv ℝ i z 0).compContinuousLinearMap (fun j:Fin i=> L):=by unfold f; rw [Push.Uniform.iter_lin_at ((h how).smooth.of_le (by exact_mod_cast (p'.trans (show _ by omega)))),map_zero]
 have h₂(y:E)(hv:‖y‖<1): ‖iteratedFDeriv ℝ 2 f y‖ ≤  q':=by
    apply (hg hn _ (fun u hv=> hh u hv _ le_rfl hn) _ hv).trans; rw [hx _ le_rfl]; apply add_le_add_left ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_) _ |>.trans_eq (show (D*s)*s^2+C*s^3=q' from by unfold q'; ring) -- tune
    rw [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul p.cap (pow_le_pow_left₀ (norm_nonneg _) hL _) (by positivity) (mul_nonneg hD ht.le)
 have hz(i:ℕ)(h:i<2): iteratedFDeriv ℝ i f 0=0:=by rw [hx _ h.le,p.peak i h]; ext; rfl
 have h₁(y:E)(hv:‖y‖<1): ‖iteratedFDeriv ℝ 1 f y‖ ≤  q':=by have he:=hg (show 1+1 ≤ n by omega) _ h₂ _ hv; rwa [hz _ one_lt_two,norm_zero,zero_add] at he
 refine ⟨hf x hv,fun i hi=>?_⟩; rcases i with _|_|_|i' -- syntax
 · have he:=hg (show 0+1 ≤ n by omega) _ h₁ _ hv; rw [hz _ (by omega),norm_zero,zero_add] at he; exact he
 · exact h₁ _ hv
 · exact h₂ _ hv
 exact (hh x hv _ (by omega) hi).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hD) (pow_nonneg ht.le _))
local notation "G" => SU.group
lemma tinPaid(P:Patch)(K:Teller G)(p:P.Branches K.bind G)(n l:ℕ)(hn:3  ≤  n)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)) :∃ C ε:ℝ,0<C∧0<ε∧ ∀ᶠ x in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F →∀ (g:S.Choices)(u:Signed)(i:Dill S), KnotP (taste T F x g l u i) n (C*(temp x)^(l+1)) C ε:=by
 obtain ⟨e,C,D,he,hC,hD,H⟩:=gambit K P Thera.yet_one p n l hn W; obtain ⟨A,M,b,hA,hM,hb,H'⟩:= fog K Thera.yet_one P p l n hn W
 let ε:= min e b; have hε := lt_min he hb; let X:= M+ 2*C; let Z:=A+2*D; let V:=max (max X (3*M)) (max Z (3*A)); have hX:0<X:=by positivity
 have hV₁:=show X  ≤  V from (le_max_left ..).trans (le_max_left ..); have hV₂:=show Z  ≤  V from (le_max_left ..).trans (le_max_right ..); have hV₃:=show 3*M  ≤  V from (le_max_right ..).trans (le_max_left ..); have hV₄:=show 3*A  ≤  V from (le_max_right ..).trans (le_max_right ..)
 refine ⟨V,ε,hX.trans_le hV₁,hε,?_⟩; filter_upwards [H,H'] with x h H c f S T F p q g u i; obtain ⟨h1,h2,h3,h4,h5⟩:=H S T F p q g u; let t':=temp x ^(l+1); have ht:0 ≤  t':=pow_nonneg (temp_nonneg _) _
 have hy:=h _ T F p q g; have hp:2  ≤  n:=by omega
 rcases i with i|i|i|i; all_goals unfold taste
 · simp only [Sum.elim_inl,Fintype.sum_bool]; refine (( (h1 i).mono le_rfl le_rfl (min_le_right ..)).addV (( (hy _).mono le_rfl le_rfl (min_le_left ..)).addV ((hy _).mono le_rfl le_rfl (min_le_left ..)) hε hp) hε hp).mono ?_ ?_ le_rfl -- infer
   · apply le_trans (le_of_eq _) (mul_le_mul_of_nonneg_right hV₂ ht); unfold Z t'; ring
   apply le_trans (le_of_eq _) hV₁; unfold X; ring
 · refine (( (h2 i).mono le_rfl le_rfl (min_le_right ..)).addV ((hy _).mono le_rfl le_rfl (min_le_left ..)) hε hp).mono ?_ ?_ le_rfl
   · apply le_trans _ (mul_le_mul_of_nonneg_right hV₂ ht); unfold Z; change _*t'+_*t' ≤ _; nlinarith
   exact le_trans (by unfold X; linarith) hV₁
 · simp only [Sum.elim_inr, Sum.elim_inl,Fintype.sum_bool]; refine (( (h3 i).mono le_rfl le_rfl (min_le_right ..)).addV (((h4 _).addV (h4 _) hb hp).mono le_rfl le_rfl (min_le_right ..)) hε hp).mono ?_ ?_ le_rfl
   · apply le_trans (le_of_eq _) (mul_le_mul_of_nonneg_right hV₄ ht); unfold t'; ring
   exact le_trans (by linarith) hV₃
 exact (h5 i).mono (mul_le_mul_of_nonneg_right (le_trans (by linarith) hV₄) ht) (le_trans (by linarith) hV₃) (min_le_right ..)
end YM.CF.Slate
