import YM.CF.Hest.Zen
import YM.CF.Hest.Cup
import YM.CF.Hest.Poet
import YM.CF.Hest.Vera
import YM.CF.Hest.Gust
import YM.CF.Hest.Foy
import YM.CF.Hest.Hull
import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C:ℝ}
open Newt Hors Souk
open RG Pressure Push AnalyticBridge.LocalGaussianLaws
local notation "GG"=>group
variable{T:Roam m X B}{c b a r w σ:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{A:Haze m X B G e}{n:ℕ}{k':T.Choices}{U:nomA m X B→ Op (Single (CSide m B))}
section
lemma lift_e{E M:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup M][NormedSpace ℝ M]{K:E→M} (h:∀ i:E, ‖i‖<1→ Allows n (fun y:E=> K (u • y)) i C)(t:0<a)(p:a ≤ u)(g:Allows 2 (fun y:E=>K (a•y)) 0 b)(hp:3 ≤ n)(x:E)(hv:‖x‖<1) : Allows n (fun y=>K (a•y)) x (3*b+C*(a/u)^3):=by
 let W:=a/u; have ht:0<W:=div_pos t (t.trans_le p); have he:W ≤ 1:= (div_le_one (t.trans_le p)).2 p
 let L:= W • (ContinuousLinearMap.id ℝ E); let F(y:E):=K (u•y); let X(y:E):=K (a•y)
 have hL: ‖L‖ ≤ W:= Newt.pole0 W E E ht.le; have ht'(y:E)(hy:‖y‖<1):= h (L y) (show ‖L y‖<1 from (L.le_opNorm _).trans_lt (lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hL.trans he)) hy))
 have h0:X=F∘ L:= by funext y; change _=K (u •(W•y)); rw [smul_smul,show u*W=a from (by unfold W; field_simp [ne_of_gt (t.trans_le p)])]
 have hs(y:E)(hy:‖y‖<1): ContDiffAt ℝ n X y:=h0.symm ▸ (show ContDiffAt ℝ n (F∘ L) y from (ht' y hy).smooth.comp _ L.contDiff.contDiffAt)
 have hQ(i:ℕ)(h:i+1 ≤ n)(y:E)(η:ℝ)(v:‖y‖<1)(p:∀ z:E, ‖z‖<1→ ‖iteratedFDeriv ℝ (i+1) X z‖ ≤ η) : ‖iteratedFDeriv ℝ i X y‖ ≤ ‖iteratedFDeriv ℝ i X 0‖ +η:=by
    let F(z:E):= iteratedFDeriv ℝ i X z; have hx: (0:E) ∈ Metric.ball 0 1:=by simp
    have hg(z:E)(hy:z∈Metric.ball 0 1):DifferentiableAt ℝ F z:= (hs _ (mem_ball_zero_iff.mp hy)).differentiableAt_iteratedFDeriv (m:=i) (by exact_mod_cast h)
    have he:=Convex.norm_image_sub_le_of_norm_fderiv_le (f:=F) (𝕜:=ℝ) hg (fun i q=>(norm_fderiv_iteratedFDeriv ..).le.trans (p i (mem_ball_zero_iff.mp q))) (convex_ball ..) hx (mem_ball_zero_iff.mpr v)
    have hq:0 ≤ η:=(norm_nonneg _).trans (p 0 (by simp)); rw [sub_zero] at he
    exact (norm_le_norm_sub_add (F y) (F 0)).trans (by linarith [mul_le_of_le_one_right hq v.le])
 let S:=C*W^3; let Y(i:ℕ)(r:ℝ):=∀ y:E, ‖y‖<1→ ‖iteratedFDeriv ℝ i X y‖ ≤ r
 have hh(i:ℕ)(hi:3≤ i)(hp:i≤n):Y i S:=by
    intro y hy; rw [h0, Uniform.iter_lin_at (((ht' y hy).order hp).smooth)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; rw [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul ((ht' y hy).norm_le _ hp) ((pow_le_pow_left₀ (norm_nonneg _) hL _).trans (pow_le_pow_of_le_one ht.le he hi)) (by positivity) (ht' y hy).nonneg
 have hx(y:E)(hy:‖y‖<1)(i:ℕ)(h:i≤2)(N:ℝ)(p:Y (i+1) N):‖iteratedFDeriv ℝ i X y‖ ≤ b+N:=(hQ i (by omega) y N hy p).trans (add_le_add_left (g.norm_le i h) _)
 have h₂: Y 2 (b+S):=fun y hy=>hx y hy _ le_rfl S (hh _ le_rfl hp)
 have h₁: Y 1 (b+(b+S)):=fun y hy=>hx y hy _ (by omega) _ h₂
 have hb:=g.nonneg
 refine ⟨hs x hv, fun i hi=>?_⟩; rcases i with _|_|_|j' -- tune
 · exact (hx x hv 0 (by omega) _ h₁).trans (by unfold S W; linarith)
 · exact (h₁ x hv).trans (by unfold S W; linarith)
 · exact (h₂ x hv).trans (by unfold S W; linarith)
 exact (hh _ (by omega) hi _ hv).trans (le_add_of_nonneg_left (by linarith))
end
end YM.CF.Hest
