import YM.CF.Souk.Bit
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
variable {X Y:Fish ι→Neige.Shelf τ}{x:Fish ι}
private lemma rapid(h:DifferentiableAt ℝ X x)(p:DifferentiableAt ℝ Y x)(v:Fin 1→ι): pS 1 (fun y=> X y*Y y) v x=X x * pS 1 Y v x+pS 1 X v x *Y x:=by
 unfold pS Uniform.entry; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]
 erw [(h.hasFDerivAt.mul' p.hasFDerivAt).fderiv]; rfl
private lemma rush(h:ContDiffAt ℝ 2 X x)(p:ContDiffAt ℝ 2 Y x)(v:Fin 2→ι):
 let a:Fin 1→ι:=fun _=>v 0; let b:Fin 1→ι:=fun _=>v 1
 pS 2 (fun y=> X y*Y y) v x=(X x*pS 2 Y v x+pS 1 X a x *pS 1 Y b x)+(pS 1 X b x*pS 1 Y a x +pS 2 X v x*Y x):=by
 intro a b
 have ha {f:Fish ι→Neige.Shelf τ}(h:ContDiffAt ℝ 2 f x): pS 2 f v x=pS 1 (pS 1 f b) a x:=by
    change Uniform.entry f x v=Uniform.entry (pS 1 f b) x a
    rw [bolt_entry (n:=1) (show ContDiffAt ℝ ((1+1:ℕ):ℕ∞ω) f x from by simpa using h),show Fin.init v=a from funext fun i=>by unfold a Fin.init; fin_cases i; rfl]; congrm Uniform.entry ?_ _ _; ext1 y; unfold Uniform.entry; rw [iteratedFDeriv_one_apply]; rfl
 have hv {f:Fish ι→Neige.Shelf τ}(h:ContDiffAt ℝ 2 f x):DifferentiableAt ℝ (pS 1 f b) x:=by
    unfold pS Uniform.entry; simp_rw [iteratedFDeriv_one_apply]; exact DifferentiableAt.clm_apply ((h.fderiv_right (m:=1) (by norm_num)).differentiableAt (by simp)) (differentiableAt_const _)
 let F:=fun y=> X y*pS 1 Y b y+(pS 1 X b y)*Y y
 have he: pS 1 (fun y=> X y*Y y) b =ᶠ[𝓝 x] F:=by
    filter_upwards [h.eventually (by simp), p.eventually (by simp)] with y hh hp; exact rapid (hh.differentiableAt (by norm_num)) (hp.differentiableAt (by norm_num)) b
 have hX:= h.differentiableAt (by norm_num); have hY:= p.differentiableAt (by norm_num)
 rw [ha (h.mul p), show pS 1 (pS 1 (fun y=>X y*Y y) b) a x=pS 1 F a x from ?_, show pS 1 F a x=pS 1 (fun y=> X y*pS 1 Y b y) a x+pS 1 (fun y=>pS 1 X b y*Y y) a x from ?_]; rw [rapid hX (hv p),rapid (hv h) hY,ha h,ha p]
 · unfold pS Uniform.entry F; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]; erw [(((hX.mul (hv p)).hasFDerivAt).add (((hv h).mul hY).hasFDerivAt)).fderiv]; rfl
 exact congr_arg (fun M:ContinuousMultilinearMap ℝ (fun _ : Fin 1=>Fish ι) (Neige.Shelf τ) => M fun j=>bolt (a j)) ((he.iteratedFDeriv ℝ 1).eq_of_nhds)
lemma Jewel.trade(h:Jewel X x C Q)(p:Jewel Y x A V): Jewel (fun y=>X y*Y y) x (4*C*A) (C*V+3*Q*A):=by
 refine ⟨(fuseN h.upper p.upper).mono (le_of_eq (by ring)), ((fuseN p.turn h.turn).mono (le_of_eq (by ring))).germ (Eventually.of_forall fun y=> by simp only [Function.comp_apply, Matrix.transpose_mul]),?_⟩
 have h₁ : ContDiffAt ℝ 2 X x:=by simpa using steep h.upper
 have h₂ : ContDiffAt ℝ 2 Y x:=by simpa using steep p.upper -- tune
 intro i hi j; interval_cases i
 · rw [rapid (h₁.differentiableAt (by norm_num)) (h₂.differentiableAt (by norm_num))]
   have hQ:0 ≤ Q:= (notes_nn _).trans (h.cents _ (by omega) j); have hA:0 ≤ A:=p.upper.nonneg; apply notes_add.trans; exact (add_le_add (buy_mul h.turn.value (p.cents _ (by decide) j)) (pay_mul (h.cents _ (by decide) j) p.upper.value)).trans (by nlinarith)
 rw [rush h₁ h₂]
 apply notes_add.trans; exact (add_le_add (notes_add.trans (add_le_add (buy_mul h.turn.value (p.cents 1 (by omega) j)) (pay_mul (h.cents 0 (by decide) _) (scaleS p.upper (i:=1) (by decide) _)))) (notes_add.trans (add_le_add (pay_mul (h.cents 0 (by omega) _) (scaleS p.upper (i:=1) (by decide) _)) (pay_mul (h.cents 1 (by omega) _) p.upper.value)))).trans_eq (by ring)
end YM.CF.Souk
