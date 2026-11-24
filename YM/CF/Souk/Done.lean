import YM.CF.Souk.Dor
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
lemma fasta_p(h:DifferentiableAt ℝ X x)(p:DifferentiableAt ℝ Y x)(v:Fin 1→ι): pS 1 (fun y=> X y*Y y) v x=X x * pS 1 Y v x+pS 1 X v x *Y x:=by
 unfold pS Uniform.entry; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]
 erw [(h.hasFDerivAt.mul' p.hasFDerivAt).fderiv]; rfl
lemma speer_m(h:ContDiffAt ℝ 2 X x)(p:ContDiffAt ℝ 2 Y x)(v:Fin 2→ι):
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
    filter_upwards [h.eventually (by simp), p.eventually (by simp)] with y hh hp; exact fasta_p (hh.differentiableAt (by norm_num)) (hp.differentiableAt (by norm_num)) b
 have hX:= h.differentiableAt (by norm_num); have hY:= p.differentiableAt (by norm_num)
 rw [ha (h.mul p), show pS 1 (pS 1 (fun y=>X y*Y y) b) a x=pS 1 F a x from ?_, show pS 1 F a x=pS 1 (fun y=> X y*pS 1 Y b y) a x+pS 1 (fun y=>pS 1 X b y*Y y) a x from ?_]; rw [fasta_p hX (hv p),fasta_p (hv h) hY,ha h,ha p]
 · unfold pS Uniform.entry F; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]; erw [(((hX.mul (hv p)).hasFDerivAt).add (((hv h).mul hY).hasFDerivAt)).fderiv]; rfl
 exact congr_arg (fun M:ContinuousMultilinearMap ℝ (fun _ : Fin 1=>Fish ι) (Neige.Shelf τ) => M fun j=>bolt (a j)) ((he.iteratedFDeriv ℝ 1).eq_of_nhds)
abbrev Typed(S:Neige.Shelf τ)(C M:ℝ): Prop:= ‖paintO S‖ ≤ C ∧∀ V:Neige.Shelf τ, |(S*V).trace| ≤ M*‖paintO V‖
variable {S H V':Neige.Shelf τ}{d M:ℝ}
lemma mul_op (h: ‖paintO H‖ ≤ C)(p: ‖paintO S‖ ≤ A): ‖paintO (H*S)‖ ≤ C*A:=by rw [paint_mul]; apply (ContinuousLinearMap.opNorm_comp_le _ _).trans; exact mul_le_mul h p (norm_nonneg _) ((norm_nonneg _).trans h)
lemma wep(P: Typed S C M)(h: ‖paintO H‖ ≤ A)(hp:0 ≤ M): Typed (S*H) (C*A) (M*A):=by
 refine ⟨mul_op P.1 h, fun V=>?_⟩; rw [Matrix.mul_assoc]; exact (P.2 (H*V)).trans ((mul_le_mul_of_nonneg_left (mul_op h le_rfl) hp).trans_eq (mul_assoc ..).symm)
lemma wel(P:Typed S C M)(h:‖paintO H‖ ≤ A)(hp:0 ≤ M): Typed (H*S) (C*A) (M*A):=by
 refine ⟨(mul_op h P.1).trans_eq (mul_comm ..),fun V=>?_⟩; rw [← Matrix.trace_mul_cycle S V H, Matrix.mul_assoc]; -- wrong
 apply (P.2 (V*H)).trans; apply (mul_le_mul_of_nonneg_left (mul_op le_rfl h) hp).trans_eq; ring
lemma typed_Note(h: ‖paintO S‖ ≤ C)(hp: notesP S ≤ M):Typed S C M:= ⟨h, fun V=> (fee_abs _).trans (pay_mul hp le_rfl)⟩
lemma typed_a(P:Typed S C M)(h:Typed H A D):Typed (S+H) (C+A) (M+D):= ⟨by rw [map_add]; exact (norm_add_le ..).trans (add_le_add P.1 h.1),fun i=> by rw [Matrix.add_mul, Matrix.trace_add,add_mul]; exact (abs_add_le ..).trans (add_le_add (P.2 _) (h.2 _))⟩
lemma typed_e(h:Typed S C M)(p:C ≤ A)(ht:M ≤ Q): Typed S A Q:= ⟨h.1.trans p,fun i=> (h.2 i).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))⟩
structure Vital(X:Fish ι→Neige.Shelf τ)(x: Fish ι)(C M:ℝ) :Prop where
 smooth:ContDiffAt ℝ 2 X x
 reader: ‖paintO (X x)‖≤ C
 chargeM: 0 ≤ M
 paidP(i:ℕ):i<2→∀ j:Fin (i+1)→ι, Typed (pS (i+1) X j x) C M
variable {P Q':Fish ι→Neige.Shelf τ}{B₀ S₀:ℝ}
lemma Vital.cap(p:Vital X x C Q)(h:C ≤ B₀)(ht:Q ≤ D): Vital X x B₀ D:= ⟨p.smooth,p.reader.trans h,p.chargeM.trans ht,fun i hi j=> typed_e (p.paidP i hi j) h ht⟩
lemma Vital.lit(h:Vital X x C Q)(ht:Vital Y x D M): Vital (fun y=> X y*Y y) x (4*C*D) (M*C+3*Q*D):=by
 have hp:0≤ Q:=h.chargeM; have hM:0≤M:=ht.chargeM; have hv:0≤C:=(norm_nonneg _).trans h.reader; have hf:0≤ D:=(norm_nonneg _).trans ht.reader
 refine ⟨h.smooth.mul ht.smooth,(mul_op h.reader ht.reader).trans (by nlinarith),by positivity,?_⟩; intro i hi j; interval_cases i
 · rw [fasta_p (h.smooth.differentiableAt (by norm_num)) (ht.smooth.differentiableAt (by norm_num))]
   exact typed_e (typed_a (wel (ht.paidP 0 (by decide) _) h.reader hM) (wep (h.paidP 0 (by decide) _) ht.reader hp)) (by nlinarith) (by nlinarith)
 rw [speer_m h.smooth ht.smooth]; exact typed_e (typed_a (typed_a (wel (ht.paidP 1 (by decide) _) h.reader hM) (wep (h.paidP 0 (by decide) _) (ht.paidP 0 (by decide) _).1 hp)) (typed_a (wep (h.paidP 0 (by decide) _) (ht.paidP 0 (by decide) _).1 hp) (wep (h.paidP 1 (by decide) _) ht.reader hp))) (by nlinarith) (by nlinarith)
end YM.CF.Souk
