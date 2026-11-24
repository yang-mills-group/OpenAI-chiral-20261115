import YM.CF.Tale.Petal
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable{E F G:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup G]
open Heir AnalyticBridge.SectorAffine.Offset
section
variable [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ G]
variable(f:F→ G)(g:E→F){x:E}(u v:E)
lemma audit_2 (p:ContDiffAt ℝ 2 f (g x))(q:ContDiffAt ℝ 2 g x): iteratedFDeriv ℝ 2 (f ∘ g) x ![u,v] = iteratedFDeriv ℝ 2 f (g x) ![fderiv ℝ g x u,fderiv ℝ g x v]+fderiv ℝ f (g x) (iteratedFDeriv ℝ 2 g x ![u,v]):=by
 let F' (z:E):= (fderiv ℝ f (g z)).comp (fderiv ℝ g z); have h:fderiv ℝ (f∘ g)=ᶠ[𝓝 x] F':=by
    have ht:= q.continuousAt.tendsto
    filter_upwards [q.eventually (by simp),ht.eventually (p.eventually (by simp))] with x v p; exact fderiv_comp _ (p.differentiableAt (by simp)) (v.differentiableAt (by simp))
 have he(z:ℝ):=(p.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
 have hg:=(q.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
 simp_rw [iteratedFDeriv_two_apply,h.fderiv_eq]; have hx:= (((he 0).hasFDerivAt.comp x (q.differentiableAt (by simp)).hasFDerivAt).clm_comp hg.hasFDerivAt); rw [show fderiv ℝ F' x=_ from hx.fderiv]; simp [add_comm]
variable {P:E→L[ℝ]F}{C d r η Z:ℝ}
lemma fg_L (h:∀ x, ‖x‖≤ Z→ Through 2 f x C)(p:‖g x‖ ≤ Z): ‖fderiv ℝ f (g x)-fderiv ℝ f 0‖ ≤ C * ‖g x‖:=by
 have hp:0≤Z:=(norm_nonneg _).trans p
 let F':=fderiv ℝ f; simpa only [sub_zero] using! (convex_closedBall (0:F) Z).norm_image_sub_le_of_norm_fderiv_le (f:=F') (fun z hz=> ((h _ (mem_closedBall_zero_iff.mp hz)).smooth.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)) (fun z hz=>price_two (h _ (mem_closedBall_zero_iff.mp hz)) le_rfl) (mem_closedBall_self hp) (mem_closedBall_zero_iff.mpr p)
lemma payload (h:∀ x,‖x‖ ≤ Z→Through 2 f x C)(hp:‖g x‖ ≤Z)(ho:f 0=0)(q:ContDiffAt ℝ 2 g x)(h0:‖g x‖≤ r)(h₁:‖fderiv ℝ g x u‖ ≤ d)(h₂:‖fderiv ℝ g x v‖ ≤ d)(h3:‖iteratedFDeriv ℝ 2 g x ![u,v]‖ ≤ η)(w:F)(v':ℝ)(hv:‖fderiv ℝ g x u-w‖ ≤ v') : ‖f (g x)‖ ≤ C*r ∧ ‖fderiv ℝ (f∘g) x u-fderiv ℝ f 0 w‖ ≤ (C*r*d+C*v') ∧ ‖iteratedFDeriv ℝ 2 (f ∘g) x ![u,v]‖ ≤ C*(d^2+η):=by
 have ht:=h _ hp; have hc:=ht.nonneg
 have hz:0≤ Z:=(norm_nonneg _).trans hp; have hp₀:=h (0:F) (by rw [norm_zero]; exact hz)
 refine ⟨(locate h (by norm_num) ho hp).trans (mul_le_mul_of_nonneg_left h0 hc),?_,?_⟩
 · rw [fderiv_comp x (ht.smooth.differentiableAt (by norm_num)) (q.differentiableAt (by norm_num)),ContinuousLinearMap.comp_apply]; let X:= fderiv ℝ f (g x); let Y:= fderiv ℝ f 0; let z:= fderiv ℝ g x u; rw [show X z-Y w= (X-Y) z+ Y (z-w) from (by simp)]; refine (norm_add_le ..).trans (add_le_add ?_ ?_)
   · exact ((X-Y).le_opNorm _).trans (mul_le_mul ((fg_L f g h hp).trans (mul_le_mul_of_nonneg_left h0 hc)) h₁ (norm_nonneg _) (mul_nonneg hc ((norm_nonneg _).trans h0)))
   exact (Y.le_opNorm _).trans (mul_le_mul (price_one hp₀ (by norm_num)) hv (norm_nonneg _) hc)
 rw [audit_2 f g u v ht.smooth q, mul_add]; apply (norm_add_le ..).trans (add_le_add ?_ ?_); swap; · exact ((fderiv ℝ f (g x)).le_opNorm _).trans (mul_le_mul (price_one ht (by norm_num)) h3 (norm_nonneg _) hc)
 let K:=iteratedFDeriv ℝ 2 f (g x); let z:= fderiv ℝ g x; let D:Fin 2→F:=![z u,z v]; refine (K.le_opNorm D).trans (mul_le_mul (ht.pay 2 le_rfl) ?_ (prod_nonneg fun _ _=>norm_nonneg _) hc); simp only [Fin.prod_univ_two,D,pow_two]; exact mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
end
section coupled
variable [NormedSpace ℝ E][InnerProductSpace ℝ F]
lemma duet_2 {f g:E→ F}(u v:E){x:E}(p:ContDiffAt ℝ 2 f x)(q:ContDiffAt ℝ 2 g x): iteratedFDeriv ℝ 2 (fun z=>inner ℝ (f z) (g z)) x ![u,v] = inner ℝ (iteratedFDeriv ℝ 2 f x ![u,v]) (g x) + inner ℝ (fderiv ℝ f x v) (fderiv ℝ g x u)+ inner ℝ (fderiv ℝ f x u) (fderiv ℝ g x v)+ inner ℝ (f x) (iteratedFDeriv ℝ 2 g x ![u,v]):=by
 let U(z):=inner ℝ (f z) (g z); let V: (E→L[ℝ]ℝ)→L[ℝ]ℝ:= ContinuousLinearMap.apply ℝ ℝ v -- tune
 let A t:= fderiv ℝ f t; let B t:=fderiv ℝ g t; let Z t:= V (fderiv ℝ U t); let X(t):=inner ℝ (A t v) (g t); let Y(t):=inner ℝ (f t) (B t v)
 have ht : Z=ᶠ[𝓝 x] Y+X:=by filter_upwards [p.eventually (by simp), q.eventually (by simp)] with y p q; exact fderiv_inner_apply ℝ (p.differentiableAt (by simp)) (q.differentiableAt (by simp)) v
 have h: DifferentiableAt ℝ (fderiv ℝ f) x := (p.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num); have hp: DifferentiableAt ℝ (fderiv ℝ g) x := (q.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num);
 have he:= ((p.inner ℝ q).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
 let W:(E→L[ℝ] F)→L[ℝ] F:= ContinuousLinearMap.apply ℝ F v
 have hz:= ((W.hasFDerivAt.comp x h.hasFDerivAt).inner ℝ (q.differentiableAt (by simp)).hasFDerivAt)
 have hy:= ((p.differentiableAt (by simp)).hasFDerivAt.inner ℝ (W.hasFDerivAt.comp x hp.hasFDerivAt))
 have hh : fderiv ℝ Z x=_:=(V.hasFDerivAt.comp x he.hasFDerivAt).fderiv
 rw [ht.fderiv_eq] at hh; rw [show fderiv ℝ (Y+X) x=_ from (hy.add hz).fderiv] at hh
 have hg:= (DFunLike.congr_fun hh u).symm
 simp_rw [iteratedFDeriv_two_apply]; refine hg.trans ?_; simp [W]; abel
end coupled
end YM.CF.Tale
