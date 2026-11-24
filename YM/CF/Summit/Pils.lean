import YM.CF.Summit.Rail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Summit
open Function Filter Set Matrix MeasureTheory FreeResolvent TestD AnalyticBridge.RelativeLogdet Differential Ink
open Next.SectorChange.Schur (principal)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι κ X E τ : Type}[Fintype ι][Fintype κ][DecidableEq ι][NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
 {W:Mark τ X}{D:Cost X}{v:τ→E}{p:ι→ X}{q:κ→ X}{x:E}{A:E→Square ι}{H: E×ℝ→ Matrix ι κ ℝ}{α σ r C d u Y N:ℝ}{n:ℕ}
omit [Fintype ι] [DecidableEq ι] in
lemma row_pay {h:ℝ→Matrix ι κ ℝ}(p':∀ i j, IntegrableOn (fun x=>h x i j) Isle)(s : Matrix ι κ ℝ)(hv:∀ i j, s i j=∫ x in Isle,h x i j){l:List τ}(w:∀ t∈Isle, W.Rates D p q l σ C (h t)): W.Rates D p q l σ C s:=by
 constructor; intro i; simp_rw [hv, Finset.mul_sum]; let P (j:κ):= W.pay l (p i)* D.weight σ (p i) (q j)
 have he : C=(∫ _:ℝ in Isle,C):=by simp [Isle, Ink.interval]
 have hp j: IntegrableOn (fun t=>P j* |h t i j|) Isle:= ((p' i j).norm.const_mul _)
 calc
    _ ≤ ∑ j, (∫ t in Isle, P j*|h t i j|) := by
        refine Finset.sum_le_sum fun j _=>?_
        rw [integral_const_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (mul_nonneg (W.pay_pos ..).le (D.weight_nn ..))
    _ ≤ _ := by
        rw [← integral_finsetSum _ (fun j _=> hp j), he]
        refine integral_mono_ae (integrable_finsetSum _ (fun j _=>hp j)) (integrable_const C) ((ae_restrict_mem measurableSet_Icc).mono fun x hx=>?_)
        unfold P; simp_rw [mul_assoc,← Finset.mul_sum]; exact (w x hx).rows _
omit [DecidableEq ι] in
lemma cent (h:Ink.Arc H n x)(w:∀ t∈Isle, Bundle v W D p q (fun y=>H (y,t)) x n σ C) : Bundle v W D p q (fun y=>Matrix.of fun i j=>∫ t in Isle,H (y,t) i j) x n σ C:=by
 let B y:= Matrix.of fun i j=>∫ t in Isle,H (y,t) i j
 have hv(i j) : Ink.Arc (fun v=> H v i j) n x:=fun t ht=> (evaluate i j).contDiff.contDiffAt.comp _ (h t ht)
 have he:ContDiffAt ℝ n B x:= rectangle_smooth fun i j=>(hv i j).writes
 refine ⟨he,fun l hl=>?_⟩; let T t:= jet v (fun y=>H (y,t)) l x; let s:=jet v B l x; have hj (i j) : Arc (fun v=> H v i j) l.length x:=fun r hr=>smooth_of_le (hv i j r hr) hl
 have hh i j: s i j=∫ t in Isle,T t i j:= by
    unfold T s; rw [← entry v l (smooth_of_le he hl)]
    change jet v (fun y=>∫ t in Isle,H (y,t) i j) l x=_; rw [(hj i j).report]
    exact setIntegral_congr_fun measurableSet_Icc fun t ht=> entry v l (smooth_of_le (w t ht).smooth hl) i j
 have hk i j: IntegrableOn (fun t=> T t i j) Isle:=by
    let F z:= H z i j; have hy : Arc (over v F l) 0 x:=fun t ht=> over_smooth v l (by simpa using hj i j t ht)
    exact IntegrableOn.congr_fun (f:=fun t=>over v F l (x,t)) hy.int (fun t ht=>entry v l (smooth_of_le (w t ht).smooth hl) i j) measurableSet_Icc
 exact ⟨row_pay hk s hh (fun t ht=>((w _ ht).bound l hl).row),row_pay (h:=fun t=>(T t).transpose) (fun j i=> hk i j) _ (fun j i=> hh i j) fun t ht=>((w _ ht).bound l hl).col⟩
section compress
variable (I:ι→ Set ι)
def mild (A:Square ι):= (2/Real.pi) • Matrix.of fun i j=> ∫ t in Isle,pie I (spanX A t) 0 i j
lemma mild_zero (A:Square ι)(i j:ι)(hi:i ∉ I j): mild I A i j=0:=by unfold mild; simp_rw [Matrix.smul_apply,Matrix.of_apply,pie_miss _ _ _ _ _ hi]; simp
lemma mild_read (A:Square ι)(i j:ι)(hi:i ∈ I j)(hj:j∈ I j): mild I A i j= shard (principal A (I j)) ⟨i,hi⟩ ⟨j,hj⟩:=by
 unfold mild shard glassX; simp_rw [Matrix.smul_apply,Matrix.of_apply,pie_read _ _ _ _ _ hi hj,resolve,zero_smul,add_zero]; congrm _ • ?_; apply setIntegral_congr_fun measurableSet_Icc; intro t ht
 dsimp only; rw [show principal (spanX A t) (I j)= spanX (principal A (I j)) t from ?_]; unfold Next.SectorChange.Schur.principal spanX; ext; simp [Matrix.one_apply,Subtype.ext_iff]
lemma pole_run (k:Bundle v W D p p A x n σ C)(p':Gap (A x) r)(p1:0<r)(p2:0 ≤ C)(p3:Price σ (C+1) (min r 1/2) d u Y 1 n)(h: D.Volume p d Y)(ht:W.Move D d u)(hI:∀ i,i∈ I i)(hz:(study I hI).Near D p N):
 let R:= meter n n (C+1) u (rise Y (min r 1/2)); let e:=Real.exp (-(n+1:ℕ)*d*N)
 Bundle v W D p p (fun y=>shard (A y)) x n d ((2/Real.pi)*R) ∧ Bundle v W D p p (fun y=>mild I (A y)-shard (A y)) x n d (e* ((2/Real.pi)*tagPrice u n R (tagPrice u n (C+1) (Y*R)))):=by
 intro R e; let s:= (2/Real.pi); let J(z:E×ℝ):=spanX (A z.1) z.2
 have he:Ink.Arc J n x:= fun t _=> (((contDiffAt_const.sub contDiffAt_snd).pow 2).smul (k.smooth.comp (g:=A) _ contDiffAt_fst)).add ((contDiffAt_snd.pow 2).smul (g:=fun _=>1) contDiffAt_const)
 have hp (t): Gap (J (x,t)) (min r 1/2):= span_gap p' p1.le t
 have hh:= pole_paid k p' p1 p2 p3 h ht hI hz; have hw: Arc (fun z=>(J z)⁻¹) n x:= fun t hv=> reflected (he t hv) ((hp _).unit_det p3.r0); have hr:=pie_s J he hI (fun t _=> hp t) p3.r0
 have ht:= (cent hw (fun t ht=>(hh t ht).1)).scale s; rw [abs_of_pos (show 0<s from by unfold s; positivity)] at ht
 refine ⟨ht,?_⟩
 have hd:= (cent (H:=fun z=>pie I (J z) 0-(J z)⁻¹) (x:=x) (n:=n) (fun t hv=>(hr t hv).sub (hw t hv)) (fun t ht=>(hh t ht).2)).scale s
 rw [abs_of_pos (show 0<s from by unfold s; positivity)] at hd
 apply (hd.mono le_rfl (le_of_eq (by unfold R e s; ring))).glue
 filter_upwards [hr.persists,hw.persists] with w hy hz
 ext i j; simp_rw [Matrix.smul_apply, Matrix.of_apply, Matrix.sub_apply]; unfold mild shard glassX; simp_rw [Matrix.smul_apply,Matrix.of_apply]; rw [← smul_sub]
 congrm _ • ?_
 let P(t:ℝ):=pie I (J (w,t)) 0 i j; let G(t:ℝ):=(J (w,t))⁻¹ i j
 change (∫ t in Isle,P t-G t)=(∫ t in Isle,P t)-(∫ t in Isle,G t)
 exact integral_sub ((Ink.Arc.int (g:=fun z=> pie I (J z) 0 i j) (x:=w) (k:=n) (fun t ht=> typed (hy t ht) i j))) ((Ink.Arc.int (g:=fun z=> (J z)⁻¹ i j) (x:=w) (k:=n) (fun t ht=> typed (hz t ht) i j)))
end compress
end YM.CF.Summit
