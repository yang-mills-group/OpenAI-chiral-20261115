import YM.CF.Jet.Stokes
/-! Flat masks through finite regularity. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Set Metric
open scoped Topology BigOperators ContDiff
variable {E Y Z X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Z][NormedSpace ℝ Z]
variable {f:E→Y}{g:E→Z}{S T:Set E}{k:ℕ}{C:ℝ}{x:E}
lemma Allows.slide (h:Allows (k+1) f x C): Allows k (fderiv ℝ f) x C:=by
 refine ⟨h.smooth.fderiv_right (by simp),fun j hj=> ?_⟩; simpa only [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.norm_map] using h.norm_le (j+1) (by omega)
lemma Allows.dead (h:Allows k f x 0): f x=0 := norm_le_zero_iff.mp h.value
lemma call_g {L:E→Y}(x:E)(p:∀ᶠ y in 𝓝 x,HasFDerivAt L (fderiv ℝ L y) y)(h: Allows k (fderiv ℝ L) x 0)(hp:L x=0) : Allows (k+1) L x 0:=by
 have he :ContDiffAt ℝ ((k:WithTop ℕ∞)+1) L x:=by
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    exact ⟨fderiv ℝ L,⟨_,p,fun i hi=> hi⟩,h.smooth⟩
 refine ⟨by push_cast; exact he,fun i hi=>?_⟩
 cases i; simp only [norm_iteratedFDeriv_zero,hp,norm_zero,le_rfl]; next i=> rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.norm_map]; exact h.norm_le _ (by omega)
variable (P:Y→L[ℝ] Z→L[ℝ] X)(l:IsOpen S)(m:IsOpen T)(c:0≤C) (F:∀ x∈S,x∉T → Allows k f x 0)(hf:∀ x∈S, ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(G:∀ x∈S,x∈T→ Allows k g x C)
include P F G c
lemma knocks(x) (h:x∈ S) : ‖P (f x) (g x)‖ ≤ ‖f x‖*(‖P‖*C):=by
 by_cases t:x∈ T
 · calc
    _ ≤ ‖P (f x)‖*‖g x‖ := ContinuousLinearMap.le_opNorm ..
    _ ≤ (‖P‖*‖f x‖)*C := mul_le_mul (P.le_opNorm _) (G x h t|>.value) (norm_nonneg _) (by positivity)
    _ = _ := by ring
 simp [Allows.dead (F _ h t),c]
include hf l m
lemma born (L:E→X)(h: L=fun x=> P (f x) (g x))(x) (hx:x∈ S) : ContDiffAt ℝ (↑k:WithTop ℕ∞) L x ∧ (x∉T → Allows k L x 0) :=by
 subst L; let W (x:E):=P (f x) (g x)
 have hr x (hx:x∈S) (p:x∈T) : ContDiffAt ℝ (↑k:WithTop ℕ∞) W x:=
     ((P.contDiff.contDiffAt.comp x (hf x hx)).clm_apply (G x hx p).smooth)
 suffices hq:∀ x∈S,x∉T→Allows k W x 0 by
    exact ⟨Classical.byCases (hr x hx) (fun v=> (hq x hx v).smooth),hq x hx⟩
 intro i st t
 clear x hx
 induction k generalizing X Y Z i with
 | zero =>
   have hp : ContinuousOn W S:=by
     intro x hx; by_cases p:x∈T
     · exact (hr x hx p).continuousAt.continuousWithinAt
     apply ContinuousAt.continuousWithinAt; unfold ContinuousAt; rw [show W x=0 by unfold W; rw [(F x hx p).dead]; simp]
     rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (g:=fun u=>‖f u‖*(‖P‖*C)) (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ?_
     · exact Eventually.mono (l.mem_nhds hx) (fun y hy=> knocks P c F G y hy)
     have ht: Tendsto _ _ (𝓝 ‖f x‖):=(hf x hx).continuousAt.norm; rw [(F x hx p).dead,norm_zero] at ht; simpa using ht.mul_const (‖P‖*C)
   refine ⟨(contDiffOn_zero.mpr hp).contDiffAt (l.mem_nhds st),fun k hk=>?_⟩
   rw [Nat.eq_zero_of_le_zero hk,norm_iteratedFDeriv_zero,show W i=0 by unfold W; rw [(F i st t).dead]; simp,norm_zero]
 | succ k ih =>
   let Y₁(x:E):= P.precompR E (f x) (fderiv ℝ g x)
   let Y₂(x:E):= P.precompL E (fderiv ℝ f x) (g x)
   have A(u) (w:u∈S) : HasFDerivAt W (Y₁ u+Y₂ u) u:=by
     by_cases p:u∈T
     · exact P.hasFDerivAt_of_bilinear ((hf u w).differentiableAt (by simp)).hasFDerivAt ((G u w p).smooth.differentiableAt (by simp)).hasFDerivAt
     let hZ:=F u w p; have hi:= hZ.dead; have he:= hZ.slide.dead
     have hF':HasFDerivAt f 0 u:= he ▸ (hZ.smooth.differentiableAt (by simp)).hasFDerivAt
     have hy: W u=0:=by simp [W,hi]
     show HasFDerivAt W _ _
     rw [show Y₁ u+Y₂ u=0 by simp [Y₁,Y₂,hi,he],hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
     intro e p'; rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff] at hF'
     set D:=‖P‖*C; have hd:0≤ D:= by unfold D; positivity
     filter_upwards [l.mem_nhds w,hF' (show 0<e/(D+1) by positivity)] with x hx h
     simp only [hi,ContinuousLinearMap.zero_apply,sub_zero,Pi.zero_apply] at h
     simp only [hy,ContinuousLinearMap.zero_apply,sub_zero]; apply (knocks P c F G x hx).trans
     apply le_trans (show ‖f x‖*D ≤ ‖f x‖*(D+1) by gcongr; simp)
     apply le_trans (mul_le_mul_of_nonneg_right h (by positivity)) (le_of_eq ?_)
     field_simp
   have Hb : fderiv ℝ W =ᶠ[𝓝 i] Y₁ + Y₂ := Eventually.mono (l.mem_nhds st) fun x hx=> (A x hx).fderiv
   have mu:Allows k Y₁ i 0:=by
     apply ih (P:=P.precompR E) (f:=f) (g:=fderiv ℝ g) (fun x hx z=> (F x hx z).order (by omega)) (fun x hx=> (hf x hx).of_le (by exact_mod_cast k.le_succ)) (fun x hx z=> (G x hx z).slide) ?_ i st t
     intro x q p; exact ((P.precompR E).contDiff.contDiffAt.comp x ((hf x q).of_le (by exact_mod_cast k.le_succ))).clm_apply (G x q p).slide.smooth
   -- explicit below
   have mv:Allows k Y₂ i 0 := by
     apply ih (P:=P.precompL E) (f:=fderiv ℝ f) (g:=g) (fun x hx z=>(F x hx z).slide) (fun x hx=> (hf x hx).fderiv_right (by simp)) (fun x hx z=>(G x hx z).order (by omega)) ?_ i st t
     intro x q p; exact ((P.precompL E).contDiff.contDiffAt.comp x ((hf x q).fderiv_right (by simp))).clm_apply ((G x q p).order (Nat.le_succ _)).smooth
   refine call_g i (Eventually.mono (l.mem_nhds st) (fun x hx=> (A x hx).fderiv.symm ▸ A x hx)) ?_ (by unfold W; rw [(F i st t).dead]; simp)
   exact ((by simpa [Pi.add_def] using mu.add mv: Allows k (Y₁+Y₂) i 0)).germ Hb.symm
end YM.CF.Jet
