import YM.SU5.Regis.Archive
import YM.SU5.Thin.Glacier.Toll
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
private lemma on_wind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))
variable (B:Z.Bounds q η C S) {φ:Config G n→ℝ}(u: Envelope φ)
abbrev polarBill (Z:PathData G)(q:Clip)(p:BudgetPoint)(β κ κA τ:ℝ)(U:Config G n):= Real.exp (-(Z.inChannels q p β U)+stipd κ κA (meek p U) τ U)
variable {κA τ:ℝ}
include B
lemma polar_env: Envelope (polarBill Z q p β κ κA τ (n:=n)):= by
 exact ((PathData.channels_env B p β).neg.add ((conduct n _ _).add (conduct n _ _))).exp
include u in
lemma everyPolar (ξ:ℝ)(t:ℝ)(hh:∀ d: Signed,(∫ x:Config G n, heatG Z q p β κ κA τ x *Real.exp (t*φ (pull d 0 x)) ∂prior G n) ≤ ξ) : (∫ x:Config G n, polarBill Z q p β κ κA τ x * Real.exp (t*φ x) ∂prior G n) ≤ ξ := by
 let M:ℝ:=Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 let w:= M⁻¹; let S:=polarBill Z q p β κ κA τ (n:=n); let F (s: Signed) (x:Config G n):= heatG Z q p β κ κA τ x * Real.exp (t*φ (pull s⁻¹ 0 x)); let X:=prior G n; let Φ(s:Signed)(x:Config G n ):=F s (pull s 0 x)
 have hw:∑ _:Signed,w=1:= by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 have E(i:Signed) : Envelope (F i):=(heat_env B).mul ((fun p:Envelope (fun x:Config G n=> φ (pull i⁻¹ 0 x) )=>expEnv p t) ⟨u.meas.comp (by apply (prior_pull _ _).measurable), u.cost.choose,fun _=> u.cost.choose_spec _⟩); let G'(x: Config G n):= ∑ i: Signed,w*Φ i x
 have he(i:Signed): Integrable (fun x=>w*Φ i x) X:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable ((E i).integrable X)).const_mul w
 have hf:Integrable G' X:= integrable_finsetSum _ (fun i _=> he i)
 refine le_trans (integral_mono (show Integrable _ _ from ((polar_env (n:=n) (p:=p) (κ:=κ) (β:=β) B).mul (expEnv u t)).integrable X) hf ?_) ?_
 · intro x; let f(s:Signed):= Z.principal q p β (pull s 0 x); let g:= stipd κ κA (meek p x) τ x; let e(s:Signed):= -f s+g + t*φ x; have ht(i:Signed): Φ i x=Real.exp (e i ):=by unfold Φ F heatG e stipd meek g; rw [on_wind,on_wind, pull_pull]; simp [affine,Real.exp_add]; ring -- maybe
   unfold G'; simp_rw [ht]; let tt:= (convexOn_exp.map_sum_le (w:=fun _ : Signed=>w) (fun i _=> inv_nonneg.mpr hM.le) hw (fun s _ => Set.mem_univ (e s)))
   rw [←Real.exp_add]
   change Real.exp _ ≤ ∑ i,w • _; apply tt.trans'; refine Eq.le (congrArg Real.exp ?_); unfold e; simp only [smul_eq_mul,mul_add,sum_add_distrib, mul_neg,sum_neg_distrib, ← mul_sum, sum_const, card_univ,nsmul_eq_mul]; change -(w*∑ s,f s)+ g + t*φ x= -(w*∑ s,f s)+ w * (M*g) + w * (t*(M*φ x)); rw [mul_left_comm t M, inv_mul_cancel_left₀ hM.ne', inv_mul_cancel_left₀ hM.ne'] -- order
 unfold G'; rw [integral_finsetSum _ (fun i _=> he i)] -- signature lemma
 have h(i:Signed):(∫ x:Config G n, w*Φ i x∂X)=w*∫ x,F i x∂X:=by rw [integral_const_mul]; refine congrArg (w * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂X from (by have ht:= integral_map (μ:=prior G n) (f:=F i) t.measurable.aemeasurable (show AEStronglyMeasurable (F i) _ from (E i).meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht))
 simp_rw [h]; refine (Finset.sum_le_sum (g:=fun _=> w*ξ) (fun i _=>?_)).trans_eq ?_; · exact mul_le_mul_of_nonneg_left (hh i⁻¹) (by unfold w; positivity)
 rw [← Finset.sum_mul,hw,one_mul]

end YM.Gleam