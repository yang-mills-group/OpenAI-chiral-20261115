import YM.SU5.Regis.Easel
/-! # Packed apertures. Overlaps permitted at this stage, issued by distinct anchors.
Aggregate sensitivity estimate. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule
open Gleam Matrix Next.SectorChange Next.SectorChange.Gaussian
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {n c:Side}{r: Ratio c n}{G:Gauge}{H:Bed}{m:ℕ}{η C S v δ : ℝ}{Z:PathData G}{I J:Type*}
namespace Etch
variable [Fintype I](A:Etch G I) (q:Clip) [Fintype J] (o:J→ Site n)(p:Injective o)
abbrev layoutC (ρ:ℝ)(t:J→Signed)(o:J→Site n) (y:Altar G n):= ∑ j:J,A.chalk q ρ (t j) (o j) y
def gallery (ρ:ℝ)(t:J→Signed)(o:J→Site n) (x:Config G n):=∑ j:J,A.palette ρ (t j) (o j) x
-- possibly chess has extra factors `exp(C_j)` but independent of placement for single probe; ok
variable (ρ:ℝ)(t:J→Signed) (B:Z.Bounds q η C S)(P:Attached H Z)(L:Floor H q n δ v)(O:Bid.Sworn H n G)
lemma museum : Envelope (A.gallery ρ t o):= ⟨(continuous_finsetSum _ (fun i _=> A.panel_smooth ..)).measurable,A.arc*Fintype.card J,fun i=> (by rw [gallery,Real.norm_eq_abs]; apply le_trans (Finset.abs_sum_le_sum_abs ..); apply (Finset.sum_le_sum (fun x _=> A.panel_bound ρ (t x) (o x))).trans; refine Eq.le ?_; simp; ring)⟩
lemma encase : GaugeInvariant (A.gallery ρ t o):=fun x U=> Finset.sum_congr rfl (fun i _=> A.panel_gauge ρ _ _ x U)
lemma entourage (s:Signed)(b:Site n)(x:Config G n): A.gallery ρ t o (pull s b x)=A.gallery ρ (fun i=>s*t i) (fun i=> affine s b (o i)) x:= Finset.sum_congr rfl (fun i _=> A.panel_pull ..)
lemma planBound (x:Altar G n) : |A.layoutC q ρ t o x| ≤ Fintype.card J*A.arc:= (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun x _=> A.chalk_bound q ρ (t x) (o x))).trans (le_of_eq (by simp)))
lemma planSmooth : ContDiff ℝ 1 (A.layoutC q ρ t o):= ContDiff.sum (fun i _=> A.chalk_smooth ..)
include p in
lemma cup_sum (u:RG.Slot)(x:Altar G n): (∑ i:J, ‖cup (slotFace u (o i)) x‖) ≤ Real.sqrt (Fintype.card J)*‖x‖:=by
 let S(i:J):= slotFace u (o i); let Z(i:J):= ‖cup (S i) x‖; let f(i: J × G.ColorIndex) : Cell n×Bool×G.ColorIndex:=(S i.1,false,i.2)
 have hf:Injective f:=by
    rintro ⟨a,b⟩ ⟨c,d⟩ g; have h: S a=S c:=congrArg Prod.fst g; have he:b=d:=congrArg Prod.snd (congrArg Prod.snd g); exact Prod.ext (p (add_left_cancel (congrArg Prod.fst h: wrap n u.offset+o a=wrap n u.offset+o c))) he
 have hx: (∑ i:J,Z i^2) ≤ ‖x‖^2:=by
    let G(w):=x w^2
    rw [EuclideanSpace.real_norm_sq_eq]; refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (f:=G) (subset_univ (univ.image f)) (fun w _ _=> sq_nonneg _))
    rw [sum_image (fun _ _ _ _=> hf.eq_iff.mp), Fintype.sum_prod_type]; unfold Z; simp_rw [EuclideanSpace.real_norm_sq_eq]; exact le_rfl
 have hu:=le_trans (Real.sum_mul_le_sqrt_mul_sqrt univ (fun i:J=>1) Z) (mul_le_mul_of_nonneg_left (le_trans (Real.sqrt_le_sqrt hx) (Real.sqrt_sq (norm_nonneg x)|>.le)) (Real.sqrt_nonneg _)); simpa only [one_pow,one_mul,sum_const,card_univ,nsmul_eq_mul,mul_one] using hu
-- Bessel. Lipschitz via sum over all spins flag; slack factor O(k^2).
abbrev rays (ρ:ℝ):ℝ:= |ρ| *(Real.sqrt q.direct)⁻¹
def lensLimit (ρ:ℝ):ℝ:= A.favor * rays q ρ * Fintype.card I * Fintype.card Signed
lemma lensLimit_non (ρ:ℝ): 0 ≤ A.lensLimit q ρ:= by unfold lensLimit rays; positivity
lemma chalk_steady (s:Signed)(o:Site n) (x y:Altar G n): |A.chalk q ρ s o x-A.chalk q ρ s o y| ≤ (A.favor:ℝ)*rays q ρ * (∑ i:I, ‖cup (slotFace (skewSlot G (A.slot i) s) o) (x-y)‖):=by
 let F(i:I):= slotFace (skewSlot G (A.slot i) s) o; let Z(p:Altar G n)(i:I):=ρ • skewSig G (A.slot i) s • river q (F i) p; let t:= rays q ρ
 have he: ‖Z x-Z y‖ ≤ t*(∑ i:I, ‖cup (F i) (x-y)‖):= by
    refine (pi_norm_le_iff_of_nonneg ?_).mpr (fun i=>?_); · unfold t rays; positivity
    have h:0 ≤ t:=by unfold t rays; positivity
    apply le_trans _ (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun i:I=> ‖cup (F i) (x-y)‖) (fun i _=>norm_nonneg _) (mem_univ i)) h); apply le_of_eq
    rw [Pi.sub_apply, show Z x i-Z y i=ρ • skewSig G (A.slot i) s • (river q (F i) (x-y)) from (by unfold Z; rw [_root_.map_sub, smul_sub,smul_sub])]; unfold t rays river; simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg,Real.sqrt_nonneg, mul_assoc] -- tune
 rw [← Real.norm_eq_abs]; exact (A.steady.norm_sub_le (Z x) (Z y)).trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_assoc ..).symm)
include p in
lemma rays_steady (x:Altar G n): ‖fderiv ℝ (A.layoutC q ρ t o) x‖ ≤ A.lensLimit q ρ * Real.sqrt (Fintype.card J):=by
 let D:= A.lensLimit q ρ; let E:= Real.sqrt (Fintype.card J); let N:ℝ≥0:=⟨D*E,mul_nonneg (A.lensLimit_non q _) (Real.sqrt_nonneg _)⟩; refine norm_fderiv_le_of_lipschitz ℝ (C:=N) (LipschitzWith.of_dist_le_mul fun x y=>?_)
 rw [dist_eq_norm,dist_eq_norm,Real.norm_eq_abs]; unfold layoutC; rw [← sum_sub_distrib]; let X(i:J)(b:Signed)(j:I):= ‖cup (slotFace (skewSlot G (A.slot j) b) (o i)) (x-y)‖; let c:ℝ:= A.favor*rays q ρ; have h:0 ≤ c:=by unfold c rays; positivity
 refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun i=> c* (∑ b:Signed,∑ j:I,X i b j)) (fun i _=>(A.chalk_steady q ρ (t i) (o i) x y).trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun b=> ∑ j:I, X i b j) (fun b _=> sum_nonneg (fun j _=> norm_nonneg _)) (mem_univ (t i))) h))).trans ?_)
 rw [← mul_sum, Finset.sum_comm]; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _=> Fintype.card I*(E*‖x-y‖)) ?_) h).trans_eq ?_
 · intro i _; rw [Finset.sum_comm]; refine (Finset.sum_le_sum (fun u _=> cup_sum o p (skewSlot G (A.slot u) i) _)).trans_eq (?_) -- type X tune
   simp [E]
 rw [sum_const,card_univ,nsmul_eq_mul]; change _=D*E*_; unfold D lensLimit; unfold c; ring
include O L in
lemma gallery_fee (α:ℝ): plumeCost B P (A.layoutC q ρ t o) α= Fintype.card J* (α* A.muρ q B P ρ n):=by
 rw [plumeCost, cloud_turn B P _ (A.planSmooth .. |>.continuous)]; -- A.. ambiguity
 unfold clouds layoutC; rw [integral_finsetSum]; swap; · exact fun i _=> A.integr_chalk ..
 have h(i:J): (∫ x: stamen B P n, A.chalk q ρ (t i) (o i) x.val ∂stdGaussian (stamen B P n))=A.muρ q B P ρ n:= A.paid_chalk q ρ _ _ B P L O
 simp_rw [h]; rw [sum_const,card_univ,nsmul_eq_mul,mul_left_comm]
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.Etch.gallery_fee
#print axioms YM.Regis.Head.Etch.rays_steady
