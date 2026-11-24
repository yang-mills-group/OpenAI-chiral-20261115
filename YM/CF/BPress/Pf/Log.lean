import YM.CF.BPress.Pf.Plog
/-! Four real trace terms choose exact physical log with distinguished imaginary part. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter Finset Fock Spin NormedSpace MeasureTheory Branch Spin.Pledge Spin.Cellar Spin.Cellar.Pass Quad Mileage Helm Thera
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q:Finset I}{A T V W:Op I}{C C': ℝ → Op I}{r ε a:ℝ}

section Log
def permit(A T:Op I):= (1/2:ℝ) • helm 3 (1+ star T*T)
def permitX (P:Finset I)(A T:Op I):=(1/2:ℝ) • helm 3 (terrace (cutM P) (mood A T))
def permitY (P Q:Finset I)(A T:Op I):=(1/2:ℝ) • helm 3 (terrace (cutM Q) (1-rent0 (cutM P) (mood A T)))
def billZ (P Q: Finset I)(A T C:Op I):=(1/4:ℝ) • loss (ramp (shun I P Q) (cutM P) (mood A T)) C
def realBill(P Q:Finset I)(A T C:Op I):ℂ:=(permit A T+permitX P A T+permitY P Q A T+billZ P Q A T C).trace
def totalBill(P Q:Finset I)(A T:Op I)(C C':ℝ→Op I):ℂ:= ((realBill P Q A T (C 2)).re:ℂ)+ (sweepR P Q A T C C').im * Complex.I
lemma trace_real(K:Op I)(x:ℝ): (x • K).trace.re=x*K.trace.re:=by rw [Matrix.trace_smul]; simp

variable (H: Issued P Q A T C C' r ε)
namespace Issued
include H
local notation "aP"=> cutM P
local notation "aQ"=> cutM Q
local notation "T₁"=> mood A T
local notation "L"=> shun I P Q
local notation "R"=> ramp L (cutM P) T₁

lemma pay_s : (1:Op I)≤1+star T*T∧1+star T*T≤(3:ℝ) • (1:Op I):=by
 refine ⟨le_add_of_nonneg_right (star_mul_self_nonneg _), (add_le_add le_rfl ((op_le_norm_one (IsSelfAdjoint.star_mul_self T)).trans (smul_le_smul_of_nonneg_right (?_ : ‖star T*T‖≤(2:ℝ)) zero_le_one))).trans_eq ?_⟩; swap -- tune smul b name
 · module
 rw [CStarRing.norm_star_mul_self]; exact (mul_le_one₀ H.near (norm_nonneg _) H.near).trans (by norm_num)
omit H in
lemma price1 {c:ℝ}(p:IsStarProjection V)(e:IsStarProjection W)(h:c • V≤V*W*V)(s:0<c)(u:c≤1) : c • (1:Op I)≤ terrace V W∧ terrace V W≤ (3:ℝ) • (1:Op I):=by
 refine ⟨coin p _ s u h,?_⟩; apply (add_le_add (s_mono p.isSelfAdjoint e.le_one) (show 1-V≤1 from p.one_sub.le_one)).trans; rw [mul_one,p.isIdempotentElem.eq]; apply (add_le_add p.le_one le_rfl).trans; rw [show (1:Op I)+1=(2:ℝ) • 1 by module]; exact smul_le_smul_of_nonneg_right (by norm_num) zero_le_one
lemma pay_1:let M:=terrace aP T₁; ε • (1:Op I)≤ M∧ M≤(3:ℝ) • (1:Op I) := price1 (cutM_idp _) H.rails.a H.rails.payP H.rails.pos H.rails.small
lemma pay_2:let M:=terrace aQ (1-rent0 aP T₁); ε • (1:Op I)≤ M∧ M ≤(3:ℝ) • (1:Op I):=price1 (cutM_idp _) H.rails.r0.one_sub H.rails.pay0 H.rails.pos H.rails.small
lemma drum : Arrange P Q L T₁ (C 2) ε r:=⟨H.rails,H.skit,H.apart,H.endF⟩
omit H in
lemma sell (A:Op I)(p:0<ε)(z:ε≤1)(h:ε • (1:Op I)≤ A)(t:A≤ (3:ℝ) • (1:Op I)): Real.exp (helm 3 A).trace.re=‖A.det‖:= by have ht:= affords p (z.trans_lt (by norm_num)) h t; exact scaledN (by norm_num) (ht.1.trans_lt ht.2)
lemma validate {x:Wave I}(p:Top A x)(q:‖x‖=1): ‖inner ℂ (braC P Q (C 2)) (craft A T x 1)‖= Real.exp (realBill P Q A T (C 2)).re:=by
 let M:= 1+star T*T; let y:=craft A T x 1; let t:= H.rising p 1; let F:= slide aP aQ L T₁ 0; let z:= acts (quant F) y; let U:=P; let G:= H.rails.enjoy 0 (by simp)
 let X:= terrace aP T₁; let Y:=terrace aQ (1-rent0 aP T₁); let A':=Trans.gram T₁ F; let r':=(helm 3 A').trace
 have hx:‖y‖^2=‖M.det‖:=by
    unfold y; let B:= tiltR H.proj H.she 1; rw [← H.craft_with p,floatW p B, q,one_pow,one_mul, Spin.tempo H.proj H.she, one_smul]
 have ht:‖z‖^2= (‖M.det‖*‖X.det‖)*‖Y.det‖:=by rw [show ‖z‖^2= _ from (floatW t G), hx, show (Trans.gram (tilt A T 1) F).det= X.det * Y.det from Mileage.cellar H.rails, norm_mul, mul_assoc] -- tune
 have hs: Top (aP+R) z:= by rw [← H.rails.mark_exit]; exact Top.spread t G
 have hw:=H.rails.small; have hK:= H.rails.pos; let H1:= permit A T; let H2:= permitX P A T; let H3:= permitY P Q A T; let H4:= billZ P Q A T (C 2); let J:= 1-lost R (C 2); let D:=(H1+H2+H3+H4).trace
 have yR(r:ℝ)(B:Op I): (r • B).trace.re=r*B.trace.re := trace_real B r
 have yD:4*D.re=2*((helm 3 M).trace.re+(helm 3 X).trace.re+(helm 3 Y).trace.re)+(loss R (C 2)).trace.re:=by unfold D H1 H2 H3 H4 permit permitX permitY billZ; simp only [Matrix.trace_add,Complex.add_re,yR]; unfold M X Y; ring
 have h₁:Real.exp (helm 3 M).trace.re= ‖M.det‖:=sell M (ε:=1) one_pos le_rfl (one_smul ℝ 1 |>.le.trans H.pay_s.1) H.pay_s.2
 have h₂:Real.exp (loss R (C 2)).trace.re=‖J.det‖:= by rw [loss,bill_p (by rw [norm_neg]; exact Issued.normL H.drum.backB),←sub_eq_add_neg]; -- tune
 rw [bra_ref (H.rising p 1) H.rails H.apart]; change ‖inner ℂ _ z‖=Real.exp D.re; apply (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le (show (4:ℕ)≠0 by norm_num)).mp; rw [H.endF.modA hs,Dual.lost_exit H.skit H.rails H.endF, show ‖z‖^4=(‖z‖^2)^2 by ring,ht,←Real.exp_nat_mul]; norm_num1; rw [yD,Real.exp_add,two_mul,Real.exp_add, Real.exp_add,Real.exp_add,h₁,h₂,sell X hK hw H.pay_1.1 H.pay_1.2,sell Y hK hw H.pay_2.1 H.pay_2.2,pow_two]
lemma offset_bill {x:Wave I}(p:Top A x)(v:‖x‖=1)(z:ℂ)(q:z.re=0)(h:Complex.exp ((uPivot A (C 0):ℂ)+z) • x=filled A (C 0)): inner ℂ (braC P Q (C 2)) (craft A T x 1)= Complex.exp (totalBill P Q A T C C'-z):=by
 rw [H.liftLog p z h]; congr 1; have hx:= H.validate p v; rw [H.liftLog p z h,Complex.norm_exp] at hx; have ht:= Real.exp_injective hx; apply Complex.ext <;> (unfold totalBill; simp [Complex.mul_re, Complex.mul_im, q , *] at *; try abel)
lemma defectB : billZ P Q A T (C 2) ≤ -( (1/4:ℝ) • lost R (C 2)) :=by unfold billZ loss; rw [← smul_neg]; exact smul_le_smul_of_nonneg_left (below H.drum.backB.PSD (Issued.normL H.drum.backB)) (by norm_num)
end Issued
end Log
end YM.CF.BPress.Pf
