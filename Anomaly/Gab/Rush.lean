import Anomaly.Gab.Script
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
/-! scalar & flag spend for estimated shapes. On all Role. Rate5 zero when weight=4 from Tir.Pulse. -/
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E}
variable {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2:ℝ}{z:ℂ}
-- use P receipts IN EXACT units h
variable (T:Melon L X Y z H Q A w)
variable {Z U:ArcΦ}{t x:ℂ} (M:Markup L X Y z H Q A w K C v0 v1 v2 Z U t x)
abbrev paceY:= |2*peka_H 2|+2
local notation "bζ"=> (|(2*peka_H 2)|)
abbrev εKo (K:ℝ):= Real.exp 1 * paceY * |K|
lemma paceY_paid : 1 ≤ paceY :=by unfold paceY; linarith [abs_nonneg (2*peka_H 2)]
include T M
local notation "κφ" i:max=> κprobe i L H (A*Q) w z Z
local notation "Lν"=> ((L.val:ℝ)⁻¹)
local notation "ΦΖ" => Markup L X Y z H Q A w K C v0 v1 v2
lemma Markup.crops : let b:= εKo A * Q; ‖z‖*‖Z.1‖≤ b∧ (‖z‖*‖Z.2‖)*H^2 ≤ b∧ (‖z‖*‖Z.2.2‖)*H^2 ≤ b∧ (‖z‖*‖Z.2.1‖)*H^2≤ b:=by
 intro b; have hp:=T.grab; obtain ⟨v,u⟩:=M.small; have hx:=T.rank
 have h': (‖z‖*‖Z.2‖)*H^2≤b:=by
    rw [mul_assoc]; apply le_trans (mul_le_mul T.seam u (by positivity) (Real.exp_pos _).le); unfold b εKo; rw [abs_of_nonneg hp]; rw [mul_assoc (Real.exp _) paceY A,mul_assoc (Real.exp _) (_*A) Q,mul_assoc paceY]; apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_two)) (show 0 ≤ A*Q from by positivity)
 refine ⟨(mul_le_mul T.seam v (norm_nonneg _) (Real.exp_pos _).le).trans ?_,h',le_trans ?_ h',le_trans ?_ h'⟩
 · unfold b εKo; simp_rw [abs_of_nonneg hp,mul_assoc]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (show 0 ≤ A*Q from by positivity) paceY_paid) (Real.exp_pos _).le
 · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_snd_le _) (norm_nonneg _)) (sq_nonneg _)
 exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_fst_le _) (norm_nonneg _)) (sq_nonneg _)
omit T M
abbrev far_C(A:ℝ):= εKo A*3+|A|+1
lemma far_ge(a:ℝ):0≤ far_C a:=by have h:=paceY_paid; have h':0≤paceY:=zero_le_one.trans h; unfold far_C εKo; positivity
lemma between_L(L:Side):0 < ((L.val:ℝ)⁻¹)∧ ((L.val:ℝ)⁻¹)≤1:=⟨by positivity,inv_le_one_of_one_le₀ (by exact_mod_cast L.property)⟩
include T M
lemma Markup.pale_bound : |κφ naxR|≤ far_C A*(Q*Lν^5):=by
 obtain ⟨ha,hb,hc,hd⟩:= Markup.crops T M; have h:=T.grab; obtain ⟨hy,y⟩:=between_L L; have hX:=T.rank
 unfold κprobe naxR; refine (abs_add_le ..).trans ((add_le_add (le_trans ?_ (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add (add_le_add ha hd) hc) (A*Q)) (pow_nonneg hy.le 5))) T.pay).trans_eq ?_)
 · rw [abs_of_nonneg]; positivity
 unfold far_C; rw [abs_of_nonneg h]; ring
omit T M
lemma tuneSlack (S T U V M a:ℝ)(h:0 < S)(t:S≤1)(r:T≥0)(u:0≤U)(v:0≤V)(m:0≤ M)(p:T≤a)(q:U≤a) : S^4*T+0+S^4*U+S^5*V + S^5*M ≤ S^4*(a+a+V+M):=by
 simp_rw [mul_add,add_zero]; have ht:S^5≤S^4:=pow_le_pow_of_le_one h.le t (by norm_num); apply add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left p (pow_nonneg h.le _)) (mul_le_mul_of_nonneg_left q (pow_nonneg h.le _))) (mul_le_mul_of_nonneg_right ht v)) (mul_le_mul_of_nonneg_right ht m)
abbrev mintSum (A K:ℝ):= paceY*|K| * far_C A
include T M
lemma Markup.three_zero (h:ιBuild3.space H Z=0):|κφ mintR| ≤ far_C A*(Q*Lν^(3+1:ℕ)):=by
 have he: Z.2.1=0:=tote_Φ H (zero_lt_one.trans_le T.earn) Z 0 M.shape ⟨mind_A.zero_mem,mind_B.zero_mem,mind_C.zero_mem⟩ ((map_zero (ιBuild3.space H)) ▸ h)
 obtain ⟨p,t,z,y⟩:= Markup.crops T M; have hX:= T.rank; have hp:= T.grab; obtain ⟨hy,u⟩:=between_L L
 unfold κprobe mintR; rw [he, norm_zero,mul_zero,zero_mul,mul_zero]; apply (abs_add_le ..).trans; rw [abs_of_nonneg (by positivity : 0 ≤ Lν^4*_ + 0 + Lν^4*_+ Lν^5* (A*Q))]; refine (le_trans (add_le_add_right T.pay _) ((Eq.le ?eq).trans ((tuneSlack Lν _ _ (A*Q) Q _ hy u (by positivity) (by positivity) (by positivity) hX.le p z).trans ?_ ))) -- scrutinize parentheses expected simplifier loop
 case eq=> ring
 unfold far_C; rw [abs_of_nonneg hp]; have he:0 ≤ εKo A :=by have hx:0 ≤ paceY:=zero_le_one.trans paceY_paid; unfold εKo; positivity
 change _≤ (εKo A*3+A+1)*(Q*Lν^4); nlinarith only [mul_nonneg he (mul_nonneg hX.le (show 0 ≤ Lν^4 by positivity))]
lemma Markup.four_zero (h:ιBuild4.space H Z=0) : |κφ mintR|≤ far_C A*(Q*Lν^5):=by
 have he: Z=0:=bite_Φ H (zero_lt_one.trans_le T.earn) Z 0 M.shape ⟨mind_A.zero_mem,mind_B.zero_mem,mind_C.zero_mem⟩ ((map_zero (ιBuild4.space H)) ▸ h)
 have h:=Markup.pale_bound T M; rw [he] at h ⊢; simpa only [κprobe,naxR,mintR, Prod.fst_zero,Prod.snd_zero,norm_zero,mul_zero,zero_mul,zero_add] using h
-- estimate normalized fields
variable {P:ℝ}
lemma Markup.offset_pay (u: |κφ mintR|≤ P): ‖x-t‖ ≤ |C| * P:=M.earn.trans ((le_abs_self _).trans ((abs_mul ..).trans_le (mul_le_mul_of_nonneg_left u (abs_nonneg _))))
lemma Markup.pay_Y (u: |κφ mintR|≤ P): ‖dreamℂ H U‖ ≤ paceY*(|K| * P):=by
 obtain ⟨hv,v⟩:=M.coin; let f:= K*(κφ mintR); have he:0 ≤ f:=(norm_nonneg _).trans hv; have hy: |f|≤ |K| * P:= (abs_mul ..).trans_le (mul_le_mul_of_nonneg_left u (abs_nonneg _)); rw [abs_of_nonneg he] at hy
 refine ηDay _ (zero_lt_one.trans_le T.earn) _ M.shape' f (2*peka_H 2) f _ hv v ?_ ?_
 · exact hy.trans (le_mul_of_one_le_left (he.trans hy) paceY_paid)
 apply mul_le_mul ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_two)) hy he (by positivity)
end YM.CF.Py
