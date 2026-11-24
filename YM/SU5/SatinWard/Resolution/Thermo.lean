import YM.SU5.Assay.Lamp
import YM.SU5.Assay.Credits
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace Classical
variable {H:Hilbert}{i:Axis}(S:Semigroup H i)
namespace Gear
/-! Precise time second-difference and Taylor properties (general). Avoid Cauchy integral on operator-valued boundary; use basic heat multiplication. Later possibly add mixed-deriv and arbitrarily high for stress. l,r costs universal.
 -/
local notation "ω"=>S.wax
variable {δ t ε l r:ℝ} -- remove
lemma temp_quad (u:0< δ)(v:δ/2≤ t)(h:0 ≤ ε):
 ‖S.wax t + S.wax (t+2*ε)-(2:ℝ) • S.wax (t+ε)‖ ≤ (8/δ)^2 * ε^2:=by
 let x:=t/2
 have ht:0≤t:= by linarith
 have hx0:0≤x:=by unfold x; linarith
 have hp:S.wax t +S.wax (t+2*ε)-(2:ℝ) • S.wax (t+ε)= (ω x-ω (x+ε))*(ω x-ω (x+ε)):=by
    simp only [_root_.sub_mul,mul_sub]; rw [S.wax_sq hx0 hx0,S.wax_sq hx0 (add_nonneg hx0 h), S.wax_sq (add_nonneg hx0 h) hx0,S.wax_sq (add_nonneg hx0 h) (add_nonneg hx0 h),show x+x=t from (add_halves _),show x+(x+ε)= t+ε from (by unfold x; ring),show x+ε+x=t+ε from (by unfold x; ring),show x+ε+(x+ε)=t+2*ε from (by unfold x; ring)]; module
 let g:= S.wax_shaking (show 0 < δ/4 from by linarith) (b:=t/2+ε) (a:=t/2) (by linarith) (by linarith)
 have hv:‖ω x-ω (x+ε)‖≤8/δ*ε:=by refine g.trans_eq ?_; rw [show t/2-(t/2+ε)=-ε from (by ring), norm_neg, Real.norm_of_nonneg h]; ring
 rw [hp]; exact le_trans (norm_mul_le ..) ((mul_self_le_mul_self (norm_nonneg _) hv).trans_eq (by ring))
-- two-sided lag second, s=v and Hu:δ ≤ l,r. for small t. Need first here separately for Taylor proof $∂$. 
local notation "CC"=> Credits
variable {T: ℝ→ℝ→H.Op}(c:Credits S 0 T)
lemma wax_comm(u v:ℝ) : ω u*ω v=ω v*ω u:= ((S.time u.toNNReal v.toNNReal).symm.trans (congrArg S.E (add_comm _ _))).trans (S.time ..)
-- inequality via add and commute. use method algebra transform heat of t: K₀=T (l-t-δ) (r-t-δ). want T (l±t)(r∓t). heat base times ≥δ. let S0=ω δ, A=ω(δ+t), B=ω(δ+2t)
include c
lemma point_quad (u:0< δ)(g:0≤t)(h:t≤ δ/2)(ha:2*δ≤ l)(hc:2*δ≤r) : ‖T (l+t) (r-t)+ T (l-t) (r+t)-(2:ℝ) • T l r‖ ≤ 4*(8/δ)^2*t^2*‖T (l-t-δ) (r-t-δ)‖:=by
 let X:= T (l-t-δ) (r-t-δ); have he(l' r':ℝ)(p:l-t-δ≤l')(q:r-t-δ≤r'): T l' r'=ω (l'-(l-t-δ))*X*ω (r'-(r-t-δ)):= c (by linarith only [ha,h,u]) (by linarith only [hc,h,u]) p q
 let D:=δ; let F:=ω D; let W:=ω (D+t); let Z:=ω (D+2*t)
 have ht:T (l+t) (r-t)+ T (l-t) (r+t)-(2:ℝ) • T l r=(Z*X*F + F*X*Z) - (2:ℝ) • (W*X*W):=by
    rw [he (l+t) (r-t) (by linarith) (by linarith),he (l-t) (r+t) (by linarith) (by linarith), he l r (by linarith) (by linarith),show l+t-(l-t-δ)=D+2*t from (by unfold D; ring),show r-t-(r-t-δ)=D from (by unfold D; ring),show l-t-(l-t-δ)=D from (by unfold D; ring), show r+t-(r-t-δ)=D+2*t from (by unfold D; ring),show l-(l-t-δ)=D+t from (by unfold D; ring), show r-(r-t-δ)=D+t from (by unfold D; ring)]
 let Q:=F+Z-(2:ℝ)•W; let R:= W-F; let M:=8/δ*t
 have hQ:‖Q‖≤ M*M:= (temp_quad S u (t:=δ) (by linarith) g).trans_eq (by unfold M; ring)
 have hF:‖F‖≤ 1:= S.wax_pay D; have hR:‖R‖ ≤ M:= by
    refine (S.wax_shaking u (a:=δ+t) (b:=δ) (by linarith only [g]) le_rfl).trans ?_; rw [add_sub_cancel_left,Real.norm_of_nonneg g]; unfold M; gcongr
    norm_num -- sub simp correct? add_sub_cancel_left? check
 have hx (X Y:H.Op)(u v:ℝ)(t:‖X‖≤ u)(k:‖Y‖≤v): ‖X*Y‖≤u*v:=(norm_mul_le X Y).trans (mul_le_mul t k (norm_nonneg _) ((norm_nonneg _).trans t))
 rw [ht,show Z*X*F + F*X*Z- (2:ℝ) • (W*X*W) = Q*X*F+ F*X*Q-(2:ℝ) • (R*X*R) from (by unfold Q R; simp only [_root_.sub_mul,mul_sub,_root_.add_mul,mul_add,smul_mul_assoc, mul_smul_comm,smul_sub]; module)]
 have ht': 0 ≤ ‖R*X*R‖:= norm_nonneg _; change _ ≤4*(8/δ)^2*t^2*‖X‖; refine le_trans (norm_sub_le ..) ?_; rw [norm_smul,Real.norm_of_nonneg zero_le_two]; refine le_trans (add_le_add ((norm_add_le ..).trans (add_le_add (hx _ _ _ _ (hx Q X _ _ hQ le_rfl) hF) (hx _ _ _ _ (hx F X _ _ hF le_rfl) hQ))) (mul_le_mul_of_nonneg_left (hx _ _ _ _ (hx R X _ _ hR le_rfl) hR) zero_le_two)) ?_; unfold M; exact le_of_eq (by ring)
#print axioms point_quad
end Gear
end YM.OS.Semigroup
