import YM.CF.BProof.Charge.Regular

/-! Taylor charge and buying its bound. Heat remains nonnegative. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}(K:Chart SU.group){C w P D:ℝ}
variable (y:ℝ)(W:Argument s)(c:Clip)(p:BudgetPoint)(T:PathData SU.group)(M:ℕ)(U:Config SU.group s)
variable (h:Ink K C y)(v:p.threshold=thresh y)(k:ValidR c p M)(ht:T.Bounds c w P D)

def sound (β:ℝ)(a:Tile s) := heavy c p T M β (mag y) a
def Taylor (β:ℝ)(a:Tile s):= heavy c p T M β U a-(sound y c p T M β a+ L T M c β y a W + Q T M c β a W)
abbrev Bound (P C y:ℝ)(M:ℕ) := (2*rough P y+thinly P C y M)*thinly P C y M
def costY (P C y:ℝ)(M:ℕ)(β:ℝ) := β*(c.direct+share)* Bound P C y M
include h v k ht
lemma regular_fee (β:ℝ)(a:Tile s)(hb:0≤β)(u:Tall y W M U a): |Taylor y W c p T M U β a| ≤ costY c P C y M β:=by
 let x:= mA y • root T M a; let q:= x+linear T M a W; let d:=unit c β a
 have hk (U:Config SU.group s)(W:Argument s)(H:Tall y W M U a) : |heavy c p T M β U a - d*(‖model y W T M a‖^2/2)| ≤ d*(Bound P C y M/2):=by
   obtain ⟨hd,hx,e,v,z⟩:= issue K y W c p T M U h v k ht a H β hb; let p':=value T M U a; let r:=‖model y W T M a‖; let g:=rough P y; let t:=thinly P C y M
   change |p'-r|≤t at z; change p'≤g at v; have hu:0≤p'+r:=add_nonneg hx (norm_nonneg _); rw [e]; change |d*(p'^2/2)-d*(r^2/2)|≤ _; rw [show d*(p'^2/2)-d*(r^2/2)=d/2*((p'+r)*(p'-r)) by ring,abs_mul,abs_mul,abs_of_nonneg (by exact div_nonneg hd (by norm_num) : 0≤d/2),abs_of_nonneg hu]
   refine (mul_le_mul_of_nonneg_left (mul_le_mul (b:=2*g+t) ?_ z (abs_nonneg _) (le_trans hu ?_)) (div_nonneg hd (by norm_num))).trans_eq (by unfold Bound g t; ring)
   all_goals linarith [(abs_le.mp z).1]
 let g:=hk U W u; have hz: model y 0 T M a=x:=by unfold model; rw [map_zero,add_zero]
 have he:=hk _ _ (lamp0 y M a) -- fix
 unfold Taylor; rw [show heavy c p T M β U a- (sound y c p T M β a+ L T M c β y a W + Q T M c β a W) = (heavy c p T M β U a - d*(‖model y W T M a‖^2/2))-(heavy c p T M β (mag y) a - d*(‖model y 0 T M a‖^2/2)) from by rw [hz, model, norm_add_sq_real]; unfold x d L Q sound; ring]; apply le_trans (abs_sub ..); refine (add_le_add g he).trans ?_
 let D:=Bound P C y M; have hB:0≤D:=by unfold D Bound rough thinly point predicted fourBill paper thin; have hu:=h.up; have hp:= Push.AbsoluteSums.budget_nonneg ht.three; have hg:=SU.group.colorScale_pos; have h₀:0<thresh y:=coin_pos ..; have he:0<aA y:=coin_pos ..; positivity
 change d*(D/2)+d*(D/2)≤_; rw [show d*(D/2)+d*(D/2)=d*D by ring]; apply mul_le_mul_of_nonneg_right _ hB; apply mul_le_mul_of_nonneg_left _ hb; cases a; exact le_add_of_nonneg_right share_pos.le; exact le_add_of_nonneg_left c.quadratic_pos.le
omit h v k ht
def gain (P C:ℝ)(M:ℕ) :ℝ:= (P+1)*((C+ (4*((1+SU.group.colorScale)*C)+(12*SU.group.colorScale)*C))+(2*M*SU.group.colorScale)*C)
lemma gain_identity : thinly P C y M=gain P C M*(aA y*thresh y):=by unfold thinly gain point predicted fourBill paper thin; ring
lemma gain_pl (M:ℝ→ℕ)(u:PL (fun y=> (M y:ℝ))) (P C:ℝ): PL (fun y=>gain P C (M y)):=by
 exact (PL.const _).mul ((PL.const _).add ((((PL.const 2).mul u).mul (PL.const _)).mul (PL.const _)))
lemma grantY (M:ℝ→ℕ)(u:PL fun y=>(M y:ℝ))(P C:ℝ): NPL (fun y=>costY c P C y (M y) (2*y)):=by
 let X(y:ℝ):= y*aA y*thresh y^2
 let i:=gain_pl M u P C
 have hx:NPL X:=by
    apply NPL.by_le (g:=fun y=>coin y (-1/4) (3/8+2) 0) (coin_n (by norm_num) _); filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy; apply le_of_eq; congr 1; unfold X; nth_rw 1 [← coinY hy]; rw [coin_mul,coin_pow,coin_mul]; ring_nf
 let Y(y:ℝ):= 2*(c.direct+share)*(2*(P+1)+gain P C (M y)*aA y)*gain P C (M y)*X y
 have h : NPL Y:= by apply PL.muln _ hx; apply PL.mul _ i; exact (PL.const _).mul ((PL.const _).add (i.mul (coin_n (a:= -1/4) (b:=3/8) (by norm_num) _).weak))
 have H(y): costY c P C y (M y) (2*y)=Y y:=by unfold costY Bound Y; rw [gain_identity]; unfold X rough; ring
 simp_rw [H]; exact h
end YM.CF.BProof.Charge.Form
