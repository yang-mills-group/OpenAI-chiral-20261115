import YM.CF.BProof.Gauss.Loss
import YM.CF.BProof.Gauss.Time

/- PL horizon purchase independent of lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Month
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open Prox (Base Show Scope Pup Solo)
open YM.SectorNext.Vacuum.Panel
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable (p a : ℝ→ℝ)(hp: PL p)(ha: PL (fun y=>(a y)⁻¹))(hr:∀ y, 0<a y)(h:∀ y,a y≤p y)
variable (R:ℝ→ℕ)(v:PL (fun y=> (R y:ℝ)))

def snap (d R k :ℕ):= (((2*(R*k)+1)^d:ℕ):ℝ)
def rate (d R k :ℕ):= (snap d R k)⁻¹
def cash (d b R k:ℕ):= snap d R k*b*Real.exp 1
lemma snap_ge (d R k:ℕ): 1≤snap d R k:= Nat.one_le_cast.mpr (one_le_pow₀ (by omega))
lemma rate_pos (d R k:ℕ):0<rate d R k:=inv_pos.mpr (one_pos.trans_le (snap_ge ..))
lemma snap_c {A:Type*} [Fintype A] (B: Prox.Base A)(R k b:ℕ): Show.radiusBill B (rate B.dim R k) (R*k) b=cash B.dim b R k:= by unfold Show.radiusBill cash; change snap B.dim R k *_*Real.exp (rate B.dim R k * snap B.dim R k)=_; rw [show rate B.dim R k*(snap B.dim R k)=1 from inv_mul_cancel₀ (one_pos.trans_le (snap_ge ..)).ne']; -- tune rw

def boundPL (d b R k:ℕ):= (k:ℝ)*(cash d b R k*3+1)*2
lemma tariff {A:Type*} [Fintype A] (B: Base A)(R k b:ℕ):Journey.bill B (rate B.dim R k) b R k=boundPL B.dim b R k:=by unfold boundPL Journey.bill Journey.rent; rw [snap_c ..]
include v
lemma snap_pl (d:ℕ) {k:ℝ→ℕ}(p:PL (fun y=>(k y:ℝ))) : PL (fun y=>snap d (R y) (k y)):=by unfold snap; push_cast; apply PL.pow; exact ((PL.const _).mul (v.mul p)).add (PL.const _)
lemma rate_inv_pl (d:ℕ) {k:ℝ→ℕ}(p:PL (fun y=>(k y:ℝ))): PL (fun y=> (rate d (R y) (k y))⁻¹) := by unfold rate; simp_rw [_root_.inv_inv]; exact snap_pl R v d p
lemma cash_pl (d b:ℕ) {k:ℝ→ℕ}(p:PL (fun y=>(k y:ℝ))) : PL (fun y=>cash d b (R y) (k y)):= ((snap_pl R v d p).mul (PL.const _)).mul (PL.const _)
lemma bill_pl (d b:ℕ) {k:ℝ→ℕ}(p:PL (fun y=>(k y:ℝ))) : PL (fun y=>boundPL d b (R y) (k y)):=by unfold boundPL; exact (p.mul (((cash_pl R v d b p).mul (PL.const _)).add (PL.const _))).mul (PL.const _)
include hp ha hr h
lemma can {d b:ℕ}: let k:= Bin.stride p a 2; PL (fun y=>(k y:ℝ))∧ ∀ᶠ y:ℝ in atTop,∀ {A:Type} [Fintype A](B:Base A),B.dim=d→ Journey.Bloc B (p y) (a y) (rate d (R y) (k y)) b (R y) (k y):=by
 intro k; have ht:= fun x=> (hr x).trans_le (h x); have hk:PL (fun y=>(k y:ℝ)):= Bin.stride_pl hp ha (Eventually.of_forall ht) (Eventually.of_forall hr) 2 (by norm_num); refine ⟨hk,?_⟩
 filter_upwards [eventually_gt_atTop (2:ℝ), coin_strongLt (a:=1) (b:=0) (by norm_num) ((PL.const 6).mul (cash_pl R v d b hk))] with y hy hv
 have hh:0<y:=lt_trans (by norm_num) hy; rw [coinY hh] at hv; have hx: 2*(p y/a y)*Real.log y≤k y:=Nat.le_ceil _; have hp:=Real.log_pos (lt_trans one_lt_two hy); have ha:=hr y; have hg:=ht y; have he := Bin.stay hg (h y) ha (one_lt_two.trans hy) 2 (by norm_num) (k y) hx
 intro A _ B w; subst d; have hl:snap B.dim (R y) (k y)>0:=one_pos.trans_le (snap_ge ..)
 refine ⟨?_,rate_pos ..,ha,h y,?_⟩; exact Nat.cast_pos.mp (lt_of_lt_of_le (by positivity : 0< 2*(p y/a y)*Real.log y) hx)
 rw [snap_c]; have hC:= show (steep (a y) (p y))^k y ≤ y⁻¹^2 from by unfold steep; rw [show a y/p y=(p y)⁻¹*a y by ring, show y⁻¹^2=coin y (-2) 0 0 by nth_rw 1 [←coinY hh]; rw [coin_inv,coin_pow]; ring_nf]; exact he
 let K:=cash B.dim b (R y) (k y); have hK:0≤K:=by unfold K cash; positivity
 apply le_trans (b:=K*(3*y⁻¹^2)) (by change K*_≤_; gcongr); have he':6*K ≤y:=(le_abs_self _).trans hv.le; field_simp; nlinarith
omit hp ha hr h v
private lemma tr_exp {t:ℝ}(u:0<t): (1-Real.exp (-t))⁻¹ ≤ t⁻¹+1 := by
 have hk : Real.exp (-t)≤ 1/(1+t):=by rw [Real.exp_neg,one_div]; exact inv_anti₀ (by positivity) (by rw [add_comm]; exact Real.add_one_le_exp t)
 apply le_trans (b:=(1-(1/(1+t)))⁻¹); refine inv_anti₀ (by field_simp; linarith) (sub_le_sub_left hk _); apply le_of_eq; field_simp; ring_nf; rw [mul_inv_cancel₀ u.ne']
lemma tr_receipt (d b:ℕ)(a:ℝ→ℝ)(h:PL (fun y=>(a y)⁻¹))(ht:∀ y,0<a y)(k:∀ y,a y≤1) : PL (fun y=>Prox.trBill d b (a y)):=by
 let P(y:ℝ):= (2^d*(b:ℝ))*((a y)⁻¹^d*d.factorial*Real.exp 1)*((a y)⁻¹+1)
 refine PL.by_le (((PL.const _).mul (((h.pow d).mul (PL.const _)).mul (PL.const _))).mul (h.add (PL.const 1)) : PL P) (Eventually.of_forall fun y=>?_)
 change |Prox.trBill d b (a y)|≤|P y|; unfold Prox.trBill; have hg : Real.exp (-a y)<1:= Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (ht y)); have hv:(0:ℝ)<1-Real.exp (-a y):=by linarith
 have h:=ht y
 rw [abs_of_nonneg (by positivity : 0≤(2^d*(b:ℝ)*((a y)⁻¹^d*d.factorial*Real.exp (a y)))*(1-Real.exp (-a y))⁻¹)]; apply le_trans _ (le_abs_self (P y)); unfold P; gcongr (_*(_*?_))*?_; exact Real.exp_monotone (k y); exact tr_exp h
lemma fast (f q:ℝ→ℝ)(p:PL f)(hp:PL (fun y=>(q y)⁻¹))(u:∀ y,0<q y) : let k:=Bin.stride (fun _=>1) q 3; PL (fun y=>(k y:ℝ)) ∧ NPL (fun y=> Real.exp (-q y/2*k y)*f y):=by
 let K:=Bin.stride (fun _=>1) q 3
 refine ⟨(Bin.stride_pl (PL.const _) hp (by simp) (Eventually.of_forall u) 3 (by norm_num)), NPL.mulp ?_ p⟩
 apply NPL.by_le (coin_n (a:=-1) (b:=0) (c:=0) (by norm_num)); filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy; have hg:= u y; change |Real.exp (-q y/2*K y)|≤_; have hM: 3*((1:ℝ)/ q y)*Real.log y≤K y:= Nat.le_ceil _; rw [abs_of_nonneg (Real.exp_pos _).le,abs_of_nonneg (coin_pos ..).le]; apply Real.exp_monotone; simp only [mul_neg,mul_one,mul_zero,add_zero]; field_simp at hM; nlinarith [Real.log_pos hy] -- tune
end YM.CF.BProof.Gauss.Month
