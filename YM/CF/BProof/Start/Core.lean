import YM.CF.BProof.Cabinet.Piece

/-! Bad-state cost. Takes all powers after width budgets already chosen.
L_c must tend to +infty. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory NormedSpace Finset Relation
open Lattice Tenant Lat Cube Skye RG Push.AbsoluteSums Angular Wilson Release hot Pricing Gauss Charge Charge.Form
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical
open Cabinet Mint Contour Pods Brick Act
variable {d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)
variable (κ:ℝ)(T:ℝ→ℕ)
def flux (c:Clip)(κ:ℝ)(d:ℕ)(y:ℝ) := issueC c d κ /2 * coin y 0 2 0
abbrev biasW(z:ℝ) (t:ℕ):= z/128*(t:ℝ)^3
abbrev costRoom (b a:ℝ)(W:ℕ)(y:ℝ): Mint.Mode:=⟨a,flux c S.κ d y,biasW b W⟩ -- Stencil arguments extracted when reducing in lemmata. adjust d implicit.
abbrev meters(t:ℕ):ℝ:= Real.log (Brick.Act.costL t)
lemma boundM (t:ℕ):1≤ Brick.Act.costL t:=by unfold Brick.Act.costL; linarith only [show 1≤ (10:ℝ)^(t^3) from one_le_pow₀ (by norm_num)] -- order
lemma valueM(t:ℕ):Real.exp (meters t)= Brick.Act.costL t:=Real.exp_log (zero_lt_one.trans_le (boundM t))
lemma flux_p (p:0<κ)(v:0<d) (y:ℝ):0<flux c κ d y:= by unfold flux; have hh:0< issueC c d κ:=div_pos (plash_pos c d v p) (by norm_num); exact mul_pos (by positivity) (coin_pos ..)
lemma burn_le (p:0<κ)(v:0<d){y:ℝ}(g:0<y)(β:ℝ)(u:y≤2*β): flux c κ d y≤ Pricing.bill_c c d κ y β:=by
 unfold flux; rw [← show y*thresh y^2=coin y 0 2 0 from ?_]; have hp:0≤ issueC c d κ:=div_nonneg (plash_pos c d v p).le (by norm_num); unfold bill_c; nlinarith [mul_le_mul_of_nonneg_left u (mul_nonneg hp (sq_nonneg (thresh y)))]; nth_rw 1 [← coinY g]; rw [coin_pow,coin_mul]; ring_nf
include T
lemma meterPrice (p: PL fun y=>(T y:ℝ)): PL fun y=>meters (T y):=by unfold meters costL; simp_rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero _ (by norm_num : (10:ℝ)≠0)),Real.log_pow]; push_cast; exact (PL.const _).add ((p.pow 3).mul (PL.const _))
-- cool = raw * columns. exponent eventual ≤ any signed pl (not discount if positive).
omit T in
lemma rawQ_t(y:ℝ): rawQ y=coin y 0 (1/4) 0:=by rw [rawQ,coin_pow]; ring_nf
variable (d)
local notation "LΦ"=> (Day.Z 1 (turnP d))⁻¹* Day.total (1/4) (turnP d)
lemma coldStore (p:PL fun y=>(T y:ℝ))(A:ℝ→ℝ)(h:PL A): ∀ᶠ y in atTop, raw_bill d y*((T y)^3:ℕ)≤ Real.exp (A y):=by
 have hp:PL fun y=> (LΦ*(T y:ℝ)^3):=(PL.const _).mul (p.pow 3)
 filter_upwards [coin_strongLt (a:=0) (b:=1/4) (by norm_num) ((PL.const 4).mul (hp.add h.neg))] with y hy
 let t:= LΦ*(T y:ℝ)^3; have ht: t-A y ≤ rawQ y/4:=by
    rw [rawQ_t]; linarith only [(le_abs_self (4*(t + -(A y)))).trans hy.le] -- invalid params tune
 let c:= -rawQ y/4; rw [raw_bill,Day.tip]; push_cast; apply le_trans (b:=Real.exp (t+c)); swap; exact Real.exp_monotone (by unfold c; linarith only [ht]); rw [Real.exp_add]; exact le_trans (le_of_eq (by unfold t c; ring : (LΦ*Real.exp (-rawQ y/4))*(T y:ℝ)^3=t*Real.exp c)) (mul_le_mul_of_nonneg_right (show t≤Real.exp t from by linarith only [Real.add_one_le_exp t]) (Real.exp_pos _).le)
variable {d}
lemma warmth (p:0<d)(h:PL fun y=>(T y:ℝ))(F:ℝ→ℝ)(u:PL F)(g:Tendsto T atTop atTop)(l:ℝ)(hl:0<l)(χ:ℝ)(v:0≤χ):
  ∀ᶠ y in atTop, (costRoom (d:=d) S l (F y) (T y) y).Buy χ (meters (T y)) (T y) d y:=by
 let f y:=meters (T y); have hs:= meterPrice T h; change PL f at hs; let V(y):=(Mode.cold (f y) χ); have he:PL V:= (((PL.const _).mul ((hs.add (PL.const χ)).add (PL.const 2))).neg)
 let J:= Real.log 2; let z(y):= V y -(f y + F y+J); have hx:PL z:=by simp_rw [z,sub_eq_add_neg]; exact he.add (((hs.add u).add (PL.const _)).neg)
 let l₁:= issueC c d S.κ/2; have hv:0<l₁:= by exact div_pos (div_pos (plash_pos c d p S.κ_pos) (by norm_num)) (by norm_num) -- tune
 have hV: Tendsto (fun y=>biasW l (T y)) atTop atTop:= (((tendsto_pow_atTop (by decide :3 ≠0)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp g).const_mul_atTop (by positivity); -- tune
 filter_upwards [coldStore d T h _ hx,hV.eventually_ge_atTop (χ+2+Real.log 10),coin_strongLt (a:=0) (b:=2) (by norm_num) (hx.mul (PL.const l₁⁻¹))] with y hy he hz
 let A:= F y; let m:=T y; let g':=flux c S.κ d y; have hw: -z y≤g':=by
    unfold g' flux; apply le_trans (le_abs_self (-z y)); rw [abs_neg,mul_comm l₁]; apply (div_le_iff₀ hv).mp; rw [div_eq_mul_inv,← abs_of_nonneg (by positivity : 0≤l₁⁻¹), ← abs_mul]; exact hz.le -- tune abs-- issue `mul_comm` elaborated l₁ abbreviation
 refine ⟨?_,(valueM (T y)).ge,?_,Real.log_nonneg (boundM _),v⟩
 · unfold pocket; dsimp only [costRoom]; change costL m*(Real.exp (A-g') + _*Real.exp A) ≤ _; rw [mul_add,←valueM]; calc
    _ ≤ Real.exp (meters m)*Real.exp (A+z y) + Real.exp (meters m)*( Real.exp (z y)*Real.exp A) := add_le_add (by gcongr; linarith only [hw]) (by gcongr)
    _ = (Real.exp (V y)/2) + Real.exp (V y)/2 := by rw [←Real.exp_add, ← Real.exp_add,← Real.exp_add]; have hh:meters m=f y:=rfl; unfold z; rw [show meters m+(A+(V y- (f y+ F y + J)))=V y-J from by unfold A; rw [hh]; ring, show meters m+(V y - (f y + F y + J) + A)=V y-J from by unfold A; rw [hh]; ring,Real.exp_sub, show Real.exp J=2 from Real.exp_log (by norm_num)]
    _ ≤ _:= by change _ ≤ Real.exp (V y); linarith
 nth_rw 1 [← show Real.exp (Real.log (10:ℝ))=10 from Real.exp_log (by norm_num)]; rw [←Real.exp_add]; exact Real.exp_monotone (by change Real.log 10+ -(biasW l (T y))≤_; linarith only [he])
end YM.CF.BProof.Start
