import YM.CF.BPress.Ledger
import YM.CF.BPress.Scale
/-! PL trace/map budgets after losses on exponentially weighted norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Filter Lattice Wilson RG Branch Push.AbsoluteSums Ledger Finset
open scoped Topology BigOperators Classical
variable (r:ℕ)(a C:ℝ)
-- scalar payment ∑. constants G not fixed explicitly ok
private def posharp (r:ℕ)(a c:ℝ) := (2*(r:ℝ)*c*a⁻¹+1)^r
def harm (r:ℕ)(a c:ℝ) := posharp r a c * (1+2*a⁻¹)
lemma scalerB (p:0<a) : (1-Real.exp (-a))⁻¹≤1+a⁻¹:=by
 rw [← one_div]; apply (div_le_iff₀ (show 0 < 1-Real.exp (-a) by rw [sub_pos]; exact Real.exp_lt_one_iff.mpr (by linarith))).mpr -- tune `one_div`
 have he:1+a≤ Real.exp a:= by simpa [add_comm] using Real.add_one_le_exp a
 rw [Real.exp_neg]; field_simp; nlinarith -- tune
lemma thin_count (p:0<a)(v:0≤ C): SumBudget (fun i:ℕ=> (C*i+1)^r* Real.exp (-a*i)) (harm r a C):=by
 let U:=Real.exp (- (a/2)); have hp:U<1:= Real.exp_lt_one_iff.mpr (by linarith); let A:=posharp r a C; have ha:0 ≤ A:=by unfold A posharp; positivity
 refine budget_mono (budget_loosen (budget_geometric ha (Real.exp_pos _).le hp) ?_) (fun i=>by positivity) ?_
 · unfold harm; apply mul_le_mul_of_nonneg_left _ ha
   calc
      (1-U)⁻¹ ≤ 1+(a/2)⁻¹:= scalerB _ (half_pos p)
      _ = _ := by field_simp
 intro k; rw [← Real.exp_nat_mul]; cases r with
 | zero=> change (C*↑k+1)^0*_ ≤ _^0 *_; simp only [pow_zero,one_mul]; apply Real.exp_monotone; nlinarith
 | succ r=>
   let V:ℝ:= ↑(r+1); have hV:0<V:= by unfold V; positivity
   let E:=a*↑k/(2*V); let R:=2*V*C*a⁻¹+1; have he:0 ≤ 2*V*C*a⁻¹:=by positivity
   have hR:0 ≤ R:=by unfold R; positivity
   have hx:0≤E:=by unfold E; positivity
   have hZ:C*↑k+1≤ R*Real.exp E:=by
     refine le_trans ?_ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp E) hR); unfold R; have hp:C*k=(2*V*C*a⁻¹)*E:=by unfold E; field_simp
     nlinarith only [hx,hp,he]
   refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hZ (r+1)) (Real.exp_pos _).le).trans_eq ?_; rw [mul_pow,mul_assoc,←Real.exp_nat_mul,←Real.exp_add]; change R^(r+1)*_=R^(r+1)*_; congr 2; change V*E + -a*k=_; unfold E; field_simp; ring
lemma pl_harm (a C:ℝ→ℝ)(h:PL fun i=>(a i)⁻¹)(p:PL C): PL (fun i=> harm r (a i) (C i)):= (PL.pow (F:=fun i=>2*r*C i*(a i)⁻¹+1) ((((PL.const (2*(r:ℝ))).mul p).mul h).add (PL.const 1)) r).mul ((PL.const 1).add ((PL.const 2).mul h))
lemma nonneg_harm (p:0<a)(v:0≤C) : 0≤harm r a C:=budget_nonneg (thin_count r a C p v) -- tune
end YM.CF.BPress
