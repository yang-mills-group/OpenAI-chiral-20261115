import YM.CF.BPress.Scale
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Filter Pressure
open scoped Topology

def heigh (y : ℝ) := drift y ^ (1/8 : ℝ)
def root (y : ℝ) := g y ^ (1/2 : ℝ)
variable {y : ℝ}
lemma rise (y : ℝ) : 1 ≤ heigh y:= Real.one_le_rpow (drift_one y) (by norm_num)
lemma heigh_pos (y : ℝ) : 0< heigh y:=zero_lt_one.trans_le (rise y)
lemma root_pos (p : 0<y) : 0<root y:= Real.rpow_pos_of_pos (g_pos p) _
lemma npl_congr {F G : ℝ → ℝ} (h : ∀ᶠ i in atTop,F i= G i) (t:NPL F): NPL G:=t.mono (h.mono fun i v=> by rw [v])
lemma drift_price (y : ℝ) : drift y=heigh y^8:= by unfold heigh; rw [← Real.rpow_natCast,←Real.rpow_mul (drift_pos y).le]; norm_num
lemma root_price (h : 0<y) : g y=root y^2:= by unfold root; rw [← Real.rpow_natCast,←Real.rpow_mul (g_pos h).le]; norm_num
lemma temp_price (h : 0<y) : temp y=root y ^2 * heigh y ^8:= by rw [temp_eq, drift_price,root_price h]
lemma mA_price (h : 0<y) : mA y=root y^2 * heigh y ^6:= by
  unfold mA; have he: drift y ^ ((1:ℝ)/4)=heigh y^2:=by unfold heigh; rw [← Real.rpow_natCast,←Real.rpow_mul (drift_pos y).le]; norm_num
  rw [temp_price h, he]; have ht:=heigh_pos y; field_simp
lemma wc_price (h : 0<y) : wc y=root y^2* heigh y ^4:= by
  have ht:= heigh_pos y; unfold wc; rw [temp_price h,drift_price y,show heigh y ^ 8=(heigh y ^4)^2 by ring,Real.sqrt_sq (by positivity)]; field_simp
lemma aA_sq (p : 0<y) : aA y^2=mA y:=Real.sq_sqrt (mA_pos p).le
lemma aA_price (h : 0<y) : aA y=root y * heigh y ^3:= by apply (sq_eq_sq₀ (aA_positive h).le (mul_pos (root_pos h) (pow_pos (heigh_pos _) _)).le).mp; rw [aA_sq h,mA_price h]; ring
lemma xi_price (h : 0<y) : xi y=root y ^6:=by rw [xi,root_price h]; ring
lemma sigma_price (y : ℝ) : sigmaN y=(heigh y)⁻¹:=by unfold heigh sigmaN; rw [neg_div,Real.rpow_neg (drift_pos y).le]
lemma hat_price (h : 0<y) : (root y)^4 = y⁻¹:= (show root y^4=(root y^2)^2 by ring)|>.trans <| by rw [←root_price h,gscale h.le]
lemma heigh_npl : NPL (fun i=> (heigh i)⁻¹):= npl_drift (1/8) (by norm_num)
lemma npl_sigmaN : NPL sigmaN:= npl_congr (Eventually.of_forall fun _=> (sigma_price _).symm) heigh_npl
lemma root_tall (k : ℤ) (n : ℕ) (p : 0<n) : NPL fun y=> root y^n * heigh y ^ k:= by
  refine npl_congr (F:=fun y=> drift y ^ ((1:ℝ)/8*(k:ℝ))*g y ^ ((1:ℝ)/2*(n:ℝ))) ((eventually_gt_atTop (0:ℝ)).mono fun y p=>?_) (npl_drift_g _ _ (by positivity)); rw [Real.rpow_mul (g_pos p).le, Real.rpow_mul (drift_pos y).le, Real.rpow_natCast,Real.rpow_intCast,mul_comm]; rfl
lemma npl_aA : NPL aA:= npl_congr (F:=fun i=> root i^1*heigh i^(3:ℤ)) ((eventually_gt_atTop (0:ℝ)).mono fun y p => by rw [aA_price p,pow_one]; rfl) (root_tall _ _ (by decide))
lemma npl_wc : NPL wc:= npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun y p => (wc_price p).symm) (root_tall 4 2 (by decide))
lemma npl_xi : NPL xi:= by refine npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun y p => (xi_price p).symm) ?_; simpa only [zpow_zero,mul_one] using root_tall 0 6 (by decide)
lemma npl_a1 (F G : ℝ → ℝ) (h : NPL (fun i=>F i/G i)) {c : ℝ} (p : 0<c) (v : ∀ᶠ i in atTop, 0<G i) :
    ∀ᶠ i in atTop, F i < c * G i := ((h.drop.eventually (gt_mem_nhds p)).and v).mono fun i e=> (div_lt_iff₀ e.2).mp e.1
lemma npl_power {F : ℝ→ℝ} (t : NPL F) (k : ℕ) (p : 0<k) : NPL fun i=> F i ^ k:=by
 obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero p.ne'; simpa only [pow_succ'] using t.mul (t.pl.pow n)
end YM.CF.BPress
