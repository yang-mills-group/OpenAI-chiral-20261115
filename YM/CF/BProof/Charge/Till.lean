import YM.CF.BProof.Charge.Input
import YM.CF.BProof.PL

/-! Price delay. Handles cut kept support permit, NPL though cubic costs running \beta,
all coefficients and loops uniform. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Push.AbsoluteSums Work Micro Moment MeasureTheory ConnectedActivityE6.Raw Next.SectorChange Real
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable (c:Clip)(W C Λ:ℝ)(h:0<W)

def reach (D y:ℝ):= ⌈D*Real.log y⌉₊
lemma reach_PL (D:ℝ)(hD:0<D): PL (fun y=>(reach D y:ℝ)) :=by
 apply PL.ceil ((PL.const D).mul PL.log_y); filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy; exact (mul_pos hD (Real.log_pos hy)).le
lemma reach_hi (D:ℝ)(hD:0<D): Tendsto (reach D) atTop atTop:=by
 rw [tendsto_atTop]; intro b; filter_upwards [(Real.tendsto_log_atTop.const_mul_atTop hD).eventually_ge_atTop (b:ℝ)] with y hx; exact_mod_cast hx.trans (Nat.le_ceil _)
lemma atom_pos {C:ℝ}(hc:0≤C): 0 ≤ atomUnit W C:=by unfold atomUnit; positivity
include h
lemma pair_pos (M:ℕ) : 0≤ pairUnit W C M := by unfold pairUnit; have ht:0≤ C*C:=mul_self_nonneg _; positivity
lemma rate_le {t β β':ℝ}(M:ℕ)(ht:0≤t)(p:|β|≤|β'|)(hc:0≤C)(hw:0≤Λ): rate t β W C Λ M≤ rate t β' W C Λ M:=by
 have hm : |β*share|≤|β'*share|:=by simp_rw [abs_mul]; gcongr
 have p0:=pair_pos W C h M; have p1:=atom_pos W hc; unfold rate trailRate; gcongr -- tune
lemma uPull_p (M:ℕ) : 0<uPull W M:=by unfold uPull ann pairRate; rw [lt_min_iff]; constructor<;> positivity
lemma uPull_PL (D:ℝ)(hD:0<D): PL (fun y=>(uPull W (reach D y))⁻¹):=by
 let B(y:ℝ):=(2*((reach D y:ℝ)+2)+1)
 have hv:PL B:= PL.add ((PL.const 2).mul ((reach_PL D hD).add (PL.const 2))) (PL.const 1)
 let A:=fun y=>Max.max (ann W)⁻¹ (8*B y^4*W⁻¹); convert PL.max (f:=fun y=> (ann W)⁻¹) (g:=fun y=>8*B y^4* W⁻¹) (PL.const _) (((PL.const 8).mul (hv.pow 4)).mul (PL.const _)) using 1
 ext x; let m:=reach D x; have ho:0<ann W:=lt_of_lt_of_le (uPull_p W h m) (min_le_left ..); have hp:0<pairRate W m:=lt_of_lt_of_le (uPull_p W h m) (min_le_right ..)
 have hx : (pairRate W m)⁻¹ = 8 * B x^4 * W⁻¹:= by unfold pairRate; rw [inv_div]; rfl
 change (min (ann W) (pairRate W m))⁻¹=A x; unfold A; rw [← hx]; rcases le_total (ann W) (pairRate W m) with h|h; rw [min_eq_left h,max_eq_left (inv_anti₀ ho h)]; rw [min_eq_right h,max_eq_right (inv_anti₀ hp h)]
omit h in
lemma store_valid : ∀ᶠ D:ℝ in atTop, 0<D∧ ∀ᶠ y:ℝ in atTop,∀ p:BudgetPoint,p.threshold=thresh y→ ValidR c p (reach D y):=by
 have hr:= c.radius_pos; filter_upwards [eventually_ge_atTop c.relaxation] with D hD; refine ⟨hr.trans_le hD,?_⟩
 -- t smaller? t≥ y^-1/2; exp≥y. use weaker t> 2/y
 filter_upwards [eventually_gt_atTop (1:ℝ),coin_budget (a:=-1) (b:=0) (c:=0) (d:=-1/2) (e:=1) (f:=0) (by norm_num) 2 1 one_pos] with y hy ht
 intro p g b e; by_contra q; have he: reach D y≤ b:=by omega
 have hp:0<y:=one_pos.trans hy
 have hv : (b:ℝ)/c.relaxation ≥ Real.log y := by
    have hi: Real.log y*c.relaxation ≤ D*Real.log y:=by rw [mul_comm]; gcongr; exact (Real.log_pos hy).le
    exact (le_div_iff₀ hr).2 ((hi.trans (Nat.le_ceil _)).trans (Nat.cast_le.mpr he))
 have hh: y ≤ Real.exp ((b:ℝ)/ c.relaxation):= (Real.exp_log hp) ▸ Real.exp_monotone hv
 have h:2/y≤p.threshold:=by rw [g,div_eq_mul_inv,show y⁻¹=coin y (-1) 0 0 from by nth_rw 1 [←coinY hp]; rw [coin_inv]; simp]; simpa only [one_mul] using ht.le
 have h':= mul_le_mul_of_nonneg_left hh p.threshold_pos.le; exact not_lt_of_ge (le_trans ((div_le_iff₀ hp).1 h) h') e

lemma reach_pair : ∀ᶠ D:ℝ in atTop, NPL (fun y=> y*pairUnit W C (reach D y)):=by
 filter_upwards [eventually_ge_atTop (4/W)] with D hD
 have ht:0<D:=lt_of_lt_of_le (by positivity) hD
 let P(y:ℝ):=(2*((reach D y:ℝ)+2)+1); let K:= (2*Real.exp W)*((W/4)⁻¹^4*(4:ℕ).factorial*Real.exp (W/4))*(C*C)
 have hp:PL P:= PL.add ((PL.const 2).mul ((reach_PL D ht).add (PL.const 2))) (PL.const 1); have hk:0≤K:=by unfold K; have he:=mul_self_nonneg C; positivity
 refine NPL.by_le (((PL.const K).mul (hp.pow 4)).muln (coin_n (a:= -1) (b:=0) (c:=0) (by norm_num))) ?_ -- tune
 filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy
 have hZ:0<y:=one_pos.trans hy; have ht : 4 ≤ W*D:= by rw [mul_comm]; exact (div_le_iff₀ h).1 hD
 let m:=reach D y; have h': -(W/2*m)≤ Real.log y * (-2):= by have hh: D*Real.log y≤ (m:ℝ):= Nat.le_ceil _; nlinarith only [mul_le_mul_of_nonneg_left hh h.le,mul_le_mul_of_nonneg_right ht (Real.log_pos hy).le]
 have he:y* Real.exp (-(W/2*m))≤coin y (-1) 0 0:=by
   apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone h') hZ.le); unfold coin; simp only [mul_zero, add_zero]; nth_rw 1 [←Real.exp_log hZ]; rw [← Real.exp_add]; ring_nf; exact le_rfl
 let q:=y*pairUnit W C m; have hv:q=K*P y^4*(y*Real.exp (-(W/2*m))):=by unfold q K P m pairUnit; ring
 have hv': 0≤ q:=mul_nonneg hZ.le (pair_pos W C h m)
 change |q| ≤ _; rw [abs_of_nonneg hv',hv]; exact (mul_le_mul_of_nonneg_left he (by positivity : 0≤K*P y^4)).trans (le_abs_self _)

lemma rates_buy (hc:0≤C) (hl:0≤Λ) : ∀ᶠ D:ℝ in atTop, NPL (fun y=>rate (thresh y) (2*y) W C Λ (reach D y)):=by
 filter_upwards [reach_pair W C h] with D hx
 let v(y:ℝ):=trailRate (thresh y) (2*y) W C Λ (reach D y)
 apply PL.muln (PL.const _) (g:=v)
 have he:NPL (fun y=> |2*y*share| * pairUnit W C (reach D y)):= by
    refine NPL.by_le ((PL.const (2*share)).muln hx) ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy; rw [abs_of_nonneg (by have :=share_pos; positivity : 0≤2*y*share)]; ring_nf; exact le_rfl
 have h2:NPL (fun y=> |share| *thresh y^2):=by
    apply (PL.const |share|).muln; convert coin_n (a:=-1) (b:=2) (c:=0) (by norm_num) using 1; ext x; rw [coin_pow]; ring_nf
 have h3(n:ℕ)(k:3≤n):NPL (fun y=>|2*y*share| *thresh y^n):=by
    have hh:-1/2*(n:ℝ)+1 < 0:=by have h':3≤(n:ℝ):=(by exact_mod_cast k); linarith
    apply NPL.by_le ((PL.const (2*share)).muln (coin_n (b:=n) (c:=0) (Or.inl hh))); filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy; rw [abs_of_nonneg (by have :=share_pos; positivity : 0≤2*y*share)]
    apply le_of_eq; congr 1; rw [coin_pow]; nth_rw 1 [← coinY hy]; rw [show (2:ℝ)*coin y 1 0 0*share=2*share*coin y 1 0 0 by ring,mul_assoc,coin_mul]; ring_nf -- tune
 exact ((PL.const _).muln he).add (((PL.const _).muln h2).add (((PL.const _).muln (h3 3 le_rfl)).add ((PL.const _).muln (h3 4 (by decide)))))
end YM.CF.BProof.Charge
