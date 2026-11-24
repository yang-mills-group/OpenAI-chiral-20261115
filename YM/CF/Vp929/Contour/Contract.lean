import YM.CF.Vp929.Analysis.Bernstein
import YM.CF.Vp929.Contour.Accounts
set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate
open Complex VolumeRate Metric Function Filter Topology Set
namespace Portfolio
variable {X:Type*}[Sub X]{c: Book X}{h: Looks X}{U:ℂ→ Pair X}{s α d D R:ℝ}
include h
lemma tilt_knots (p:Portfolio c h)(pd:0 ≤ d)(pD:0 ≤ D)(vT:4≤R)(u: Valid c h (ball (0:ℂ) (R+1)) U)(e:∀ x∈ball (0:ℂ) (R+1), Both (fun k=>c k D) (U x))(k:∀ i:ℕ,i<6 → Both (fun k=>c k d) (U ((i:ℂ)/8))): Both (fun k=>c k (100^6*(2*d+(2*D)/R^6))) (U I):= by
 have hv:I∈ball (0:ℂ) (R+1):= mem_ball_zero_iff.mpr (by rw [norm_I]; linarith); have B:= e I hv; refine p.evaluate ⟨⟨_,B.1⟩,⟨_,B.2⟩⟩ _ fun F H w=>?_ ; let t:= u.2.1; apply of_knots (f:=fun z=>probing F (U z)) (z:=I) 6 le_rfl (mem_ball_zero_iff.mpr (by rw [norm_I]; norm_num)) (by linarith: 0≤2*d) (by linarith:0 ≤ 2*D) vT _ (fun i l=> Accountable.norm_le p w (k i l)); swap
 · exact ((show Accountable c h F from H).liable _ _ u).mono (closedBall_subset_ball (by linarith))
 exact fun i hi=> Accountable.norm_le p w (e i (closedBall_subset_ball (by linarith:R< R+1) hi))

lemma offPivot (p:Portfolio c h)(pd:0<d)(ht:d≤D)(v:Valid c h (ball (0:ℂ) (5*α)) U)(hE:∀ x∈ ball (0:ℂ) (5*α), Both (fun k=> c k D) (U x))(u:∀ x:ℝ,|x|≤ 2*α → Both (fun k=>c k d) (U x))(a:0<α)(hb:|s| ≤ α)(lp:(Real.log (2*D)-Real.log (2*d)) * |s| / α / Real.log 3 ≤ Real.log 2) : Both (fun k=>c k (4*d)) (U (I*s)):= by
 have hρ:= hE _ (show (I*s:ℂ)∈ball 0 (5*α) from mem_ball_zero_iff.mpr (by rw [norm_mul,norm_I,norm_real,Real.norm_eq_abs]; linarith)); refine p.evaluate ⟨⟨_,hρ.1⟩,⟨_,hρ.2⟩⟩ _ fun F H w=>?_ ; let f(z):= probing F (U z)
 have A:0<2*d:=by linarith
 have B:0< 2*D:=by linarith
 have he (x)(p':x∈ball (0:ℂ) (5*α)):‖f x‖ ≤ Real.exp (Real.log (2*D)):= (Accountable.norm_le p w (hE x p')).trans_eq (Real.exp_log B).symm
 have hm(x:ℝ)(hy:|x|≤ 2*α):‖f x‖ ≤ Real.exp (Real.log (2*d)):= (Accountable.norm_le p w (u x hy)).trans_eq (Real.exp_log A).symm
 have ha:= off_line (f:=f) α a s hb (Real.log_le_log A (by linarith:2*d≤2*D)) ((show Accountable c h F from H).liable _ _ v) he hm
 refine ha.trans ((Real.exp_monotone (add_le_add_right lp (Real.log (2*d)))).trans_eq ?_); rw [Real.exp_add,Real.exp_log A,Real.exp_log zero_lt_two]; ring
end Portfolio
end YM.CF.Py.Rate
