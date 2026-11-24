import Zephyr.Chern.Signal
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology Silk YM.CF YM.CF.Fir YM.Next.Free YM.CF.Jill


open scoped Real
variable {j:ℕ} {r: Male → Streams}

private lemma spear {z:ℂ} {f:ℝ→ℂ} {K:ℝ} (p : f 0=0)
    (g : ∀ᶠ t in 𝓝[≠] (0:ℝ), ‖f t-t*z‖≤K*|t|^2) :
    HasDerivAt f z 0 := by
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g:=fun t=> K*|t|) (Eventually.of_forall fun _=>norm_nonneg _) ?_ ?_
  · filter_upwards [g,self_mem_nhdsWithin] with t h (hne : t≠0)
    have d : 0 < |t| := abs_pos.mpr hne
    rw [slope_def_module,p,sub_zero,sub_zero,
      show t⁻¹ • f t-z=t⁻¹ • (f t-t*z) by rw [←Complex.real_smul,smul_sub,inv_smul_smul₀ hne],
      norm_smul, norm_inv, Real.norm_eq_abs,inv_mul_le_iff₀ d]
    linarith -- tune
  · simpa using ((tendsto_id (α:=ℝ)).mono_left
      (nhdsWithin_le_nhds (a:=(0:ℝ)))).abs.const_mul K

lemma Looming.tangent (p : Looming j r) (hj: 1≤j) (M:Male) (a b : Axis) :
    E 0 (D a (r M b.succ))=(if a=b then 1 else 0) := by
  let X := r M b.succ
  have he:= E_along a X 0
  rw [Pi.single_zero,rad_zero] at he
  refine he.unique ?_
  obtain ⟨s,K,hs,hK,H⟩ := (go_b (t:=crop) RayH.x (fun _=>rfl) RayH.cap).coldS
    (fun i=>i.M.val) (fun i=>i.M.prop) j hj b
  apply spear (K:=2*K)
  · rw [Pi.single_zero,rad_zero]; exact (p.origin M).2 _

  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Metric.ball_mem_nhds _ Real.pi_pos)] with t (hne : t≠0) ht
  rw [Metric.mem_ball,Real.dist_eq,sub_zero] at ht
  let x : Bin:=Pi.single a t
  have hn : ‖x‖=|t| := by rw [show x=Pi.single a t from rfl,Pi.norm_single,Real.norm_eq_abs]
  have bw:Bound π x:=hn.le.trans ht.le
  let i:RayH:=⟨M,x,bw,hn.symm ▸ abs_pos.mpr hne⟩
  have h:= (H i 0 (by simpa using hs)).2
  change ‖skin j M.val (tmap x) b-1/2*tmap x b‖≤K*‖x‖^(2:ℤ) at h
  rw [hn,zpow_ofNat] at h
  have e : (t:ℂ)*(if a=b then 1 else 0) = tmap x b := by
    by_cases a=b
    · subst b; simp [x,tmap]
    rename_i g; simp [g,x,tmap]

  change ‖E (radians x) (r M b.succ)-_‖≤_
  rw [e,p.plays M x bw,signal_tail,show 2*skin j M.val (tmap x) b-tmap x b=
    2*(skin j M.val (tmap x) b-1/2*tmap x b) by ring,
    norm_mul, show ‖(2:ℂ)‖=2 by norm_num, mul_assoc 2 K]
  gcongr
