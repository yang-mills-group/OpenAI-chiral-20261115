import YM.CF.Newt.Source
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ: Type} [Fintype ι] [Fintype τ] {A N C P d y s r v U:ℝ} {n:ℕ}
variable {f f':Positions (ι⊕τ)→ℝ}{z m: Fish ι → Fish τ}{Pi₁: Fish ι → Fish τ →L[ℝ] Fish τ}{x:Fish ι}
-- scaled z model implicitly uses (s•x). K jet in scaled variables.
def firmly (n:ℕ)(C P D m s:ℝ): ℝ:= 2^n*P*composeCost n D 1+2^n*P*(2^n * composeCost n C 1 * m*s) -- don't use
lemma meets_n : ‖(Uniform.partSpace ι τ).symm.toContinuousLinearMap‖≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; rintro ⟨x,y⟩; rw [one_mul]; exact (Uniform.norm_meet x y).le
lemma turn_safe (h:Allows n m x (A*s))(h':Allows n z x (A*s))(hs:0≤s)(p:1≤A)(hp:‖x‖<1)(t:ℝ)(ht:t∈interval):
 Allows n (fun x=>meetVar (s • x) (z x + t • (m x-z x))) x (3*A*s):=by
 have hq := (subtract_p h h').smul t; rw [abs_of_nonneg ht.1] at hq
 let O:=s • ContinuousLinearMap.id ℝ (Fish ι); have ha: ‖O‖≤s:=pole0 s _ (Fish τ) hs; have hx:Allows n (fun x:Fish ι=>s • x) x s:=allows_linear (L:=O) ha ((O.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) hp.le).trans ha))
 refine (((hx.mono (show s ≤ 3*A*s by nlinarith only [mul_le_mul_of_nonneg_right p hs, hs])).pair ((h'.add hq).mono (show _ ≤ 3*A*s by nlinarith only [mul_le_mul_of_nonneg_right ht.2 (add_nonneg h.nonneg h.nonneg)]))).linear _ meets_n).mono (one_mul _).le
set_option maxHeartbeats 700000 in
lemma flow_buy (ha:1≤A)(hs:0<s)(h:∀ x': Fish ι, ‖x'‖<1→ Allows n z x' (A*s) ∧ Allows n m x' (A*s)∧ Slope f (meetVar (s•x') (z x'))=0)(hB:3*A*s<r)
 (hn:3*A*s≤1)(hv:Allows n (fun y=>m y-z y) x U)(hh:‖x‖<1)(hp:∀ w:Positions (ι⊕τ), ‖w‖<r→ ContDiffAt ℝ ω f w ∧ Allows n (fun y=> paintO (block f y)) w C)(hl:1 ≤ n):
 let L:=paintO (block f 0)
 Allows n (fun x'=>Slope f (meetVar (s•x') (m x'))-L (m x'-z x')) x (2^n*composeCost n (C*(3*A*s)) 1*U):=by
 intro L; let u(y:Fish ι):=m y-z y
 let w(y:Fish ι×ℝ) := meetVar (s • y.1) (z y.1+y.2 • u y.1)
 let Z(y:Fish ι×ℝ):= paintO (block f (w y)); let F(y:Fish ι×ℝ):=(Z y - L) (u y.1)
 have hW y (hy:‖y‖<1) t ht: Allows n (fun a=>w (a,t)) y (3*A*s):= turn_safe (h y hy).2.1 (h y hy).1 hs.le ha hy t ht
 have hr y (hy:‖y‖<1) t ht:=hp (w (y,t)) ((hW y hy t ht).value.trans_lt hB)
 have HU (y:Fish ι) (hy:‖y‖<1):ContDiffAt ℝ (n:WithTop ℕ∞) u y:= (h y hy).2.1.smooth.sub (h y hy).1.smooth
 have hw y (hy:‖y‖<1): Arc w n y:=by
    intro t ht; unfold w meetVar
    apply (Uniform.partSpace ..).symm.contDiff.contDiffAt.comp (f:=fun p=> (s • p.1,z p.1+p.2 • u p.1)) (y,t)
    exact (contDiffAt_fst.const_smul _).prodMk ((((h y hy).1.smooth).comp _ contDiffAt_fst).add (contDiffAt_snd.smul ((HU y hy).comp (y,t) contDiffAt_fst)))
 have hT(y:Fish ι)(hy:‖y‖<1): Arc F n y:=fun t ht=>((((hr y hy t ht).2.smooth.comp _ (hw y hy t ht)).sub contDiffAt_const).clm_apply ((HU y hy).comp (y,t) contDiffAt_fst))
 have hZ t (ht:t∈interval): Jet.Allows n (fun y=> Z (y,t)-L) x (composeCost n (C*(3*A*s)) 1):= point_ne (E:=Fish (ι⊕τ)) (M:=3*A) (f:=fun y=> paintO (block f y)) (hW x hh t ht) (fun w h=> (hp w h).2) hl hs (by linarith only [ha]) hn hB
 have HK t (ht:t∈interval): Allows n (fun y=>F (y,t)) x (2^n*composeCost n (C*(3*A*s)) 1*U):= appliance (hZ t ht) hv
 have H:= spirit (g:=F) (hT _ hh) HK
 apply H.germ; filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hh)] with v (ht: v∈ball (0:Fish ι) 1)
 have hx : ‖v‖<1:= mem_ball_zero_iff.mp ht
 let B(t:ℝ):= Slope f (w (v,t))- t • (L (u v))
 have hh t (ht:t∈interval) : HasDerivAt B (F (v,t)) t:=by
    let s':=z v + t • u v; let y':=s • v; have H':= Uniform.slope_block (show ContDiffAt ℝ ω f (meetVar y' s') from (hr v hx t ht).1)
    have hd: HasDerivAt (fun t:ℝ=> z v + t • u v) (u v) t:= by simpa using (((hasDerivAt_id' t).smul_const (u v)).const_add (z v))
    have hv: HasDerivAt (fun x=>w (v,x)) (lowerCol (ι:=ι) (u v)) t:= by
        let q(w:ℝ):= z v+w • u v; change HasDerivAt (meetVar y' ∘ q) _ t; exact (meet_derivative y' (q t)).comp_hasDerivAt (f:=q) t hd
    have hp:HasDerivAt (Slope f ∘ (fun t=> w (v,t))) (paintO (block f (w (v,t))) (u v)) t:= by
        erw [paintO_p]
        rw [← tree_der (w (v,t)) (hr v hx t ht).1 (u v)] -- via Δ rewrite needs
        exact (H'.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hv
    exact hp.sub (show HasDerivAt (fun t:ℝ=>t • (L (u v))) (L (u v)) t by simpa using ((hasDerivAt_id' t).smul_const (L (u v))))
 change (∫ t in Icc 0 1,F (v,t)) = _
 rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=B) (fun x hx'=>hh x (by simpa only [uIcc_of_le zero_le_one] using hx')) ((hT v hx).slice.intervalIntegrable_of_Icc zero_le_one),show B 0=0 by unfold B w; simp [(h v hx).2.2], sub_zero]
 unfold B w u; simp
end YM.CF.Newt
