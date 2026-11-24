import YM.SatinExist.Rive

/-! ## Pointvacuum analytic rotated time. One chosen axis; no Lorentz here. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)(σ:ℝ)(v:H) (f:Probe E4)
def charges (j:Axis)(σ:ℝ)(f:Probe E4): Prop:= ∀ p:E4,p∈tsupport f → 0<σ*p j

private lemma knows_height (p:E4)(u:charges j σ f)(z:ℂ)(w:z∈inside) : AnalyticAt ℂ (fun z=> f p • waveR S σ z p v) z:=by
 by_cases e:p∈tsupport f
 · let c:=σ*p j; have he:0<c:= u p e; let T:= (S.U (SEP j p)); let g(z:ℂ):= z*(↑c:ℂ); have hg:AnalyticAt ℂ g z:=analyticAt_id.mul analyticAt_const
   have ha:g z∈inside:=show 0<(g z).re from (by unfold g; simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; exact mul_pos w he)
   let A:H.Op →L[ℂ] H.space:= f p • (T.comp (ContinuousLinearMap.apply ℂ H.space v))
   apply ((A.analyticAt _).comp ((S.localHeat _ ha).comp hg)).congr
   filter_upwards [hg.continuousAt.tendsto.eventually (open_inside.mem_nhds ha)] with i hi
   show A (S.F (g i))= _; unfold waveR; rw [show oar S _=S.F (g i) from oar_in S (g i) hi]; rfl
 have he:f p = 0:= image_eq_zero_of_notMem_tsupport e; simp_rw [he,zero_smul]; exact analyticAt_const

lemma reading_inside (u:charges j σ f) : AnalyticOnNhd ℂ (fareR S σ f v) inside:=by
 let F(p:E4)(z:ℂ):= f p • waveR S σ z p v
 let Y(z:ℂ)(p:E4):= deriv (F p) z
 have Ht:Continuous (Function.uncurry F):= (f.continuous.comp continuous_fst).smul ((viewR S σ v).comp continuous_swap)
 apply DifferentiableOn.analyticOnNhd _ open_inside
 intro z p
 obtain ⟨r,v0,U⟩:= Metric.mem_nhds_iff.mp (open_inside.mem_nhds p)
 let δ:= r/3; have h0:0<δ:= div_pos v0 (by norm_num); let d:=ball z δ
 let K(x:E4):=‖f x‖*‖v‖; let K'(x:E4):=K x/δ
 have kz(w:ℂ)(u:w∈d): Metric.closedBall w δ ⊆ inside:=by
   intro x h; refine U ?_; have hv:dist w z<δ:= u; have ht:dist x w≤δ:=h; apply (dist_triangle x w z).trans_lt; unfold δ at *; linarith only [v0,hv,ht]
 have he(p:E4)(w:ℂ)(u':w∈d): ‖Y w p‖ ≤ K' p:=by
   let t':=kz w u'
   refine norm_deriv_le_of_forall_mem_sphere_norm_le h0 ⟨?_,?_⟩ (fun x _=> fare_pay ..)
   · intro x t; exact (knows_height S σ v f p u x (t' (ball_subset_closedBall t))).differentiableAt.differentiableWithinAt
   exact (Ht.comp (by fun_prop : Continuous (fun i:ℂ=>(p,i)))).continuousOn
 let a(p:E4):= (p,z)
 have hz:AEStronglyMeasurable (Y z) volume:= ((stronglyMeasurable_deriv_with_param Ht).comp_measurable (show Measurable a from (by unfold a; fun_prop))).aestronglyMeasurable
 have hw:= hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun z p=>F p z) (F':=Y) (s:=d) (μ:=volume)
    (Metric.ball_mem_nhds z h0) (Eventually.of_forall fun z=> (fare_int S z σ v f).1) (fare_int ..) hz (Eventually.of_forall fun i=> he i) (f.integrable.norm.mul_const ‖v‖|>.div_const δ) (Eventually.of_forall fun i k u0=>(knows_height S σ v f i u k (kz k u0 (mem_closedBall_self h0.le))).differentiableAt.hasDerivAt)
 exact hw.2.differentiableAt.differentiableWithinAt

private lemma dupes_surge (z:ℂ)(n:ℕ): pluck j (dupes j z σ n f)=dupes j z σ n (pluck j f):=by
 induction n with
 | zero=> rfl
 | succ n ih=>
    let e:=z*(σ:ℂ); let g:=dupes j z σ n f; let a:=pluck j g; let b:=dupes j z σ n (pluck j f)
    change pluck j (e • g+a)= e • b+pluck j b
    rw [map_add,map_smul]; change e • a + _ = _; rw [show a=b from ih]

lemma extends_stamp : Continuous (fun z=>fareR S σ (dupes j z σ n f) v z):=by
 induction n generalizing f with
 | zero => exact fareR_co ..
 | succ n ih=> change Continuous (fun z:ℂ=>fareR S σ ((z*(σ:ℂ)) • _ + pluck j (dupes j z σ n f)) v z); simp_rw [fare_plus, fare_smul,dupes_surge]; exact ((continuous_id.mul continuous_const).smul (ih f)).add (ih (pluck j f))

lemma marches_stamp (u:charges j σ f) : AnalyticOnNhd ℂ (fun z=>fareR S σ (dupes j z σ n f) v z) inside:=by
 induction n generalizing f with
 | zero => exact reading_inside S σ v f u
 | succ n ih=> change AnalyticOnNhd ℂ (fun z:ℂ=>fareR S σ ((z*(σ:ℂ)) • _ + pluck j (dupes j z σ n f)) v z) inside; simp_rw [fare_plus, fare_smul,dupes_surge]; exact ((analyticOnNhd_id.mul analyticOnNhd_const).smul (ih f u)).add (ih (pluck j f) fun p w=>u _ (SchwartzMap.tsupport_lineDerivOp_subset (basis j) f w))

lemma packet_roll (u:charges j σ f)(z:ℂ)(p:0≤z.re):
    ((z*(σ:ℂ))^(n+1)) • fareR S σ f v z = fareR S σ (dupes j z σ (n+1) f) (StampPower S n v) z:=by
 let F(x:ℂ):=((x*(σ:ℂ))^(n+1)) • fareR S σ f v x; let G(x:ℂ):=fareR S σ (dupes j x σ (n+1) f) (StampPower S n v) x
 have hv:F z=G z:=by
    obtain p|p:=lt_or_eq_of_le p
    · exact pulse_pad S n z σ v f p u
    let g(t:ℝ):= z+↑t
    have hu: Tendsto g (𝓝[>] 0) (𝓝 z):=by
       have h:Tendsto g (𝓝 0) (𝓝 (g 0)):= continuous_const.add continuous_ofReal |>.tendsto _; have hs:g 0=z:=by simp only [g,Complex.ofReal_zero,add_zero]
       rw [hs] at h; exact h.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique_of_eventuallyEq ((Continuous.tendsto (((continuous_id.mul continuous_const).pow (n+1)).smul (fareR_co S σ v f)) _).comp hu) (((extends_stamp S (n+1) σ (StampPower S n v) f).tendsto _).comp hu) ?_
    filter_upwards [self_mem_nhdsWithin] with i hi; apply pulse_pad S n (g i) σ v f _ u
    dsimp only [inside,g]; change 0< (z+(↑i:ℂ)).re; rw [Complex.add_re, Complex.ofReal_re, ← p,zero_add]; exact hi
 exact hv

-- at λ=1: recover exactly with positive time from the actual smeared profile, not merely
-- the profile through reclaim tests at single positive gap. Later apply with BOTH probes.
variable {Y:ℝ→H}
lemma loyal_stamp (p':HasCompactSupport ⇑f)(u:charges j σ f)(g:Positive S Y):
    Tendsto (fun e:ℝ=> fareR S σ f (Y e) 1) (𝓝[>] 0) (𝓝 (∫ p:E4, f p • S.U (SEP j p) (Y (σ*p j)))):=by
 let k(p:E4):=σ*p j; let F(p:E4)(v:H):=f p • S.U (SEP j p) v
 let G(p:E4):H:= F p (Y (k p))
 let A(e:ℝ)(p:E4):= f p • waveR S σ 1 p (Y e)
 have he(x:ℝ)(p:E4)(h:0<x): A x p = F p (Y (x+k p)):=by
    by_cases t:p∈ tsupport f
    · have hy:=u p t; unfold F A waveR; simp only [one_mul,ContinuousLinearMap.comp_apply]; rw [oar_thermal, g x (x+k p) h (le_add_of_nonneg_right hy.le), add_sub_cancel_left]
    have he:f p=0:= image_eq_zero_of_notMem_tsupport t; simp [F,A,he]
 have h(p:E4): Tendsto (fun e:ℝ=> A e p) (𝓝[>] 0) (𝓝 (G p)):=by
    by_cases t:p∈ tsupport f
    · have ht:Tendsto (fun e:ℝ=>e+k p) (𝓝[>] 0) (𝓝 (k p)):=by simpa only [zero_add,id] using ((tendsto_id (x:=𝓝 (0:ℝ))).mono_left nhdsWithin_le_nhds).add_const (k p)
      apply (((Continuous.tendsto (show Continuous (F p) from continuous_const.smul ((S.U (SEP j p)).continuous)) _).comp ((within_time S Y g (u p t)).tendsto.comp ht))).congr'
      filter_upwards [self_mem_nhdsWithin] with e q; exact (he e p q).symm
    have he:f p=0:=image_eq_zero_of_notMem_tsupport t; simp_rw [A,G,F,he,zero_smul]; exact tendsto_const_nhds
 obtain e|⟨r,hr,hh⟩ : tsupport f = ∅ ∨ ∃ r> (0:ℝ),∀ p∈tsupport f,r≤σ*p j:=by
   by_cases e:(tsupport f).Nonempty
   · obtain ⟨x,h,z⟩:= p'.exists_isMinOn e (f:=k) ((show Continuous k by unfold k; fun_prop).continuousOn)
     exact Or.inr ⟨_, u _ h,z⟩
   exact Or.inl (not_nonempty_iff_eq_empty.mp e)
 · have he(p:E4):f p=0:=image_eq_zero_of_notMem_tsupport (by simp only [e,notMem_empty,not_false_eq_true])
   simp only [fareR,he,zero_smul,integral_zero]; exact tendsto_const_nhds
 let u'(p:E4):= ‖f p‖ * ‖Y r‖
 refine tendsto_integral_filter_of_dominated_convergence (F:=A) u' (Eventually.of_forall fun x=>(fare_int S 1 σ (Y x) f).1) ?_ (f.integrable.norm.mul_const _) (Eventually.of_forall h)
 filter_upwards [self_mem_nhdsWithin] with e p
 refine Eventually.of_forall fun i=>?_
 by_cases q:i∈ tsupport f
 · have hp:r≤e+k i:=by have h0:0<e:=p; linarith only [show r≤k i from hh i q,h0]
   rw [he e i p]; unfold F; rw [norm_smul,S.unitary]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
   rw [g r (e+k i) hr hp]; exact ((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))
 simp only [A,image_eq_zero_of_notMem_tsupport q,u',zero_smul,norm_zero,zero_mul,le_refl]
end YM.SatinJets
