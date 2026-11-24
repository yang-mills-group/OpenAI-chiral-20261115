/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Voyager.Clothes
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
/-! # Exponential approximation on an arc. Buy propagation across second angular
coordinate without Euler exponential accuracy near complex strip of fixed width.
Input bound uniform real, growth arbitrary exponential in ball. -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric Bornology Asymptotics Complex
open scoped NNReal ENNReal Topology InnerProductSpace Complex ComplexConjugate ComplexOrder BigOperators
private abbrev upperQ(r:ℝ): Set ℂ:= Icc (-r) r ×ℂ Icc 0 r
private def blockQ(r:ℝ)(c:ℝ)(x:ℂ):= cexp (((c:ℝ):ℂ)*((-x)*x + 3 * ((r:ℝ):ℂ)*I*x))
lemma quark {r:ℝ}(hr:0<r) (c:ℝ)(x:ℂ): ‖blockQ r c x‖= Real.exp (c*(-x.re^2+x.im^2-3*r*x.im)):= by unfold blockQ; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re,Complex.mul_im]; left; ring
private lemma otherS (f:ℂ→ℂ){r c ρ γ:ℝ}(n:ℕ)(p:0<r)(v:0<c)(t:0<ρ)(b:0<γ)(x:ℂ)(e:x∈upperQ r)
 (hd:DifferentiableOn ℂ f (closedBall 0 (2*r)))(hx:∀ y∈ closedBall (0:ℂ) (2*r), ‖f y‖≤c^n)(hy:∀ y∈closedBall (0:ℝ) (2*r),‖f y‖≤ρ^n) -- coerces y autoly?
 (hγ: Real.exp (γ*(-r^2))*c ≤ ρ) : ‖blockQ r γ x ^ n * f x‖ ≤ ρ^n:=by
 let U:= Ioo (-r) r ×ℂ Ioo 0 r; have he:closure U=upperQ r:=by unfold U; rw [ closure_reProdIm,closure_Ioo (neg_lt_self p).ne, closure_Ioo p.ne]
 have hv:upperQ r ⊆ closedBall 0 (2*r):=by intro x p; rw [mem_closedBall_zero_iff]; have hu : |x.im| ≤ r:= (abs_of_nonneg p.2.1).trans_le p.2.2; apply (norm_le_abs_re_add_abs_im _).trans; linarith [abs_le.mpr (show -r ≤ x.re ∧ x.re ≤ r from p.1)]
 let B(y:ℂ):=blockQ r γ y^n; have hB: Differentiable ℂ B:=by unfold B blockQ; fun_prop
 refine norm_le_of_forall_mem_frontier_norm_le ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) (U:=U) (f:=fun z=>B z*f z) ⟨hB.differentiableOn.mul (hd.mono (subset_closure.trans (he.symm ▸ hv))),hB.continuous.continuousOn.mul (hd.continuousOn.mono (he.symm ▸ hv))⟩ (fun z pz=> ?_) (he.symm ▸ e)
 unfold B; have he':z ∈ upperQ r:= he ▸ frontier_subset_closure pz
 change ‖(blockQ _ _ z)^n*f z‖≤ _; rw [norm_mul,norm_pow,quark p]
 by_cases h:z.im=0
 · have hz:(z.re:ℂ)=z:= Complex.ext (by simp) (by rw [h]; rfl)
   have hu:z.re∈closedBall 0 (2*r):=by rw [mem_closedBall_zero_iff,Real.norm_eq_abs]; linarith [abs_le.mpr (show -r≤ z.re ∧ z.re≤ r from he'.1)]
   have ht:=hy z.re hu; rw [hz] at ht; apply le_trans (mul_le_of_le_one_left ?_ ?_) ht -- syntax
   · exact norm_nonneg _
   apply pow_le_one₀ (by positivity); rw [h]; apply Real.exp_le_one_iff.mpr
   nlinarith [mul_nonneg b.le (sq_nonneg z.re)]
 have hz: -z.re^2+z.im^2-3*r*z.im≤ -r^2:=by
    have hp:0 < z.im:= lt_of_le_of_ne (show 0 ≤ z.im from he'.2.1) (Ne.symm h)
    have ht:z.im≤r:=he'.2.2
    unfold U at pz; rw [frontier_reProdIm, closure_Ioo (neg_lt_self p).ne, frontier_Ioo p, closure_Ioo p.ne, frontier_Ioo (neg_lt_self p)] at pz
    cases pz with
    | inl h' => have hy:z.im=r:= (show z.im=0 ∨ z.im=r from h'.2).resolve_left h; rw [hy]; nlinarith [sq_nonneg z.re]
    | inr h' => rcases (show z.re=-r∨ z.re=r from h'.1) with h | h <;> rw [h] <;> nlinarith
 calc _ ≤ (Real.exp (γ*(-r^2)))^n * c^n:= mul_le_mul (pow_le_pow_left₀ (by positivity) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz b.le)) _) (hx _ (hv he')) (by positivity) (by positivity)
      _ ≤ _:= by rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hγ n
private theorem interiorC {r c w w':ℝ}(qr:0<r)(p:0<c)(u:0<w)(t:w<w')(v:w'<1): ∃ d,0<d∧ d ≤ 2*r∧ ∀ n:ℕ,∀ f:ℂ→ℂ,DifferentiableOn ℂ f (closedBall 0 (2*r))→
    (∀ z ∈ closedBall (0:ℂ) (2*r), ‖f z‖≤c^n)→ (∀ z∈closedBall (0:ℝ) (2*r),‖f z‖≤w^n)→∀ z∈ball (0:ℂ) d,‖f z‖≤ w'^n:=by
 have hv:Tendsto (fun a:ℝ=> Real.exp (a*(-r^2))*c) atTop (𝓝 0):=by simpa using (Real.tendsto_exp_atBot.comp (show Tendsto (fun a:ℝ=>a*(-r^2)) atTop atBot from tendsto_id.atTop_mul_const_of_neg (by nlinarith))).mul_const c
 obtain ⟨k,h₁,h₂⟩:=((hv.eventually (ge_mem_nhds u)).and (eventually_gt_atTop (0:ℝ))).exists
 let B:= blockQ r k; have hB:Continuous (fun z:ℂ=>‖B z‖):= by unfold B blockQ; fun_prop
 have h0:w/w'< ‖B 0‖:=by unfold B blockQ; simpa using (div_lt_one (u.trans t)).2 t
 obtain ⟨d,hd,H⟩:= Metric.mem_nhds_iff.mp ((hB.continuousAt.tendsto).eventually (lt_mem_nhds h0)) -- gt_mem etc tune
 let D:=min r d; refine ⟨D,lt_min qr hd, (min_le_left ..).trans (by linarith),?_⟩
 have he:(ball (0:ℂ) D)⊆ closedBall (0:ℂ) r:=ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_left ..))
 have hp(n:ℕ)(f:ℂ→ℂ)(P:DifferentiableOn ℂ f (closedBall 0 (2*r)))(F:∀ z∈closedBall (0:ℂ) (2*r),‖f z‖≤ c^n)(G:∀ z∈closedBall (0:ℝ) (2*r),‖f z‖≤ w^n) (x:ℂ)(v:x∈ball (0:ℂ) D)(y:0≤x.im): ‖f x‖≤w'^n:=by
    have hx: ‖x‖≤r:= mem_closedBall_zero_iff.mp (he v); have hz: x∈upperQ r:=⟨abs_le.mp ((abs_re_le_norm x).trans hx), y, (im_le_norm x).trans hx⟩
    have ha:=otherS f n qr p u h₂ x hz P F G h₁; have hc:w ≤ ‖B x‖*w':=(div_le_iff₀ (u.trans t)).1 (le_of_lt (show w/w'<‖B x‖ from H (ball_subset_ball (min_le_right ..) v)))
    have h':0 < ‖B x‖:=by unfold B; rw [quark qr]; positivity
    apply le_of_mul_le_mul_left ?_ (pow_pos h' n); rw [norm_mul,norm_pow] at ha; exact ha.trans ((pow_le_pow_left₀ u.le hc n).trans_eq (mul_pow ..))
 intro n f P F G z hz; by_cases h:0 ≤ z.im; · exact hp n f P F G z hz h
 let f'(w:ℂ):=f (-w); have hg:f z=f' (-z):=by simp [f']
 have h'(z:ℂ)(d:ℝ)(h:z∈closedBall 0 d) : -z∈ closedBall 0 d:=by simpa only [mem_closedBall_zero_iff,norm_neg] using h
 rw [hg]; apply hp n f' (P.comp (differentiable_neg.differentiableOn) (fun z h=>h' z _ h)) (fun z h=>F _ (h' z _ h)) (fun z h=>?_) ( -z) (by simpa using hz) (by rw [neg_im]; exact neg_nonneg.mpr (le_of_not_ge h))
 simpa [f'] using G (-z) (by simpa using h)
private lemma growth_analytic {d c k:ℝ} (h:0<d)(hk:0<k)(hk':k<1) (v:0<c)(F:ℕ→ℂ→ℂ)(f:ℝ→ℂ)
 (x:∀ᶠ n:ℕ in atTop,DifferentiableOn ℂ (F n) (closedBall 0 (2*d))∧ ∀ z∈ closedBall (0:ℂ) (2*d),‖F n z‖≤ c^n)
 (y:∀ᶠ n:ℕ in atTop,∀ z∈ closedBall (0:ℝ) (2*d), ‖F n z-f z‖≤ k^n) : AnalyticAt ℝ f 0:=by
 obtain ⟨a,ha,ha'⟩:= exists_between hk'; obtain ⟨b,hb,hb'⟩:= exists_between ha'; let C: Set ℂ:= closedBall 0 (2*d); let C': Set ℝ:= closedBall 0 (2*d)
 let D(n:ℕ):= fun z:ℂ=>F (n+1) z-F n z; let c':=c+1; have v':c<c':=lt_add_one ..
 obtain ⟨u,e,U,Y⟩:= interiorC h (v.trans v') (hk.trans ha) hb hb'; let S:= ball (0:ℂ) u; have hs:S⊆C:= ball_subset_closedBall.trans (closedBall_subset_closedBall U)
 have he : ∀ᶠ n:ℕ in atTop, ∀ z∈S, ‖D n z‖≤ b^n:=by
     filter_upwards [x,tendsto_add_atTop_nat 1|>.eventually x,y,tendsto_add_atTop_nat 1|>.eventually y, least v v' (c+1), least hk ha (k+1)] with n ⟨p,l⟩ ⟨p',l'⟩ h₁ h₂ x' y'
     apply Y n (D n) (p'.sub p); · intro t ht; exact (norm_sub_le ..).trans ((add_le_add (l' t ht) (l t ht)).trans ((by rw [pow_succ]; ring : c^(n+1)+c^n=(c+1)*c^n).trans_le x'))
     intro t ht; have hx:D n t=(F (n+1) t-f t)-(F n t-f t):=by unfold D; simp
     rw [hx]; exact (norm_sub_le ..).trans ((add_le_add (h₂ t ht) (h₁ t ht)).trans ((by rw [pow_succ]; ring : k^(n+1)+k^n=(k+1)*k^n).trans_le y'))
 obtain ⟨p,Y'⟩:= (he.and x).exists_forall_of_atTop -- check
 let g(z:ℂ):= F p z+(∑' i:ℕ,D (p+i) z)
 have ht:∀ i:ℕ, p≤p+i:=fun i=>by omega
 have hz(i:ℕ)(z:ℂ)(hz:z∈S): ‖D (p+i) z‖≤b^p*b^i:=(Y' (p+i) (ht i)).1 z hz|>.trans_eq (pow_add ..)
 have h' : 0<b:= hk.trans (ha.trans hb); have hy:Summable (fun i:ℕ=>b^p*b^i):=(summable_geometric_of_lt_one h'.le hb').mul_left _
 have hy':AnalyticAt ℂ g 0:= ((DifferentiableOn.analyticOnNhd (((Y' p le_rfl).2.1.mono hs).add (differentiableOn_tsum_of_summable_norm hy (fun i=>(((Y' _ (show p≤p+i+1 from by omega)).2.1.sub (Y' _ (ht i)).2.1).mono hs)) isOpen_ball hz)) isOpen_ball) _ (mem_ball_self e)) -- tune
 have hb(z:ℝ)(u':|z| < u): g z=f z:=by
     have he:(z:ℂ) ∈ S:=by simpa [S,norm_real,Real.norm_eq_abs] using u'
     have hu:z∈ C':=by simpa [C',norm_real,Real.norm_eq_abs] using (show (z:ℂ)∈closedBall 0 (2*d) from hs he)
     have hG:Tendsto (fun n=> F n z) atTop (𝓝 (f z)):= by rw [tendsto_iff_norm_sub_tendsto_zero]; exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (y.mono fun n h=>h z hu) (tendsto_pow_atTop_nhds_zero_of_lt_one hk.le hk')
     have hg:= ((Summable.of_norm_bounded hy (fun n=>hz n z he)).hasSum.tendsto_sum_nat).const_add (F p z)
     refine tendsto_nhds_unique (hg.congr (fun n=> ?_)) (hG.comp (show Tendsto (fun i:ℕ=>p+i) atTop atTop from tendsto_atTop_mono (fun i=>Nat.le_add_left ..) tendsto_id)) -- target
     have h(i:ℕ): F p z+ ∑ v∈Finset.range i,D (p+v) z=F (p+i) z:=by
         induction i with|zero=>simp|succ i ih=>rw [Finset.sum_range_succ,← add_assoc,ih]; unfold D; simp only [Nat.add_assoc]; abel
     exact h n
 have hl : AnalyticAt ℝ (fun z:ℝ=> g z) 0:= (show AnalyticAt ℝ g (ofRealCLM 0) from (by simpa using (show AnalyticAt ℝ g 0 from hy'.restrictScalars))).comp ((ofRealCLM).analyticAt _) -- syntax
 apply hl.congr; filter_upwards [ball_mem_nhds (0:ℝ) e] with z h; exact hb z (mem_ball_zero_iff.mp h) -- orientation
lemma golden_arc {d c k:ℝ} (h:0<d)(hk:0<k)(hk':k<1)(v:0<c)(F:ℕ→ℂ→ℂ)(f:ℝ→ℂ)
 (x:∀ᶠ n:ℕ in atTop,DifferentiableOn ℂ (F n) (closedBall 0 d)∧ ∀ z∈ closedBall (0:ℂ) d,‖F n z‖≤ c^n)
 (y:∀ᶠ n:ℕ in atTop,∀ z∈ closedBall (0:ℝ) d, ‖F n z-f z‖≤ k^n) : AnalyticAt ℝ f 0:= growth_analytic (d:=d/2) (half_pos h) hk hk' v F f (by rwa [show 2*(d/2)=d from (by ring)]) (by rwa [show 2*(d/2)=d from (by ring)])
end YM.Caino
#print axioms YM.Caino.golden_arc
