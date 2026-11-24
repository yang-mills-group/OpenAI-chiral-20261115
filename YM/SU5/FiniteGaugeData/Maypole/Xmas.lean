import YM.SU5.FiniteGaugeData.Maypole.Juno
/-! # Diagonal spectrum: time-skew tilt, moment poles -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno
open Function Set MeasureTheory OS OS.Semigroup Complex Filter NormedSpace Metric Bornology Rimbaud
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {X:Type*} [MeasurableSpace X] {A U:X→ℝ} {n i j k:ℕ}{μ:Measure X}[IsFiniteMeasure μ]{r s t e x C:ℝ} {z:ℂ}
-- scalar energies. slope with both directions, measured.P_Eq (OS proof later)
local notation "D₁"=> 𝓝[>] (0:ℝ)
local notation "γ" x:max => Ar (A x) (U x)
local notation "Δ" s:max => sVal A U s
def blow(A U:X→ℝ)(t:ℝ)(n:ℕ)(z:X):= kin t (A z)*‖Ar (A z) (U z)‖^(2*n)
abbrev spinIn(s:ℝ)(A U:X→ℝ)(x:X):= ‖1- sVal A U s x‖ / s
def rich (A U:X→ℝ)(t:ℝ)(s:ℝ)(n:ℕ)(x:X):= (kin t (A x))*power A U s n x
omit [MeasurableSpace X] in
lemma rich_p(A U:X→ℝ)(t s:ℝ)(x:X):0≤ rich A U t s n x:=by unfold rich power kin; positivity
omit [MeasurableSpace X] in
lemma onStep(A U:X→ℝ)(t s:ℝ)(x:X)(n:ℕ) : rich A U t s n x / s^(2*n)= (kin t (A x))*spinIn s A U x^(2*n):=by unfold rich power spinIn; rw [div_pow,mul_div_assoc]
private lemma spinD(A U:ℝ)(t:ℝ): HasDerivAt (fun k:ℝ=>shape k A U) (shape t A U* Ar A U) t:=by
 simpa only [shape, ofReal_one,one_mul,id_eq] using! (((hasDerivAt_id' t).ofReal_comp).mul_const (Ar A U)).cexp
omit [MeasurableSpace X] in
private lemma spin_lim(x:X) : Tendsto (fun s=>spinIn s A U x) D₁ (𝓝 ‖γ x‖):=by
 let f(s:ℝ):=(Δ s) x; let z:= γ x; have hp:f 0=1:=by simp [f,sVal,shape]
 have he:HasDerivAt f z 0:=by
    let h:= spinD (A x) (U x) 0; simpa only [f,z,hp,sVal,show shape ↑(0:ℝ) (A x) (U x)=1 from hp,one_mul] using h
 refine Tendsto.congr' ?_ (he.tendsto_slope.mono_left (nhdsGT_le_nhdsNE _)|>.norm); filter_upwards [self_mem_nhdsWithin] with s w; have hs:s>0:=w; change ‖slope f 0 s‖=_; simp_rw [slope,hp,spinIn,norm_smul,Real.norm_eq_abs]; simp only [vsub_eq_sub,sub_zero, abs_inv, abs_of_pos hs, norm_sub_rev (1:ℂ) _, f]; rw [div_eq_inv_mul] -- tune
omit [MeasurableSpace X] in
private lemma den_norm(s:ℝ)(x:X)(p:0≤ s)(t:0≤ A x): ‖sVal A U s x‖≤1:=by
 unfold sVal shape; rw [norm_exp]; apply Real.exp_le_one_iff.mpr; simp [Ar]; positivity -- may simp; prove
omit [MeasurableSpace X] in
private lemma spin_norm(x:X)(p:0≤ A x)(h:0<s): spinIn s A U x ≤ ‖γ x‖:= by
 let f(s:ℝ):=(Δ s) x; let z:= γ x; have hz(r:ℝ): HasDerivAt f (f r*z) r:= spinD _ _ r; have he:f 0=1:=by simp [f,sVal,shape]
 let S':= Icc (0:ℝ) s
 have ht: ‖f s-f 0‖ ≤ ‖z‖* ‖s-0‖:= Convex.norm_image_sub_le_of_norm_deriv_le (fun i (_:i∈ S')=>(hz i).differentiableAt) (fun i g=>by rw [(hz i).deriv,norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (den_norm i x g.1 p)) (convex_Icc 0 s) (left_mem_Icc.mpr h.le) (right_mem_Icc.mpr h.le) -- def S TC
 unfold spinIn; apply (_root_.div_le_iff₀ h).mpr; rw [he,sub_zero,Real.norm_of_nonneg h.le,norm_sub_rev] at ht; exact ht
omit [MeasurableSpace X] in
private lemma spin_up(x:X)(h:0≤ s): 0 ≤ spinIn s A U x:= by unfold spinIn; positivity
variable (P:Payer μ A U)(T:Chunk t C μ A U)
include P
private lemma rich_m (s:ℝ)(k:ℕ): Measurable (rich A U t s k):=by have he:= P.a_m; have hv:= P.u_m; unfold rich kin power shape Ar; fun_prop
private lemma blow_m (s:ℝ)(n:ℕ): Measurable (blow A U s n):=by have he:= P.a_m; have hv:= P.u_m; unfold blow kin Ar; fun_prop
-- DCT price low.N
private lemma loom (h:Integrable (blow A U t n) μ): Tendsto (fun s:ℝ=> ∫ x, rich A U t s (n+1) x / s^(2*n) ∂μ) D₁ (𝓝 0) :=by
 let f(s:ℝ)(x:X):=rich A U t s (n+1) x / s^(2*n); let g:=blow A U t n; let u(x:X)(s:ℝ):= ‖1-sVal A U s x‖; let r(x:X):=kin t (A x); have hv(s:ℝ)(x:X): f s x=r x* (spinIn s A U x)^(2*n)* (u x s)^2:=by
    rw [show f s x= rich A U t s n x/ s^(2*n)* (u x s)^2 from (by unfold f u rich power sVal; rw [Nat.mul_add,Nat.mul_one,pow_add]; ring), onStep]
 have hx(x:X):Tendsto (u x) D₁ (𝓝 0):=by
    let i:ℝ→ℂ:= fun s=>sVal A U s x; let H:= spinD (A x) (U x) 0; have hx:i 0=1:=by simp [i,shape,sVal]
    simpa only [u,i,sVal,show (1:ℂ)-shape ↑(0:ℝ) (A x) (U x) =0 from hx ▸ sub_self _,norm_zero] using (((H.continuousAt.tendsto.const_sub 1).norm).mono_left nhdsWithin_le_nhds)
 let S(x):=g x*4; have hs:Integrable S μ:=h.mul_const 4; have hl:∀ x:X,Tendsto (fun s=> f s x) D₁ (𝓝 0) :=by intro x; simp_rw [hv]; let u:=hx x; simpa only [zero_pow (by decide: 2≠0),mul_zero] using (((spin_lim (A:=A) (U:=U) x).pow (2*n)).const_mul (r x) |>.mul (u.pow 2)) -- tune implicit A T
 have hp:∀ᶠ s in D₁,∀ᵐ x∂μ, ‖f s x‖≤ S x:=by
    filter_upwards [self_mem_nhdsWithin] with s hs; filter_upwards [P.air] with x hh; have ht:0<s:=hs; rw [Real.norm_of_nonneg (show 0≤ f s x from div_nonneg (rich_p ..) (by positivity)),hv]; unfold S g blow
    refine mul_le_mul ?_ ?_ (by positivity) (by unfold kin; positivity); · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (spin_up x ht.le) (spin_norm x hh ht) _) (Real.exp_pos _).le
    have h1:u x s≤2:= (norm_sub_le ..).trans ((add_le_add norm_one.le (den_norm s x ht.le hh)).trans_eq (by norm_num)); exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans_eq (by norm_num) -- tune
 have he:=tendsto_integral_filter_of_dominated_convergence S (Eventually.of_forall fun s=>((rich_m (t:=t) P s (n+1)).div_const _).aestronglyMeasurable) hp hs (Eventually.of_forall hl); simpa only [integral_zero,f] using he
include T
private lemma cap_zero : 0≤ C:=by obtain ⟨f,u,v,p⟩:=T.memo 0 (by simp); exact (norm_nonneg (f 0)).trans (v 0 (mem_closedBall_self (by exact (by have hx:=T.live; positivity:0≤ t/8)))) -- positivity from T
omit P T in
lemma blow_nn (x:X): 0≤ blow A U t n x:=by unfold blow kin; positivity
private lemma countO (p:Integrable (blow A U t n) μ){f:ℂ→ℂ}(h:Warp μ (fun s x=> (rich A U t s (n+1) x:ℂ)) (burn t (n+1)) (C*4^(n+1)) f)(x:ℂ)(e:‖x‖≤ burn t (n+1)): ‖f x‖≤ C*4^(n+1)*(‖x‖/(burn t (n+1)))^(2*(n+1)):=by
 let B:= burn t (n+1); let D:= 𝓝 (0:ℝ); have ht:0<B:=bore T; have hv:∀ᶠ x:ℝ in 𝓝 0, f (x:ℂ)=(↑(∫ p,rich A U t x (n+1) p ∂μ):ℂ):=by
    filter_upwards [closedBall_mem_nhds (0:ℝ) ht] with x k; have he:= Metric.mem_closedBall.mp k; rw [dist_zero_right] at he; rw [(h.deed x he).2, integral_complex_ofReal]
 have he:∀ᶠ z:ℝ in D,0≤ f (z:ℂ):=hv.mono fun x e=> by rw [e]; exact_mod_cast (integral_nonneg (μ:=μ) (show ∀ z:X,0≤rich A U t x (n+1) z from fun z=>rich_p ..))
 have hF:↑(2*n+2:ℕ)≤ analyticOrderAt f 0:=by
    apply upward (h.hol _ (mem_closedBall_self ht.le)) he
    apply Tendsto.congr' ?_ (continuous_ofReal.continuousAt.tendsto.comp (loom P p)); filter_upwards [hv.filter_mono nhdsWithin_le_nhds] with s v; unfold Function.comp; dsimp only; rw [v, ← Complex.ofReal_pow, integral_div,Complex.ofReal_div]
 exact dimm ht h.hol (fun z v=>h.price z (mem_closedBall_zero_iff.mp v)) (show ↑(2*(n+1):ℕ) ≤ analyticOrderAt f 0 from (show 2*(n+1) = 2*n+2 from (by omega)) ▸ hF) x (mem_closedBall_zero_iff.mpr e) -- cast orientation
abbrev billow (t C:ℝ)(n:ℕ):= C*4^n*(burn t n)⁻¹^(2*n)
private lemma hires (p:Integrable (blow A U t n) μ){f:ℂ→ℂ}(h:Warp μ (fun s x=> (rich A U t s (n+1) x:ℂ)) (burn t (n+1)) (C*4^(n+1)) f)(x:ℝ)(u:0<x) (k:x≤ burn t (n+1)):
   let V(p:X):= rich A U t x (n+1) p / x^(2*(n+1)); (∫⁻ i, ‖V i‖ₑ ∂μ) ≤ ENNReal.ofReal (billow t C (n+1)):=by
 intro V; obtain ⟨q,hp⟩:=h.deed x (abs_of_pos u |>.trans_le k); let N:=n+1; have hg:Integrable (rich A U t x (n+1)) μ:=by let he:=q.re; exact he
 have he:=countO P T p h (x:ℂ) (by rw [Complex.norm_real]; exact (Real.norm_of_nonneg u.le).trans_le k); rw [hp,integral_complex_ofReal, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg u.le] at he; let B:= burn t (n+1); have hB:= (bore T (n:=n+1)); rw [←ofReal_integral_norm_eq_lintegral_enorm (show Integrable V μ from hg.div_const _), show (fun i=> ‖V i‖)=V from funext fun i=> Real.norm_of_nonneg (show 0≤ V i from div_nonneg (rich_p ..) (by positivity)), integral_div]; apply ENNReal.ofReal_le_ofReal; apply (_root_.div_le_iff₀ (pow_pos u _)).mpr; apply le_trans ((le_abs_self _).trans he); unfold billow; exact le_of_eq (by rw [div_pow,inv_pow]; ring) -- tune expand V integral_div
private lemma fatou (p:Integrable (blow A U t n) μ) : Integrable (blow A U t (n+1)) μ ∧ (∫ x,blow A U t (n+1) x ∂μ) ≤ billow t C (n+1):=by
 obtain ⟨f,h⟩:= (bloomG P T (n+1)); let D:= burn t (n+1); let g:= blow A U t (n+1); let N:=2*(n+1); let K(s:ℝ)(x:X):= rich A U t s (n+1) x / s^N; let J:= billow t C (n+1); have hJ:0≤J:=by unfold J billow; have he:=bore T (n:=n+1); have hp:=cap_zero P T; positivity
 have hp(x:X): Tendsto (fun s=> ‖K s x‖ₑ) D₁ (𝓝 (‖g x‖ₑ)):=by unfold g K N; simp_rw [onStep]; exact (((spin_lim (U:=U) x).pow _).const_mul (kin t (A x))).enorm
 have hu : ∀ᶠ k in D₁, (∫⁻ x, ‖K k x‖ₑ ∂μ) ≤ ENNReal.ofReal J :=by
    filter_upwards [self_mem_nhdsWithin,(nhdsWithin_le_nhds (α:=ℝ) (s:=Set.Ioi 0)) (ge_mem_nhds (bore T (n:=n+1)))] with s hs ht; exact hires P T p (show Warp _ _ _ _ _ from h) s hs ht -- type inference expensive
 have he:(∫⁻ x, ‖g x‖ₑ ∂ μ) ≤ ENNReal.ofReal J:= calc
    _ = (∫⁻ x, liminf (fun s=> ‖K s x‖ₑ) D₁ ∂ μ):=lintegral_congr (fun x=>(hp x).liminf_eq.symm)
    _ ≤ liminf (fun s=>∫⁻ x,‖K s x‖ₑ ∂ μ) D₁:=by apply lintegral_liminf_le; intro k; exact ((rich_m (t:=t) P k (n+1)).div_const (k^N)).enorm
    _ ≤ _ := liminf_le_of_frequently_le' hu.frequently
 have hv:Integrable g μ:=⟨(blow_m P t (n+1)).aestronglyMeasurable, lt_of_le_of_lt he ENNReal.ofReal_lt_top⟩; refine ⟨hv,?_⟩; rw [←ofReal_integral_norm_eq_lintegral_enorm hv, show (fun x=>‖g x‖)=g from funext fun x=> Real.norm_of_nonneg (blow_nn x)] at he; exact (ENNReal.ofReal_le_ofReal_iff hJ).mp he
lemma Momentum (n:ℕ): Integrable (blow A U t n) μ ∧ (∫ x, blow A U t n x ∂μ) ≤ billow t C n:=by
 induction n with
 | succ n ih=> exact fatou P T ih.1
 | zero=>
    obtain ⟨f,h⟩:= bloomG P T 0; let B:=burn t 0; have hv:0<B:=bore T; let W(x:X):=kin t (A x); have he:blow A U t 0=W:=funext fun x=>by simp only [W,blow,Nat.mul_zero,pow_zero,mul_one]
    rw [he]; obtain ⟨q,X⟩:= h.deed 0 (abs_zero.trans_le hv.le); simp_rw [power,Nat.mul_zero,pow_zero,mul_one,ofReal_zero] at q X; rw [integral_complex_ofReal] at X; refine ⟨?_,?_⟩; · exact q.re
    let hx:= h.price 0 ((norm_zero (E:=ℂ)).trans_le hv.le); rw [X,pow_zero,mul_one,Complex.norm_real,Real.norm_eq_abs] at hx; simp only [billow,Nat.mul_zero,pow_zero,mul_one]; exact (le_abs_self _).trans hx
#print axioms Momentum
end YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno
