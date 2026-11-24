import YM.SU5.FiniteGaugeData.Largo.Pin
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset
open scoped Topology BigOperators Pointwise
variable {x:ℝ}(o:Rim)(r:ℝ)(i:Tip)(j:ℤ)
lemma faraway(z:ℂ) : τ* |(j:ℝ)| ≤ ‖afar z j‖+‖z‖:= by
 have hx: τ*|(j:ℝ)|=‖((τ*(j:ℝ):ℝ):ℂ)‖:= (by rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos tau_pos]); rw [hx]; nth_rw 1 [show (((τ* (j:ℝ)):ℝ):ℂ)=(afar z j)-z from (by simp [afar])]; exact norm_sub_le ..
private lemma slipG (p:1 ≤ r): Set.Finite {j:ℤ| τ * |(j:ℝ)| ≤ r}:=by
 obtain ⟨n,h⟩:=exists_nat_gt (r/τ); refine (Set.finite_Icc (-(n:ℤ)) (n:ℤ)).subset fun j e=>?_ ; have ht: |(j:ℝ)| ≤ (n:ℝ):= le_trans ((le_div_iff₀ tau_pos).mpr ((mul_comm ..).trans_le e)) h.le; rw [abs_le] at ht; constructor <;> first| exact_mod_cast ht.1|exact_mod_cast ht.2
private lemma far_set_z (C:ℝ): ∀ᶠ j:ℤ in cofinite,∀ z:ℂ, ‖z‖ ≤ C → 1+(snow j:ℝ) ≤ ‖afar z j‖:=by
 have hz:1 ≤ max 1 (2*(C+1)):= le_max_left ..; filter_upwards [(slipG _ hz).eventually_cofinite_notMem] with j p z h; have he:=lt_of_not_ge (show ¬τ * |(j:ℝ)| ≤ max 1 (2*(C+1)) from p); have hr:=faraway j z; have hτ:2 ≤ τ:= by unfold τ; linarith [Real.pi_gt_three]
 change _ ≤ _; rw [show (snow j:ℝ)=|(j:ℝ)| from (by simp [snow])]; nlinarith only [h,hτ,hr,he,le_max_right 1 (2*(C+1)), mul_le_mul_of_nonneg_right hτ (abs_nonneg (j:ℝ))]
lemma anti_phase (z:ℂ): ‖Complex.sin (afar z j/2)‖=‖Complex.sin (z/2)‖:=by
 -- Antiperiodic shift.
 let a:ℂ:= Real.pi; rw [show afar z j/2=z/2+(j:ℂ)*a from ?_, Complex.sin_antiperiodic.add_int_mul_eq]; swap; · unfold afar τ a; push_cast; ring
 simp
lemma far_bound (C:ℝ): ∃ H:ℤ→ℝ,Summable H ∧(∀ j,0≤ H j)∧ ∀ (j:ℤ)(z:ℂ),‖z‖ ≤C → ‖hsinc (afar z j/2) ^ 8‖ ≤ H j:= by
 let r:=max C 1; have hr:0 ≤ r:= le_trans zero_le_one (le_max_right ..); let P(j:ℤ): Prop:=∀ z:ℂ, ‖z‖ ≤ r → 1+(snow j:ℝ) ≤ ‖afar z j‖; let K:= closedBall (0:ℂ) r
 let f(j:ℤ)(z:ℂ):= hsinc (afar z j/2)^8; let g(z:ℂ):= Complex.sin (z/2)
 have he(i:ℤ):∃ z∈ K,∀ w∈K,‖f i w‖≤‖f i z‖:= isCompact_closedBall ..|>.exists_isMaxOn ⟨0,mem_closedBall_self hr⟩ ((show Continuous (fun x=>‖f i x‖) from by unfold f afar; exact (show Differentiable ℂ (f i) from by unfold f afar; fun_prop).continuous.norm).continuousOn)
 choose k km kV using he; let H(i:ℤ):= ‖f i (k i)‖; obtain ⟨z,h0,hg⟩:= (isCompact_closedBall ..).exists_isMaxOn (show K.Nonempty from ⟨0,mem_closedBall_self hr⟩) ((show Continuous (fun z=>‖g z‖) from by unfold g; fun_prop).continuousOn)
 refine ⟨H,?_,fun _=> norm_nonneg _,fun i z h=> kV i z (mem_closedBall.mpr (by rw [dist_zero_right]; exact le_trans h (le_max_left ..)))⟩
 let T:= (2*‖g z‖); apply Summable.of_norm_bounded_eventually (g:=fun i=>T^8*gateL i) (gate_summ.mul_left _); filter_upwards [far_set_z r] with i B
 let a:=(1+(snow i:ℝ)); have ht: a ≤ ‖afar (k i) i‖:= B _ (by simpa only [K, mem_closedBall,dist_zero_right] using km i); have hx: 1≤a:=(by unfold a; simp [snow]); have ha:0<a:=zero_lt_one.trans_le hx; have hz: H i= ‖hsinc (afar (k i) i/2)‖^8:= norm_pow ..
 have hv:‖hsinc (afar (k i) i/2)‖ ≤T/a:=by
    let w:= afar (k i) i; have he: w≠0:= norm_pos_iff.mp (ha.trans_le ht); rw [haway _ (div_ne_zero he (by norm_num)),Complex.norm_div,anti_phase i,show T/a= ‖g z‖/(a/2) from (by unfold T; field_simp),Complex.norm_div,show ‖(2:ℂ)‖=(2:ℝ) from Complex.norm_two]; exact div_le_div₀ (norm_nonneg _) (hg (km i)) (by positivity : 0 < a/2) (by linarith only [ht])
 rw [Real.norm_of_nonneg (show 0≤H _ from norm_nonneg _),hz]; refine (pow_le_pow_left₀ (norm_nonneg _) hv 8).trans ?_; rw [div_pow]; change T^8/a^8 ≤ T^8*(a^2)⁻¹; rw [←div_eq_mul_inv]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); gcongr; norm_num
abbrev Locks := (Tip × ℤ) × Bool
def pinHeight (x:Locks):ℂ:= afar (if x.2 then Complex.I*bush o x.1.1 else -(Complex.I*bush o x.1.1)) (-x.1.2)
def heritage (o:Rim)(x:Locks)(z:ℂ):ℂ:= floam o x.1.1 * hsinc (afar z x.1.2/2)^8
lemma altitude (l:Bool) : |(pinHeight o ((i,j),l)).im|= bush o i ∧ |(pinHeight o ((i,j),l)).re|= τ*|(j:ℝ)|:= by have t:= tau_pos; cases l <;> simp [pinHeight,afar,Complex.mul_re, Complex.mul_im,bush, abs_mul, τ, Real.pi_pos.le]
lemma slippery (p:Slab o) : Bank (pinHeight o) (heritage o):=by
 refine ⟨fun r=>?_, fun r=>?_, fun i=>by unfold heritage afar; fun_prop⟩
 · obtain ⟨n,h⟩:=exists_nat_gt r; let s:= Finset.Icc (fun _ : Tang=> -(n:ℤ)) (fun _=>(n:ℤ)); refine (((s.finite_toSet).prod (slipG (max r 1) (le_max_right ..))).prod (Set.finite_univ (α:=Bool))).subset fun i u=>?_ ; obtain ⟨⟨j,k⟩,l⟩:=i
   let V:= pinHeight o ((j,k),l); have hv:‖V‖≤ r:=u; obtain ⟨u,w⟩:=altitude o j k l; have he:= (abs_im_le_norm V).trans (hv.trans h.le); have ht:τ*|(k:ℝ)| ≤ max r 1:= w ▸ ((abs_re_le_norm V).trans (hv.trans (le_max_left ..)))
   refine ⟨⟨?_, ht⟩, Set.mem_univ _⟩; have hB (a:Tang):(snow (j a):ℝ)≤ (n:ℝ):=by have hx:= (conductor (o a) (j a) (p a).1 (p a).2).trans (bush_ge o j a); change |(pinHeight o ((j,k),l)).im| ≤ _ at he; rw [u] at he; linarith
   exact Finset.mem_Icc.mpr ⟨fun i=>(show -(n:ℤ)≤ j i from (by have : Int.natAbs (j i) ≤ n:= Nat.cast_le.mp (hB i); omega)),fun i=>(show j i≤ (n:ℤ) from (by have : Int.natAbs (j i) ≤ n:= Nat.cast_le.mp (hB i); omega))⟩
 obtain ⟨g,t,z,H⟩:= far_bound r; let Q(i:Tip):ℝ:= 256^3*billC i; have hz(i:Tip):0 < Q i:=mul_pos (by norm_num) (bill_pos _); let W(i:Tip×ℤ):=Q i.1*g i.2
 have he:Summable W:=by
    refine (summable_prod_of_nonneg (f:=W) ?_).mpr ⟨fun i=>t.mul_left (Q i),?_⟩
    · exact fun i=> mul_nonneg (hz _).le (z _)
    simpa only [W, tsum_mul_left] using (bill_summ.mul_left (256^3)).mul_right (∑' i,g i)
 let Y(i:Locks):= W i.1; have hf(i:Locks):0 ≤ Y i:= mul_nonneg (hz _).le (z _)
 refine ⟨Y,hf,(summable_prod_of_nonneg hf).2 ⟨fun k=>(hasSum_fintype _).summable,?_⟩,fun f v p'=>?_⟩
 · simpa only [Y,tsum_fintype,sum_const,card_univ,nsmul_eq_mul] using he.mul_left (Fintype.card Bool:ℝ)
 rw [heritage,Complex.norm_mul,Complex.norm_real]; exact mul_le_mul (floam_le o _ p) (H _ v p') (norm_nonneg _) (hz _).le
end YM.CF.Window.Largo
