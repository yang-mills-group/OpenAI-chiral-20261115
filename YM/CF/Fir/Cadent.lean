import YM.CF.Fir.Dash
import YM.Next.FREE_KERNELS.Warm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma moderateFirm (f:Momentum→ℂ)(h:Moderate (fun _:Unit=>1) (fun _=>f))(hg:∀ p∈realCube zone,f p≠0) : Firm (fun _:Unit=>1) (fun _=>f):=by
  obtain ⟨η,C,hη,hC,H⟩:=h
  let d:=min η zone; have hd:=lt_min hη zone_pos
  let K:= {p:Momentum| physical p ∧ ‖p‖≤Real.pi+d/2}
  have hK:IsCompact K:=by
    have he : K={p:Momentum|star p=p} ∩ closedBall 0 (Real.pi+d/2):=by ext p; simp [K,physical,mem_closedBall]
    rw [he]; exact (isCompact_closedBall ..).inter_left (isClosed_eq continuous_star continuous_id)
  have hh : K⊆ realCube d:=by
    intro p hq; change physical p∧ _ at hq; refine ⟨hq.1, fun i=> ?_⟩; exact (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm p i).trans hq.2) |>.trans_lt (by linarith)
  have hx : ContinuousOn f K:=fun p hp=> ((H ()).hol _ (cube_mono (min_le_left ..) (mem_cube_real (hh hp) hd))).continuousAt.continuousWithinAt
  obtain ⟨a,ha,hb⟩:= hK.exists_isMinOn ⟨0,show physical 0 ∧ ‖(0:Momentum)‖≤ Real.pi+d/2 from ⟨star_zero _,by rw [norm_zero]; have:= Real.pi_pos; positivity⟩⟩ hx.norm
  have he : 0<d/2:= by linarith
  refine ⟨d/2,‖f a‖,he, norm_pos_iff.mpr (hg _ (realCube_mono (min_le_right ..) (hh ha))),fun _ p hm=>?_⟩
  rw [mul_one]; have hi:= Real.pi_pos
  refine hb (show physical p∧_ from ⟨hm.1,?_⟩ : p∈K); rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i; exact (le_of_eq (by rw [show p i=(((p i).re:ℝ):ℂ) from (congr_fun (pq p hm.1) i).symm]; simp) : ‖p i‖≤|(p i).re|).trans (hm.2 i).le
lemma trimP (L:Side): Pay (fun _:Unit=>1) fun _ p=> trident L p := by
  refine ⟨fun _=>zero_le_one,fun ⟨i,a⟩ ⟨k,b⟩=>?_⟩
  -- no odd? can compact pay
  by_cases he:a=b
  · simp only [trident,aliasBlock,Matrix.smul_apply,Matrix.of_apply,he,if_true,smul_eq_mul]
    let f:Momentum→ℂ:=fun p=>mode (aliasAt p k) (lift i)
    have hh:Differentiable ℂ f:=by unfold f mode aliasAt; fun_prop
    obtain ⟨C,hC⟩:= (isCompact_closedBall (0:Momentum) domainRadius).exists_bound_of_continuousOn hh.continuous.continuousOn
    have he: Moderate (fun _:Unit=>1) fun _=>f:=⟨zone,|C|+1,zone_pos,by positivity,fun _=>⟨fun p h=>hh p, fun p h=>by rw [mul_one]; exact (hC _ (cube_inside h)).trans (by grind)⟩⟩
    simpa only [f,one_mul] using (Moderate.const (((L.val:ℂ)^2)⁻¹)).mul he
  simpa only [trident,aliasBlock,Matrix.smul_apply,Matrix.of_apply,if_neg he,smul_zero] using (Moderate.zero (ι:=Unit) (w:=fun _=>1) (fun _=>zero_le_one))
lemma ret_trim (L:Side):Pay (fun _:Unit=>1) fun _ p=> returned (trident L) p:=by
  refine ⟨fun _=>zero_le_one,fun ⟨i,a⟩ ⟨k,b⟩=>?_⟩
  by_cases h:a=b; swap
  · simpa only [returned, Matrix.conjTranspose_apply,trident,aliasBlock,Matrix.of_apply,Matrix.smul_apply,if_neg (Ne.symm h),smul_zero,star_zero] using (Moderate.zero (ι:=Unit) (w:=fun _=>1) (fun _=>zero_le_one))
  simp only [returned,Matrix.conjTranspose_apply,trident,aliasBlock,Matrix.of_apply,Matrix.smul_apply,h,if_true,star_mul, star_inv₀,star_pow,star_natCast,alias_conj,mode_adjoint,smul_eq_mul]
  let f:Momentum→ℂ:=fun p=>mode (aliasAt p i) (-lift k)
  have hh:Differentiable ℂ f:=by unfold f mode aliasAt; fun_prop
  obtain ⟨C,hC⟩:= (isCompact_closedBall (0:Momentum) domainRadius).exists_bound_of_continuousOn hh.continuous.continuousOn
  have he: Moderate (fun _:Unit=>1) fun _=>f:=⟨zone,|C|+1,zone_pos,by positivity,fun _=>⟨fun p h=>hh p, fun p h=>by rw [mul_one]; exact (hC _ (cube_inside h)).trans (by grind)⟩⟩
  simpa only [f,one_mul,mul_comm] using (Moderate.const (((L.val:ℂ)^2)⁻¹)).mul he
lemma repay (j L)(ho:Odd L.val)(l:Site L): Moderate (fun _:Unit=>1) fun _ p=> money j L l p:=by simpa only [money,mul_one] using (Moderate.const _).mul ((muff_pay j (fun _=> L) (fun _=> ho) (fun _=>l)).raise_price (fun _ : Unit=> decay_le_one ..))
lemma repaid (j L)(ho:Odd L.val)(l:Site L)(p:Momentum): star (money j L l (star p))=money j L l p:=by
  have he z : star (plank L (star z))=plank L z:=by rw [plank_bar,star_star,plank_even _ ho]; -- check
  unfold money muff; rw [star_mul,star_pow,star_prod]; simp only [alias_conj,Pi.star_apply,he]; simp [mul_comm]
lemma stack_quote {ι:Type*} (L:Side)(f:ι→Momentum→Site L→Op SpinIdx){w:ι→ℝ}(H:∀ i, Pay w fun a p=> f a p i): Pay w fun a p=>stack L (f a p):=by
  refine ⟨(H 0).site,fun ⟨i,b⟩ ⟨k,c⟩=>?_⟩; by_cases h:i=k
  · simpa only [s_app,h,if_true] using (H k).tap b c
  simpa only [s_app,if_neg h] using Moderate.zero (H 0).site
lemma col_quote {ι:Type*}(L:Side)(f:ι→Momentum→Site L→Op SpinIdx){w:ι→ℝ}(H:∀ i, Pay w fun a p=> f a p i): Pay w fun a p=>col L (f a p):=by
  refine ⟨(H 0).site,fun ⟨i,b⟩ ⟨k,c⟩=>?_⟩; by_cases h:k=0
  · simpa only [c_app,h,if_true] using (H i).tap b c
  simpa only [c_app,if_neg h] using Moderate.zero (H 0).site
lemma sprigPay (j:ℕ)(L:Side)(ho:Odd L.val): Pay (fun _:Unit=>1) fun _ p=> sprig j L p:=by
  apply col_quote L; intro l; simpa only [mul_one] using (Pay.const (1:Op SpinIdx)).scale (repay j L ho l)
lemma sprigR (j:ℕ)(L:Side)(ho:Odd L.val): Pay (fun _:Unit=>1) fun _ p=> returned (sprig j L) p :=by
  refine ⟨fun _=> zero_le_one,fun ⟨i,b⟩ ⟨k,a⟩=>?_⟩
  have hp (p): returned (sprig j L) p (i,b) (k,a) = sprig j L p (k,a) (i,b):=by
    by_cases h:i=0 <;> simp only [sprig,returned,Matrix.conjTranspose_apply,c_app,h] <;> simp only [h,if_false,↓reduceIte,Matrix.smul_apply,star_smul,repaid j L ho,Matrix.one_apply] <;> (try split_ifs) <;> simp
  simp_rw [hp]; exact (sprigPay j L ho).tap _ _
lemma W_quote (j L)(ho:Odd L.val): Pay (fun _:Unit=>1) fun _ p=>stackW j L p :=by
  have hx:= (ret_trim L).times (Pay.const (1-peb L)); simp only [mul_one] at hx; exact (sprigPay j L ho).add hx
lemma W_opp (j L)(ho:Odd L.val): Pay (fun _:Unit=>1) fun _ p=> returned (stackW j L) p:=by
  have h(p): returned (stackW j L) p=returned (sprig j L) p+(1-peb L)*trident L p:=by
    change star (stackW j L (star p))=_; unfold stackW returned; rw [star_star]; change star (sprig j L _+star (trident L p)*(1-peb L))=_; rw [star_add, star_mul, star_sub,star_star,peb_star,star_one]; rfl
  simp_rw [h]; have he := (Pay.const (1-peb L)).times (trimP L); simp only [one_mul] at he; exact (sprigR j L ho).add he
lemma wood_quote (j L)(ho:Odd L.val)(hj:Even j)(u:Bool): Pay (fun _:Unit=>1) fun _ p=> wood u j L p:=by
  have h:= W_quote j L ho
  have hx:= moderateFirm _ h.determinant (fun p hp=> isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (lofty j L hj ho hp)))
  have ht: Pay (fun _:Unit=>1) fun _ p=> (stackW j L p)⁻¹:=by
    simpa only [mul_one,inv_one,Matrix.inv_def,Ring.inverse_eq_inv'] using h.adj.scale (h.determinant.inv hx fun _=>one_pos)
  unfold wood; have ha:= ht.times (Pay.const (slashA u L)); have hb:= (W_opp j _ ho).times (Pay.const (1-sA u L)); simp only [mul_one] at ha hb; exact ha.add hb
end YM.CF.Fir
