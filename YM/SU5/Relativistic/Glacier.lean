import YM.SU5.Relativistic.MilkPot
/-! # free row near radial seam. Smooth stencils and peers. No regulator election here. -/
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free Asymptotics
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
private lemma stop (x:Bin) : ‖x‖^2 ≤ radius x :=by
 have ht: 0≤radius x:=by unfold radius; positivity
 have he: ‖x‖ ≤ Real.sqrt (radius x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr; intro i; apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp; rw [Real.sq_sqrt ht,Real.norm_eq_abs,sq_abs]; exact Finset.single_le_sum (fun i _=>sq_nonneg (x i)) (Finset.mem_univ _)
 exact (pow_le_pow_left₀ (norm_nonneg _) he _).trans_eq (Real.sq_sqrt ht)
private lemma ride : ContDiff ℝ ω radius:=by unfold radius; fun_prop
private def upright : Bin →L[ℝ] ℝ:= ContinuousLinearMap.proj TA
private def paean (d k:ℕ):Bin→ℝ := (⇑upright)^d * ((radius)^k)⁻¹
private lemma eval_u {x:Bin}(d k): paean d k x = (x TA)^d / (radius x)^k:= by simp only [paean,Pi.mul_apply,Pi.pow_apply,Pi.inv_apply,div_eq_mul_inv]; rfl
private lemma via_w {d k:ℕ}(p:0<d):paean d k 0=0:=by simp [eval_u,p.ne']
private lemma in_night (d k:ℕ) (x:Bin)(p:x≠0): DifferentiableAt ℝ (paean d k) x:=by unfold paean; exact ((upright.differentiableAt).pow d).mul (((ride.differentiable (by simp) x).pow k).inv (show _ ≠ 0 from (pow_pos (radius_pos x p) k).ne'))
private lemma tender (d k:ℕ)(p:2*k+2≤d) (x:Bin)(h:‖x‖ ≤ 1): ‖paean d k x‖≤‖x‖^2:=by
 by_cases v:x=0; · subst x; rw [via_w (by omega)]; simp
 rw [eval_u, norm_div,Real.norm_eq_abs, abs_pow,Real.norm_of_nonneg (pow_pos (radius_pos x v) k).le]; apply (div_le_iff₀ (by apply pow_pos (radius_pos x v))).mpr
 apply (pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm x TA) d).trans
 apply (pow_le_pow_of_le_one (norm_nonneg _) h p).trans
 rw [pow_add,pow_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) (stop x) _) (by positivity)
private lemma farewell {d k:ℕ}(p:2*k+2≤d): HasFDerivAt (paean d k) (0:Bin→L[ℝ] ℝ) 0 :=by
 rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]; intro c h; filter_upwards [mem_nhds_iff.mpr ⟨ball 0 (min c 1),Subset.rfl,isOpen_ball, Metric.mem_ball_self (lt_min h zero_lt_one)⟩] with x g
 have hv: ‖x‖ < min c 1:=by simpa using mem_ball.mp g
 simp only [zero_add, ContinuousLinearMap.zero_apply, sub_zero,via_w (d:=d) (k:=k) (by omega)]
 exact le_trans (tender d k p x (le_trans hv.le (min_le_right ..))) (by rw [sq]; exact mul_le_mul_of_nonneg_right (hv.le.trans (min_le_left ..)) (norm_nonneg _))

lemma sloane {d k n:ℕ}(hk:0<k)(p:2*(k+n)+2≤d) : ContDiff ℝ (↑n) (paean d k):=by
 have h:Differentiable ℝ (paean d k):= fun x=> by
    by_cases u:x=0; · subst x; exact (farewell (by omega)).differentiableAt
    exact in_night d k x u

 induction n generalizing d k with
 | zero => exact contDiff_zero.mpr h.continuous
 | succ n ih=>
    let u:= upright; let S:= fderiv ℝ radius; let R:=fun x=> ((d:ℝ)*paean (d-1) k x) • u - ((k:ℝ)*paean d (k+1) x) • S x -- precedence parenth
    have hx:fderiv ℝ (paean d k)=R:=by
       funext x; by_cases v:x=0
       · subst x; rw [(farewell (by omega)).fderiv]; unfold R; simp [via_w (d:=d-1) (by omega),via_w (d:=d) (by omega)]
       have he:= radius_pos x v; let g:Bin→ℝ:= fun x=> radius x ^ k; have hy:g x≠0:= (pow_pos he _).ne'
       have hf:= (ride.differentiable (by simp) x).hasFDerivAt; have hp' := ((u.hasFDerivAt).pow d).mul (((hasDerivAt_inv hy).hasFDerivAt).comp x (hf.pow k)); change fderiv ℝ ((fun x => u x ^ d) * ((fun y:ℝ => y⁻¹) ∘ g)) x = _; rw [hp'.fderiv] -- tune
       have hd(x:ℝ):x^(d-1)*x=x^d := by rw [←pow_succ, Nat.sub_add_cancel (by omega)]
       have hrad: radius x ^ (k-1) *radius x=radius x^k:=by rw [←pow_succ,Nat.sub_add_cancel (by omega)]
       ext q; unfold R paean; simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, Pi.pow_apply, Pi.mul_apply,Function.comp_apply,Pi.inv_apply,smul_eq_mul] -- tune
       simp only [nsmul_eq_mul]; unfold u S g; rw [pow_succ (radius x), ←hrad]; field_simp <;> ring
    rw [Nat.cast_add_one, contDiff_succ_iff_fderiv]; refine ⟨h,fun g=>by simp at g,?_⟩
    have he:ContDiff ℝ (↑n) (paean d (k+1)):= ih (by omega) (by omega) (fun x=>hStub _ _ (by omega) x); have hp':ContDiff ℝ (↑n) (paean (d-1) k):= ih hk (by omega) (fun x=> hStub _ _ (by omega) x)
    rw [hx]; unfold R; exact ((contDiff_const.mul hp').smul contDiff_const).sub ((contDiff_const.mul he).smul (ride.fderiv_right le_top))
where hStub (d k:ℕ)(p:2*k+2≤d)(x:Bin) : DifferentiableAt ℝ (paean d k) x:= by
        by_cases v:x=0; · subst x; exact (farewell p).differentiableAt
        exact in_night d k x v

abbrev Pasture:= ball (0:Bin) (3*Real.pi/2)
lemma convene (x:Bin)(i:Axis)(p:x∈Pasture): tough x i = slat x 0 i + feast i x :=by
 let S:Set Cover:= {0}; have h:Summable (fun l: {l:Cover//l∈ Sᶜ}=> slat x l i):=snack i x (ball_subset_closedBall p) -- implicit S compl definally?
 let f:= fun l:Cover=> slat x l i; have hv:HasSum (f ∘ ((↑):S→Cover)) (f 0):=by have hz:= Set.mem_singleton_iff.mp (default : ↑({0}:Set Cover)).property; unfold S; simpa only [Fintype.sum_unique,comp_apply,hz] using (hasSum_fintype (f ∘ ((↑):({0}:Set Cover)→Cover)))
 exact (hv.add_compl (show HasSum (f ∘ ((↑):↑(Sᶜ)→Cover)) (feast i x) from h.hasSum)).tsum_eq

lemma graze (x:Bin)(z:Cover): tough (x+stem z)= tough x:=by
 funext i; unfold tough; let W:=Equiv.addLeft z; rw [←W.tsum_eq (fun l=>slat x l i)]; apply tsum_congr; intro j; unfold slat; rw [show W j=z+j from rfl, ←show x+stem z+stem j=x+stem (z+j) from (by rw [stem_a,add_assoc])] -- lhs choose reindex orientation rw picks lhs

def sparrow (d:ℕ)(x:Bin):ℂ:= (↑(Real.sin (x TA / 2)):ℂ)^(2*d)
private lemma spry (x:ℝ): Real.sin (x/2)= Real.sinc (x/2)*(x/2):=by
 by_cases h:x=0; · subst x; simp
 rw [Real.sinc_of_ne_zero (div_ne_zero h two_ne_zero), div_mul_cancel₀ _ (div_ne_zero h two_ne_zero)]
lemma sieved (d:ℕ)(x:Bin)(z:Cover): sparrow d (x+stem z)= sparrow d x:=by
 have he: |(-1:ℝ)^(z TA)|=1:=by rw [abs_zpow]; simp
 unfold sparrow; simp only [Pi.add_apply,stem]; rw [show (x TA+_)/2=x TA/2+(z TA:ℝ)*Real.pi by ring, Real.sin_add_int_mul_pi, Complex.ofReal_mul,mul_pow]; rw [←Complex.ofReal_pow, ←(Even.pow_abs (by exact even_two_mul d) _),he]; simp
lemma sats (d:ℕ) : ContDiff ℝ ω (sparrow d):=by apply contDiff_iff_contDiffAt.mpr; intro x; unfold sparrow; fun_prop
lemma hall (d n:ℕ)(i:Axis)(p:2*(1+n)+2≤2*d) : ContDiffOn ℝ (↑n) (fun x=>sparrow d x*tough x i) Pasture:=by
 let b(x:Bin):= (x TA); let g:= fun x:Bin=> (weave x)^8 *(2*(x i:ℂ))*((2⁻¹:ℂ)*skirt (b x))^(2*d)
 have he(x:Bin):sparrow d x*slat x 0 i = (paean (2*d) 1 x:ℂ)*g x:=by unfold g slat sparrow b; rw [spry, eval_u,stem_0,add_zero]; unfold weave skirt; push_cast; ring -- includes denominator zeros; tune
 apply ContDiffOn.congr (f:=fun x=> (paean (2*d) 1 x:ℂ)*g x+ sparrow d x*feast i x) (ContDiffOn.add (((Complex.ofRealCLM.contDiff.comp (sloane zero_lt_one p)).mul _).contDiffOn) (((sats d).of_le le_top).contDiffOn.mul (buffet i n))) (fun x v=> ?_)
 · unfold g; have ht:ContDiff ℝ (↑n) weave:= contDiff_prod (fun _ _=>(evenSkirt.comp (by fun_prop)).of_le le_top); have hK:ContDiff ℝ (↑n) (fun x:Bin=> (x i:ℂ)):= Complex.ofRealCLM.contDiff.comp (by fun_prop)
   exact ((ht.pow _).mul (contDiff_const.mul hK)).mul ((contDiff_const.mul ((evenSkirt.of_le le_top).comp (by unfold b; fun_prop))).pow _) -- tune
 · rw [convene _ _ v,mul_add,he]
lemma shelter (x: Bin):∃ z:Cover,x+stem z∈ Pasture:=by
 choose k hk using fun i=>fragment Real.pi pi_pos (x i); refine ⟨-k,?_⟩; apply mem_ball.mpr; rw [dist_zero_right]; apply lt_of_le_of_lt _ (show π<3*Real.pi/2 by linarith [pi_pos]); apply (pi_norm_le_iff_of_nonneg pi_pos.le).mpr; intro i; simpa [stem,sub_eq_add_neg] using hk i
lemma parade (d n:ℕ)(i:Axis)(p:2*(1+n)+2≤2*d): ContDiff ℝ (↑n) (fun x=> sparrow d x*tough x i):=by
 apply contDiff_iff_contDiffAt.mpr; intro x; obtain ⟨z,h⟩:=shelter x
 have he:= ((hall d n i p).contDiffAt (isOpen_ball.mem_nhds h)).comp x (show ContDiffAt ℝ (↑n) (fun y=>y+stem z) x by fun_prop)
 simpa only [Function.comp_def,graze,sieved] using he
end YM.CF.Crest.Sleet.Sorcerer

#print axioms YM.CF.Crest.Sleet.Sorcerer.parade
