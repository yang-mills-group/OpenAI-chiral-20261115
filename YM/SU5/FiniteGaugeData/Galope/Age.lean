import YM.Extra.ITERATION_NO_LOSS.Scales
/-! Numerics for angular audit; alternative to germ stamps
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter Lattice Wilson RG Pressure Extra.Iteration Extra.Iteration.Scales
open scoped Topology BigOperators Classical
namespace Cold
section tiny
variable {p f g:ℝ→ℝ}
lemma timid_le (h:Tiny p g)(u:∀ᶠ x in atTop,0≤ f x∧ f x ≤g x): Tiny p f:=by
 intro ε he; filter_upwards [h ε he,u] with x hx hz; exact ⟨hz.1,hz.2.trans hx.2⟩
lemma timid_congr (h:Tiny p g)(u:g= f): Tiny p f:=by rw [←u]; exact h
end tiny
section
variable {p q c:ℝ}{f g:ℝ→ℝ}
def soft(p:ℝ)(f:ℝ→ℝ):=∃ v:ℝ→ℝ,Tiny id v∧ ∀ᶠ x:ℝ in atTop, 0≤f x ∧ f x ≤ v x / (x^p)
namespace soft
lemma turned (e: soft p f)(h:p=q)(t:f=ᶠ[atTop] g): soft q g:=by
 obtain ⟨v,hv,hx⟩:= e; subst q; exact ⟨v,hv, hx.congr (t.mono (fun x he=> by rw [he]))⟩
lemma curb(e:soft p g)(q:∀ᶠ x:ℝ in atTop, 0≤ f x ∧ f x≤ g x): soft p f:=by
 obtain ⟨v,h,hv⟩:=e; refine ⟨v,h,?_⟩; filter_upwards [hv,q] with x hx tz; exact ⟨tz.1,tz.2.trans hx.2⟩
lemma nonneg(e:soft p f): ∀ᶠ x:ℝ in atTop, 0≤f x:=by obtain ⟨_,_,h⟩:=e; exact h.mono (fun x he=>he.1)
lemma zero(e:Tiny id f): soft 0 f:= ⟨f,e,(e 1 zero_lt_one).mono fun x p=>by simpa only [Real.rpow_zero,div_one,and_true,_root_.le_refl] using p.1⟩ -- tune
lemma const(c:ℝ)(p:0≤c): soft 0 (fun _=> c):= zero (Tiny.const tendsto_id c p)
lemma plus(e:soft p f)(u:soft p g): soft p (fun x=>f x+g x):=by
 obtain ⟨v,h,h'⟩:= e; obtain ⟨w,b,b'⟩:=u; refine ⟨(fun x=>v x+w x),h.add b tendsto_id,?_⟩; filter_upwards [h',b'] with x hx bv; exact ⟨add_nonneg hx.1 bv.1,(add_le_add hx.2 bv.2).trans_eq (add_div ..).symm⟩
lemma times(e:soft p f)(u:soft q g): soft (p+q) (fun x=> f x*g x):=by
 obtain ⟨v,h,h'⟩:=e; obtain ⟨w,b,b'⟩:=u; refine ⟨(fun x=>v x*w x),h.mul b tendsto_id,?_⟩; filter_upwards [h',b',eventually_gt_atTop (0:ℝ)] with x hx bv p; exact ⟨mul_nonneg hx.1 bv.1,(mul_le_mul hx.2 bv.2 bv.1 (hx.1.trans hx.2)).trans_eq (by rw [div_mul_div_comm,Real.rpow_add p])⟩
lemma at_const(e:soft p f)(u:soft 0 g):soft p (fun x=>g x*f x):= by simpa only [zero_add] using u.times e
lemma price (e:soft p f)(c:ℝ)(u:0≤c):soft p (fun x=> c*f x):=e.at_const (const c u)
lemma payC(e:soft p f)(c:ℝ)(u:0≤ c):soft p (fun x=>f x*c):=by simp_rw [mul_comm (f _) c]; exact e.price c u -- tune
lemma classP(e:soft p f)(h:q≤p): soft q f:=by
 obtain ⟨v,hv,hu⟩:=e; refine ⟨v,hv,?_⟩; filter_upwards [hu,(hv 1 zero_lt_one),eventually_ge_atTop (1:ℝ)] with x hx hp hy; have he:0<x:=zero_lt_one.trans_le hy; exact ⟨hx.1,hx.2.trans (div_le_div_of_nonneg_left hp.1 (Real.rpow_pos_of_pos he q) (Real.rpow_le_rpow_of_exponent_le hy h))⟩ -- orientation div tune
lemma bare_rpow(p:ℝ):soft p (fun x:ℝ=> x^(-p)):=by
 refine ⟨(fun _=>1),Tiny.const tendsto_id 1 zero_le_one,?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact ⟨Real.rpow_nonneg hx.le _,le_of_eq (by rw [Real.rpow_neg hx.le,one_div])⟩
lemma identity : soft (-1) id:=by simpa only [neg_neg,Real.rpow_one] using! bare_rpow (-1)
lemma close (e:soft p f)(q:0<p): Tendsto f atTop (𝓝 0):=by
 obtain ⟨v,hv,hu⟩:=e; apply Metric.tendsto_nhds.mpr; intro ε he; have ht:=half_pos q; have hh:=tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop ht)
 filter_upwards [hu,(hv _ ht),hh.eventually (gt_mem_nhds he),eventually_gt_atTop (0:ℝ)] with x hx hb hz hp; rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1]; apply lt_of_le_of_lt (hx.2.trans ?_) (show (x^(p/2))⁻¹ < ε from hz) -- tune
 apply (div_le_iff₀ (Real.rpow_pos_of_pos hp p)).mpr; calc
    _ ≤ x^(p/2):=hb.2
    _ =(x^(p/2))⁻¹ * x^p:=by
       conv_rhs=> rhs; rw [←add_halves p,Real.rpow_add hp]
       have ht:0<x^(p/2):=Real.rpow_pos_of_pos hp _
       field_simp
lemma snows (p:ℝ)(ε:ℝ)(he:0<ε): soft p (fun x:ℝ=> Real.exp (-ε*(radiusB x:ℝ))):=curb (bare_rpow p) ((Scales.first ε p he).mono (fun x e=>⟨(Real.exp_pos _).le,e⟩)) -- tune
lemma θA : soft (1/2) temp:=by
 have hp:Tiny id meter:=by simpa only [Real.rpow_one,add_zero] using Tiny.meter_pow 0 1
 refine ⟨meter,hp,Eventually.of_forall ?_⟩ -- need atTop only
 intro x; unfold temp meter; exact ⟨by positivity,by rw [← Real.sqrt_eq_rpow, inv_mul_eq_div]; rfl⟩
lemma radius : Tiny id (fun x:ℝ=> (radiusB x:ℝ)):= timid_le Tiny.cover_size (Eventually.of_forall fun x=>⟨Nat.cast_nonneg _,le_add_of_nonneg_left zero_le_one⟩)
lemma radiusM : Tiny meter (fun x:ℝ=> (radiusB x:ℝ)):=by refine timid_le (show Tiny meter (fun x:ℝ=>1+(radiusB x:ℝ)) by simpa only [add_zero] using Tiny.cover 0) (Eventually.of_forall (fun x=>⟨Nat.cast_nonneg _,le_add_of_nonneg_left zero_le_one⟩))
end soft
end
end Cold
end YM.SU5.FiniteGaugeData.Galope
