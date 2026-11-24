import YM.CF.Fief.Bank
/-! Power asymptotics, arguments large X, helpers. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Sleigh
open Function Filter Lattice Asymptotics RG
open Pressure
open scoped Topology
variable {a b t:ℝ} {F G H:ℝ→ℝ}
def Paddled (a:ℝ) (F:ℝ→ℝ): Prop:= ∃ C > (0:ℝ), ∀ᶠ x in atTop, |F x| ≤ C*x^a
namespace Paddled
lemma caps (p:Paddled a F) (t:∀ᶠ x in atTop, |G x| ≤ |F x|) : Paddled a G:=by obtain ⟨C,c,g⟩:=p; exact ⟨C,c,(g.and t).mono fun _ w=> w.2.trans w.1⟩
lemma agree (p:Paddled a F)(t:F=ᶠ[atTop] G):Paddled a G:=p.caps (t.mono fun _ h=> (congrArg abs h).ge)
lemma agrees (p:Paddled a F)(x:a=b):Paddled b F:= x ▸ p
lemma park (a:ℝ):Paddled a (fun x:ℝ=>x^a):=⟨1,one_pos,(eventually_gt_atTop (0:ℝ)).mono fun x h=> by rw [one_mul,abs_of_pos (by positivity : 0<x^a)]⟩
lemma lake (C:ℝ):Paddled 0 (fun _=> C):=⟨|C|+1,by positivity,Eventually.of_forall fun x=>by rw [Real.rpow_zero,mul_one]; linarith⟩
lemma add (p:Paddled a F)(q:Paddled a G):Paddled a (fun x=> F x+G x):=by obtain ⟨C,c,hc⟩:=p; obtain ⟨D,d,hd⟩:=q; refine ⟨C+D,add_pos c d,?_⟩; filter_upwards [hc,hd] with x h k; rw [add_mul]; exact (abs_add_le _ _).trans (add_le_add h k)
lemma mul(p:Paddled a F)(q:Paddled b G):Paddled (a+b) (fun x=>F x*G x):=by obtain ⟨C,c,hc⟩:=p; obtain ⟨D,d,hd⟩:=q; refine ⟨C*D,mul_pos c d,?_⟩; filter_upwards [hc,hd,eventually_gt_atTop (0:ℝ)] with x H K e; rw [abs_mul,Real.rpow_add e]; exact (mul_le_mul H K (abs_nonneg _) (by positivity)).trans_eq (by ring)
lemma scale (p:Paddled a F)(C:ℝ):Paddled a (fun x=> C*F x):= ((lake C).mul p).agrees (zero_add _)
lemma up (p:Paddled a F) (t:a≤b):Paddled b F := by obtain ⟨C,c,hc⟩:=p; exact ⟨C,c,(hc.and (eventually_ge_atTop (1:ℝ))).mono fun x h=>h.1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h.2 t) c.le)⟩
lemma power(p:Paddled a F) (n:ℕ): Paddled (a*n) (fun x:ℝ=>F x^n):=by induction n with | zero=>simp only [Nat.cast_zero,mul_zero,pow_zero]; exact lake _| succ n H=> simp_rw [pow_succ]; apply (H.mul p).agrees; push_cast; ring
lemma discounts (p:Paddled a F) (t:a<b) {z:ℝ} (e:0<z):∀ᶠ x in atTop, |F x| ≤ z*x^b:=by
 obtain ⟨C,c,hc⟩:=p
 filter_upwards [hc, (tendsto_rpow_atTop (sub_pos.mpr t)).eventually_ge_atTop (C/z),eventually_gt_atTop (0:ℝ)] with x h k e₀
 have hu: C≤ z*x^(b-a):=by rw [mul_comm]; exact (div_le_iff₀ e).1 k
 apply h.trans; calc
 C*x^a ≤ (z*x^(b-a))*x^a:= mul_le_mul_of_nonneg_right hu (by positivity)
 _ = _:=by rw [mul_assoc,← Real.rpow_add e₀,sub_add_cancel]
lemma pure (p:Paddled a F)(h:a<b):∀ᶠ x in atTop, F x ≤ x^b:= (p.discounts h one_pos).mono (fun i h=> (le_abs_self _).trans (h.trans (by rw [one_mul])))
lemma lim (p:Paddled a F)(t:a<0): Tendsto F atTop (𝓝 0):=by
 apply Metric.tendsto_nhds.mpr; intro ε e; filter_upwards [p.discounts t (half_pos e)] with x h; rw [Real.rpow_zero,mul_one] at h; rw [dist_zero_right,Real.norm_eq_abs]; exact h.trans_lt (half_lt_self e)
lemma lim_prod (p:Paddled a F)(t:a<b): Tendsto (fun x:ℝ=>x^(-b)*F x) atTop (𝓝 0):= ((park _).mul p).lim (by linarith)
lemma wiggle (p:Tendsto F atTop (𝓝 t)):Paddled 0 F:=⟨ |t|+1,by positivity, (p.abs.eventually (ge_mem_nhds (show |t|< |t|+1 by linarith))).mono fun x h=> by simpa using h⟩
lemma addWeather (p:ℝ):Paddled 1 (fun x:ℝ=>x+p):=(((park 1).agree (Eventually.of_forall fun x=> Real.rpow_one x)).add ((lake p).up zero_le_one))
lemma singers (p:∀ᶠ x in atTop, |F x| ≤ x^a):Paddled a F:=⟨1,one_pos,(p.mono fun x h=> by simpa only [one_mul] using h)⟩
lemma tempay (p:0<a):Paddled (-(1/2:ℝ)+a) temp:=by apply singers; filter_upwards [Work.E09.temp_cost a p,eventually_gt_atTop (0:ℝ)] with x h k; rw [abs_of_nonneg (Work.E09.temp_pos k).le]; exact h
lemma radpay (p:0<a)(n:ℕ):Paddled a (fun x:ℝ=>(radiusB x:ℝ)^n):=by apply singers; filter_upwards [(Work.E09.radiusB_small _ p n).bound one_pos,eventually_gt_atTop (0:ℝ)] with x h k; rwa [one_mul,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity:0≤ x^a)] at h
end Paddled
open SectorNext.Remainder.Scales
variable (L:Side)(J:Gauge)
lemma fitYear : ∀ᶠ x:ℝ in atTop,x/2 ≤ y J L x∧ y J L x≤2*x:=by filter_upwards [eventually_ge_atTop (-2*(J.slopeConstant*Real.log (L.val:ℝ))),eventually_ge_atTop (J.slopeConstant*Real.log L.val)] with x h g; unfold y betaF; constructor <;> linarith
lemma pstar (u:0<a)(n:ℕ): Paddled a (fun x=>p J L x^n):=by
 have hz:=year J L

 refine ⟨(2:ℝ)^a,by positivity,?_⟩
 filter_upwards [hz.eventually (Vac.Numbers.cost (n:ℝ) a u), fitYear L J,hz.eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with x h k hY he
 have hp:0 < p J L x:= pos J L x
 rw [abs_of_nonneg (pow_nonneg hp.le _)]
 rw [Real.rpow_natCast] at h
 unfold p; rw [Next.Scheduling.Clock.watch_two]; refine (show Vac.Numbers.P _ ^ n ≤ _ from h).trans ?_
 exact (Real.rpow_le_rpow hY.le k.2 u.le).trans_eq (Real.mul_rpow (by norm_num) he.le)
lemma gpaddled:Paddled (-(1/2:ℝ)) (g J L):= by
 refine ⟨Real.sqrt (2:ℝ), by positivity,?_ ⟩
 filter_upwards [fitYear L J,(year J L).eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with x h k v
 have hx:= yg2 J L k; have he:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2); have ht:=gauge J L k
 rw [abs_of_pos ht,Real.rpow_neg v.le, ← Real.sqrt_eq_rpow]
 refine (sq_le_sq₀ ht.le (by positivity)).mp ?_; rw [mul_pow,inv_pow,he,Real.sq_sqrt v.le, ← div_eq_mul_inv,le_div_iff₀ v]; nlinarith only [hx,mul_le_mul_of_nonneg_right h.1 (sq_nonneg (g J L x))]
lemma skca (n:ℕ)(h: CF.Fief.sizeK L n F)(p:0<a): Paddled ((-(1/2:ℝ))*(n:ℝ)+a) F:=by
 obtain ⟨N,H⟩:=h; exact (((gpaddled L CF.SU.group).power n).mul (pstar L CF.SU.group p N)).caps (H.mono fun _ t=>t.trans (le_abs_self _))
end YM.Sleigh
