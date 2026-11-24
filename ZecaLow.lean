import YM.SU5.FiniteGaugeData.Seld.Wadding
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

def low (t:ℝ≥0) := R - R * S.E t

lemma tail (x:H)(t:ℝ≥0):
   ∫ v in Set.Ioi (t:ℝ), cups S x v
    = Real.exp (-t) • R (S.E t x):=by
 have p := (measurePreserving_add_right volume (t:ℝ)).setIntegral_preimage_emb
      (Homeomorph.addRight (t:ℝ)).measurableEmbedding (cups S x) (Set.Ioi (t:ℝ))
 have e:(fun v:ℝ=>v+(t:ℝ)) ⁻¹' Set.Ioi (t:ℝ) = Set.Ioi 0:=by
   ext1 y; change t.val < y+t.val ↔ _
   rw [Set.mem_Ioi]; exact lt_add_iff_pos_left _
 rw [←p,e, saucer_apply]; unfold ship
 rw [←integral_smul]
 refine setIntegral_congr_fun measurableSet_Ioi ?_
 intro s h
 change 0<s at h
 unfold cups highlande
 beta_reduce
 rw [smul_smul, Real.toNNReal_add h.le (show 0 ≤ (t:ℝ) from t.property), Real.toNNReal_coe, S.time,
    ContinuousLinearMap.comp_apply, neg_add_rev, Real.exp_add]

lemma low_norm (t:ℝ≥0) : ‖low S t‖≤2*(t:ℝ):=by
 refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
 intro x; let r:ℝ:=t
 have hr:0≤r:= t.property
 let J:=Ioc 0 r
 let y := R (S.E t x)
 have c:Real.exp (-r) ≤ 1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
 let z:= ∫ s in J,cups S x s
 have h: R x=z+ Real.exp (-r) • y:=by
   rw [saucer_apply,ship,←Ioc_union_Ioi_eq_Ioi hr,
          setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
           ((cupsI S x).mono_set Ioc_subset_Ioi_self) ((cupsI S x).mono_set (Ioi_subset_Ioi hr)),tail S x t]
 have hz:‖z‖≤‖x‖*r:=by
    unfold z J
    rw [← intervalIntegral.integral_of_le hr]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=‖x‖) ?_).trans
    · rw [sub_zero,abs_of_nonneg hr]
    intro s h
    rw [uIoc_of_le hr] at h
    apply (cupsP S x _).trans
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith [h.1]))
 change ‖R x - y‖≤2*r*‖x‖
 rw [h,add_sub_assoc,show Real.exp (-r) • y-y=(Real.exp (-r)-1) • y by rw [sub_smul,one_smul]]
 refine (norm_add_le ..).trans ?_
 rw [norm_smul]
 have hx:‖y‖≤ ‖x‖:=(ship_cost ..).trans (le_trans ((S.E t).le_opNorm x) (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)))
 have he: ‖Real.exp (-r)-1‖≤r:=by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr c)]; linarith [Real.add_one_le_exp (-r)]
 apply (add_le_add hz (mul_le_mul he hx (norm_nonneg _) hr)).trans; ring_nf; rfl

lemma op_one : ‖(1:H.Op)‖ ≤ 1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; rfl
lemma pow_le (x:H.Op)(n:ℕ): ‖x^n‖≤‖x‖^n:=by
 rcases n.eq_zero_or_pos with (rfl|h); · simp only [pow_zero]; exact op_one
 exact norm_pow_le' x h
def trade (n:ℕ)(t:ℝ≥0):=
   (∑ i ∈ Finset.range n, R^i * (low S t)^(n-1-i)) * R
lemma low_charge (t:ℝ≥0): ‖low S t‖ ≤2:=by
 have h:=pot S
 exact le_trans (norm_sub_le ..) ((add_le_add h ((norm_mul_le ..).trans (mul_le_one₀ h (norm_nonneg _) (S.shrinks t)))).trans (by norm_num))

private lemma sum_cap {n:ℕ}{r:ℝ} (f:ℕ→H.Op)
 (h:∀i, i<n → ‖f i‖≤r):
 ‖∑i∈Finset.range n,f i‖ ≤ (n:ℝ)*r:=by
 refine (norm_sum_le ..).trans ((Finset.sum_le_sum (s:=Finset.range n) (g:=fun _=>r) (fun i e=> h i (Finset.mem_range.mp e))).trans ?_)
 simp
lemma trade_norm (t:ℝ≥0)(n:ℕ):‖trade S n t‖≤n*(2:ℝ)^n:=by
 refine le_trans (norm_mul_le ..) ?_
 refine (mul_le_of_le_one_right (norm_nonneg _) (pot S)).trans ?_
 apply sum_cap
 intro i _
 refine (norm_mul_le ..).trans ?_
 have h: ‖R^i‖≤1:= (pow_le ..).trans (pow_le_one₀ (norm_nonneg _) (pot S))
 refine (mul_le_of_le_one_left (norm_nonneg _) h).trans ?_
 exact (pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) (low_charge S t) _).trans
    (pow_le_pow_right₀ one_le_two (by omega)))
lemma trade_E (n:ℕ)(s t:ℝ≥0): Commute (S.E s) (trade S n t):=by
 have h:= (cupE S s).symm
 unfold trade
 refine Commute.mul_right ?_ h
 apply Commute.sum_right
 intro i _
 refine (h.pow_right i).mul_right (Commute.pow_right ?_ _)
 refine h.sub_right (h.mul_right ?_)
 exact (S.time _ _).symm.trans ((congrArg S.E (add_comm s t)).trans (S.time t s))

lemma trade_price (n:ℕ)(t:ℝ≥0): trade S n t * S.E t=R^n-low S t^n:=by
 have h:Commute R (low S t):= (Commute.refl R).sub_right ((Commute.refl R).mul_right (cupE S t))
 unfold trade
 rw [← h.geom_sum₂_mul n,mul_assoc, low,sub_sub_cancel]
lemma trade_diff (n:ℕ)(s:ℝ≥0): trade S n s-trade S n (s+s)*S.E s
   = low S s ^ n * ∑i∈Finset.range n,(1+S.E s)^i:=by
 have I(A B:H.Op) (p:A*S.E s=B*S.E s): A=B:=ContinuousLinearMap.ext (congrFun ((S.whole s).equalizer A.continuous B.continuous (funext fun v => DFunLike.congr_fun p v)))
 have l:low S (s+s)= low S s*(1+S.E s):=by
   unfold low
   rw [S.time]; change R-R*(S.E s*S.E s)=_
   rw [mul_add,mul_one,sub_mul,←mul_assoc,sub_add_sub_cancel]
 have c: Commute (low S s) (1+S.E s) := (Commute.one_right _).add_right
   ((cupE S s).sub_left ((cupE S s).mul_left (Commute.refl _)))
 apply I
 rw [sub_mul,mul_assoc (trade S n _), show S.E s*S.E s=_ from (S.time _ _).symm,
      trade_price,trade_price,sub_sub_sub_cancel_left,l,c.mul_pow,
      mul_assoc,← mul_sub_one, ← geom_sum_mul (1+S.E s) n,add_sub_cancel_left]

lemma trade_err (n:ℕ)(s:ℝ≥0): ‖trade S n s-trade S n (s+s)*S.E s‖
     ≤ (2*(s:ℝ))^n * (n*(2:ℝ)^n):=by
 rw [trade_diff]
 refine (norm_mul_le ..).trans (mul_le_mul ((pow_le ..).trans
   (pow_le_pow_left₀ (norm_nonneg _) (low_norm S s) _)) ?_ (norm_nonneg _) (by positivity))
 apply sum_cap; intro i t
 exact (pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _)
        ((norm_add_le ..).trans ((add_le_add op_one (S.shrinks s)).trans (by norm_num:1+(1:ℝ)≤2))) i).trans
       (pow_le_pow_right₀ one_le_two t.le))
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
