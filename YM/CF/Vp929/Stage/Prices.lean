import YM.CF.Vp929.Stage.API
import YM.CF.Bloom.Screen

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py.Rate
open Filter Topology Metric Esti Pressure Lattice Vale RG
open Finset
abbrev Zlog (x : ℝ) := 1 + Real.log x
lemma log_ge {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Zlog x := le_add_of_nonneg_right (Real.log_nonneg hx)
lemma log_inc {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) : Zlog x ≤ Zlog y := by unfold Zlog; gcongr
lemma strip_pos {x : ℝ} (hx : 1 ≤ x) : 0 < strip x :=
  div_pos (zero_lt_one.trans_le hx) (pow_pos (zero_lt_one.trans_le (log_ge hx)) _)
lemma strip_large : Tendsto strip atTop atTop := by
  have p : Tendsto (fun x=> (Zlog x)^30 / x) atTop (𝓝 0) := by
    have hv : Tendsto (fun x=> (2^30:ℝ)*(Real.log x)^30 / x) atTop (𝓝 0) := by
      simp_rw [mul_div_assoc]; exact mul_zero (2^30:ℝ) ▸ (((Real.isLittleO_pow_log_id_atTop (n:=30)).tendsto_div_nhds_zero).const_mul _)
    refine squeeze_zero' ?_ ?_ hv; · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; positivity
    filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx h
    have he : 1 ≤ Real.log x := h; rw [← mul_pow]; unfold Zlog; gcongr; linarith
  have h : ∀ᶠ x : ℝ in atTop, 0 < (Zlog x)^30 / x := (eventually_ge_atTop (1:ℝ)).mono fun x hx =>
    div_pos (pow_pos (zero_lt_one.trans_le (log_ge hx)) _) (zero_lt_one.trans_le hx)
  change Tendsto (fun x=> x/Zlog x^30) atTop atTop
  simpa [Pi.inv_def, strip] using (Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_iff.mpr ⟨p,h⟩))
lemma strip_deriv {x : ℝ} (hx : 1 ≤ x) : HasDerivAt strip ((Zlog x-30)/ Zlog x^31) x := by
  have he:= zero_lt_one.trans_le (log_ge hx); have hh:= zero_lt_one.trans_le hx
  refine (((hasDerivAt_id' x).div (((Real.hasDerivAt_log hh.ne').const_add 1).pow 30) (pow_ne_zero _ he.ne')).congr_deriv ?_)
  change (1* Zlog x^30-x*((30:ℕ)*(Zlog x)^(30-1) * x⁻¹))/(Zlog x^30)^2 = _

  generalize E : Zlog x = y at *; field_simp <;> ring
private lemma norm_strip_growth {x y : ℝ} (hx : 1 ≤ x) (h : 60 ≤ Zlog x) (e : x ≤ y) :
    (y-x) / (2*Zlog y^30) ≤ strip y-strip x := by
  rcases e.eq_or_lt with v|v; subst y; simp
  have ht : DifferentiableOn ℝ strip (Set.Icc x y) := fun i hi=>
    (strip_deriv (hx.trans hi.1)).differentiableAt.differentiableWithinAt
  obtain ⟨s,⟨xv,vx⟩,p⟩:= exists_deriv_eq_slope strip v ht.continuousOn (ht.mono Set.Ioo_subset_Icc_self)
  have hx':=zero_lt_one.trans_le hx; have h0:= h.trans (log_inc hx' xv.le); have hz:= log_inc (hx'.trans xv) vx.le
  have hs : 0 < Zlog s := lt_of_lt_of_le (by norm_num) h0; have hy := hs.trans_le hz
  have A : 0 < y-x := by linarith
  have hB : (1:ℝ)/(2*Zlog s^30) ≤ (Zlog s-30)/ Zlog s^31 := by
    generalize E : Zlog s = z at *; field_simp; linarith
  have B:= le_trans (b:=1/(2*Zlog s^30)) (by gcongr : 1/(2*Zlog y^30) ≤ _) hB
  rw [← (strip_deriv (hx.trans xv.le)).deriv,p] at B; rw [←mul_one_div, mul_comm]; exact (le_div_iff₀ A).mp B

private lemma chill_bound {D : ℝ → ℝ} (H : Chill_v D) (c b : ℝ) (v : 0 < c) (hb : 0 < b) (k : ℕ) :
    ∀ᶠ x in atTop, |D x| * Zlog (x+b)^k ≤ c := by

  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop b, Real.tendsto_log_atTop.eventually_ge_atTop 3,
     (H k).abs.eventually (ge_mem_nhds (by simpa using v : (|(0:ℝ)|)<c))] with x q p hx A
  have hxt : 0 < x := zero_lt_one.trans_le q; have hx' : 3 ≤ Real.log x := hx
  have he : Zlog (x+b) ≤ plow x := by
    have hv := Real.log_le_log (add_pos hxt hb) (show x+b ≤ 2*x by linarith)
    rw [Real.log_mul (by norm_num) hxt.ne'] at hv
    have hh : (Real.log x)^2 ≤ (radiusB x:ℝ):= Nat.le_ceil _
    change Zlog (x+b) ≤ 1+(radiusB x:ℝ); unfold Zlog; nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hu : 1 ≤ Zlog (x+b) := log_ge (by linarith)
  have hp : 1 ≤ plow x := hu.trans he
  change |plow x^k * D x| ≤ _ at A
  rw [abs_mul, abs_of_nonneg (by positivity),mul_comm] at A
  refine le_trans ?_ A; gcongr

structure Prices (L : Side) (D : ℝ → ℝ) (x : ℝ) : Prop where
  grade : 1 ≤ x
  slope : 0 < billX L
  leaf : 0 < dleaf L x
  leaf_mono (y : ℝ) : x ≤ y → dleaf L y ≤ dleaf L x
  bank : 0 ≤ D x
  increase (y) : x ≤ y → strip x ≤ strip y
  ratio : strip (x+billX L) ≤ 2*strip x
  peri : strip x ≤ x/1000
  slow : D x ≤ billX L/512
  fast : 4*D x ≤ strip (x+billX L)- strip x
  telescope : 400*(D x/strip (x+billX L)) ≤ 1/Zlog x - 1/Zlog (x+billX L)

private lemma telescope_step {x b D : ℝ} (hx : 1 ≤ x) (hb : 0 < b) (H : D*Zlog (x+b)^32 ≤ b/400) :
    400*(D/strip (x+b)) ≤ 1/Zlog x - 1/Zlog (x+b) := by
  let y:= x+b; have e : x<y := lt_add_of_pos_right _ hb
  have hz:=zero_lt_one.trans_le hx; have hy:=hz.trans e
  let s:=Zlog x; let t:=Zlog y
  have hp:0<s:=zero_lt_one.trans_le (log_ge hx); have l:s ≤ t:=log_inc hz e.le; have h:=hp.trans_le l
  have hq:Real.log (x/y) ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hz hy); rw [Real.log_div hz.ne' hy.ne'] at hq
  have htq : b/y ≤ t-s := by
    dsimp only [t,s,Zlog]; have hh:b/y+x/y=1:=by field_simp; dsimp [y]; ring
    linarith
  calc
    _ = (400*D*t^32)/(y*t^2) := by change 400*(D/(y/t^30))=_; field_simp
    _ ≤ b/(y*t^2) := by gcongr; linarith [show D*t^32 ≤ b/400 from H]
    _ = b/y/(t*t) := by field_simp
    _ ≤ (t-s)/(s*t) := by gcongr
    _ = _ := by change _=1/s-1/t; field_simp

lemma eventual_prices {D : ℝ → ℝ} {R : Patch} (p : 0 < billX R.L) (h : Chill_v D) (hp : ∀ᶠ x in atTop, 0 ≤ D x) :
    ∀ᶠ x in atTop, Prices R.L D x := by
  obtain ⟨i,hi,H⟩:= glimp_T (R:=R)
  let b:= billX R.L; have hb:0<b:= p
  filter_upwards [eventually_ge_atTop i,eventually_ge_atTop b,Real.tendsto_log_atTop.eventually_ge_atTop 1000,hp,
    chill_bound h (b/512) b (by positivity) hb 0,chill_bound h (b/400) b (by positivity) hb 32,
    chill_bound h (b/8) b (by positivity) hb 30] with x q q' xh v h₀ hu hv
  have hx:=hi.trans q; have h':=zero_lt_one.trans_le hx; have h:= H x q
  simp only [abs_of_nonneg v,pow_zero,mul_one] at h₀ hu hv
  have hh : 1000 ≤ Zlog x := by unfold Zlog; linarith [show 1000 ≤ Real.log x from xh]
  have hL : 60 ≤ Zlog x := le_trans (by norm_num) hh
  have hg : 0 < Zlog x := zero_lt_one.trans_le (log_ge hx)
  refine ⟨hx,p,h.1,fun y e => (h.2.2 y e).1,v,fun y e=>?_,?_,?_,h₀,?_,telescope_step hx p hu⟩
  · exact sub_nonneg.mp ((show 0 ≤ (y-x)/(2*Zlog y^30) from by positivity).trans (norm_strip_growth hx hL e))
  · calc
      strip _ ≤ (2*x)/Zlog x^30 := by
        change (x+b)/Zlog (x+b)^30 ≤ _; gcongr
        · linarith
        · exact log_inc h' (le_add_of_nonneg_right hb.le)
      _ = _ := by change _=2*(x/Zlog x^30); ring
  · change x/Zlog x^30 ≤ _; gcongr; exact hh.trans (le_self_pow₀ (log_ge hx) (by omega))
  have ha:= norm_strip_growth hx hL (show x≤x+b by linarith)
  refine le_trans ?_ ha; rw [add_sub_cancel_left]; apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos (hg.trans_le (log_inc h' (by linarith))) _))).mpr; linarith

lemma prices_sum {L : Side} {D : ℝ → ℝ} {x : ℝ} (p : ∀ y ≥ x, Prices L D y) (i : ℕ) :
    ∑ u∈Finset.range i, D (hat L x u) / strip (hat L x (u+1)) ≤ 1/400 := by
  let X:= hat L x
  have h y : Prices L D (X y) := p _ (Vale.crown ..)
  have H y : 1 ≤ Zlog (X y) := log_ge (h y).grade
  have he(i:ℕ): 400*(∑ u∈Finset.range i,D (X u)/strip (X (u+1))) ≤ 1 - 1/Zlog (X i) := by
    induction i with
    | zero=> rw [sum_range_zero,mul_zero]; exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le (H _))).2 (H _))
    | succ i ih=>
      have p:= (h i).telescope
      rw [show X i+billX L=X (i+1) by dsimp only [X]; rw [hat_succ]; rfl] at p; rw [sum_range_succ]; linarith
  change ∑ u∈Finset.range i,D (X u)/strip (X (u+1)) ≤ 1/400
  linarith [he i,one_div_pos.mpr (zero_lt_one.trans_le (H i))]
variable {L : Side} {D : ℝ → ℝ} {x : ℝ}
@[simp] theorem hat_zero : hat L x 0 = x := by simp [hat]
theorem hat_step (i : ℕ) : hat L x (i+1) = hat L x i + billX L := by rw [hat_succ]; rfl
theorem hat_mono : Monotone (hat L x) := monotone_nat_of_le_succ fun i=> by rw [hat_step]; exact le_add_of_nonneg_right (pitch L)
theorem hat_up {y : ℝ} (i : ℕ) : hat L (x+y) i = hat L x i + y := by unfold hat; ring
lemma Prices.enroll (p : Prices L D x) {b : ℝ} (hl : 3/4*x ≤ b) (hu : b ≤ 3/2*x)
    {z : ℂ} (h : ‖z-(b:ℂ)‖ ≤ 3*strip x) : enters x z ∧ ‖z‖ ≤ 2*x ∧ entersReal x z.re := by
  have hx : 0 < x := zero_lt_one.trans_le p.grade; have hp:= p.peri; have η:= Complex.abs_re_le_norm (z-b); have θ:= Complex.abs_im_le_norm (z-b)
  rw [Complex.sub_re,Complex.ofReal_re] at η; rw [Complex.sub_im,Complex.ofReal_im,sub_zero] at θ
  have H: - (3*strip x) ≤ z.re-b ∧ z.re-b ≤ 3*strip x := abs_le.mp (η.trans h)
  refine ⟨⟨by linarith [H.1],by linarith [H.2],θ.trans h⟩, ?_,by constructor <;> linarith [H.1,H.2]⟩
  have e:= norm_sub_norm_le z (b:ℂ); rw [Complex.norm_real, Real.norm_eq_abs,abs_of_pos (by linarith)] at e; linarith
lemma Prices.enroll' (p : Prices L D x) {b z : ℝ} (hl : 3/4*x ≤ b) (hu : b ≤ 3/2*x)
    (h : |z-b| ≤ strip x) : entersReal x z ∧ enters x z := by
  have hp:= p.enroll hl hu (show ‖(z:ℂ)-(b:ℂ)‖ ≤ _ from by rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; linarith [abs_nonneg (z-b)])
  exact ⟨hp.2.2,hp.1⟩
lemma matched_of_enters (p : Prices L D x) {b : ℝ} (h : enters x (b:ℂ)) : matchedX x b := by
  obtain ⟨(hl : 53/100*x ≤ b),(hu : b ≤ 7/4*x),_⟩:= h
  have hx:=p.grade; constructor <;> linarith
end YM.CF.Py.Rate
