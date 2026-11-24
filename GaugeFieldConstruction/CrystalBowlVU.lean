import GaugeFieldConstruction.CrystalRouteVU
/-!
 Woven momentum estimates for comparison. PiNorm, #110 etc incl legalizations on A pressed false.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Filter MeasureTheory Measure Complex Boundary Probe Row OS Word
open scoped Topology BigOperators NNReal ENNReal ContDiff Classical
private lemma PeakMercyRC (i:Axis)(a:E4):∃ (j:SpaceAxis),‖(part i a:Tang)‖ = ‖part i a j‖:=by
 obtain ⟨b,_,h⟩:=Finset.exists_max_image Finset.univ (fun j=>‖part i a j‖) Finset.univ_nonempty
 refine ⟨b,le_antisymm ((pi_norm_le_iff_of_nonneg (x:=part i a) (norm_nonneg _)).mpr (fun j=> h j (Finset.mem_univ _))) ?_⟩
 exact (pi_norm_le_iff_of_nonneg (x:=part i a) (norm_nonneg _)).mp le_rfl b
private lemma MonShiftRC (i:Axis)(F:E4→ℝ)(k:ℕ)(x:ℝ)(μ:Measure E4) (q:x ≤ (2*k:ℕ)) (hq:0 ≤ᵐ[μ] F) (ht: Integrable F μ)
    (H : ∀ j: SpaceAxis, Integrable (fun p=> F p * ‖part i p j‖^(2*k)) μ) : Integrable (fun p=> F p * (1+‖part i p‖)^x) μ := by
 let f(p:E4) (j: SpaceAxis):= F p*‖part i p j‖^(2*k)
 let y(p:E4):= F p + ∑ j,f p j
 have hy:Integrable y μ:= ht.add (integrable_finsetSum Finset.univ fun j _=>H j) -- defeq?
 refine (hy.const_mul ((2:ℝ)^(2*k))).mono' (ht.1.mul ?_) ?_
 · have hp:Continuous (fun a => part i a):=continuous_pi fun j=> by unfold part; fun_prop
   exact (((continuous_const.add hp.norm).rpow_const fun a=> Or.inl (show 1+‖part i a‖≠0 from ne_of_gt (by positivity))).aestronglyMeasurable)
 filter_upwards [hq] with p h
 change 0≤F p at h; have he j:0≤f p j:=mul_nonneg h (by positivity)
 let G:=F p + ∑ j,f p j
 have hg: F p ≤ G:=le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>he j)
 change ‖F p*(1+‖part i p‖)^x‖ ≤ 2^(2*k)*G
 obtain ⟨i₀,ζ⟩:=PeakMercyRC i p
 let w:=‖part i p i₀‖; rw [Real.norm_of_nonneg (by positivity),ζ]
 have hw:0≤w:=norm_nonneg _
 have hl: (1+w)^x ≤ (1+w)^(2*k):= by exact (Real.rpow_le_rpow_of_exponent_le (by linarith) q).trans_eq (Real.rpow_natCast ..)
 refine (mul_le_mul_of_nonneg_left hl h).trans ?_; by_cases hh:w≤1
 · calc
    _ ≤ G* (2:ℝ)^(2*k):=mul_le_mul hg (by gcongr <;> linarith) (pow_nonneg (by linarith) _) (hg.trans' h)
    _ =_:=mul_comm ..
 have hp: f p i₀ ≤ G:=(Finset.single_le_sum (fun j _=>he j) (Finset.mem_univ i₀)).trans (le_add_of_nonneg_left h)
 calc
    _ ≤ F p*((2:ℝ)*w)^(2*k):=by gcongr; linarith
    _ = 2^(2*k)* f p i₀:=by change _=2^_* (F p* w^(2*k)); rw [mul_pow]; ring
    _ ≤ _:= mul_le_mul_of_nonneg_left hp (by positivity)
noncomputable abbrev MomShiftRC (i:Axis)(t x:ℝ)(p:E4):= Real.exp (-t*p i)*(1+‖part i p‖)^x
variable {G:Gauge}{L:Register G}{S:Table L}
lemma softMomRC (i:Axis)(V: Chamber S i)(H:S.Hierarchy)(A:Weight L)(x:ℝ)(t:ℝ≥0)(h:Lowered i A t):Integrable (MomShiftRC i (t+t) x) (ν V A):=by
 let p(k:ℕ)(j:SpaceAxis):= placed_moment V H A (i.succAbove j) (i.succAbove_ne j) k t h
 obtain ⟨B,u⟩:= exists_nat_gt x
 apply MonShiftRC i _ B
 · push_cast; linarith [u] -- tune
 · exact Eventually.of_forall fun a=> (Real.exp_pos _).le
 · have he:=p 0 0; unfold mom at he; simpa using he
 intro b; have he:= p B b; rw[NNReal.coe_add] at he; exact he
private lemma hardProfitRC (i:Axis)(V: Chamber S i)(H:S.Hierarchy)(A:Weight L)(p:Pressed i A)(x:SpaceAxis)(k:ℕ) : ∀ᶠ D:ℕ in atTop, Integrable (fun y:E4=> ((1+y i)⁻¹)^D * ‖part i y x‖^(2*k)) (ν V A) :=by
 obtain ⟨D,hD⟩:=pay_moment V H A p _ (i.succAbove_ne x) k
 filter_upwards [eventually_ge_atTop D] with j h
 refine hD.mono' ?_ ?_
 · exact (show Measurable _ from by unfold part; fun_prop).aestronglyMeasurable
 filter_upwards [before V A] with y hy; rw [Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by linarith)) h) (pow_nonneg (norm_nonneg _) _)
noncomputable abbrev DecMomRC (i:Axis)(D:ℕ)(x:ℝ)(p:E4):=((1+p i)⁻¹)^D*(1+‖part i p‖)^x
lemma hardMomRC (i:Axis)(V: Chamber S i)(H:S.Hierarchy)(A:Weight L)(p:Pressed i A)(x:ℝ): ∀ᶠ D in atTop,Integrable (DecMomRC i D x) (ν V A):=by
 obtain ⟨B,u⟩:=exists_nat_gt x
 filter_upwards [eventually_all.mpr (fun j=> hardProfitRC i V H A p j B),hardProfitRC i V H A p 0 0] with D h hp
 apply MonShiftRC i _ B _ _ _ _ _ h
 · push_cast; linarith
 · filter_upwards [before V A] with y hy
   change 0 ≤ ((1+y i)⁻¹)^D; positivity
 simpa only [Nat.mul_zero,pow_zero,mul_one] using hp
#print axioms hardMomRC
end YM.NSF.Outer
end
