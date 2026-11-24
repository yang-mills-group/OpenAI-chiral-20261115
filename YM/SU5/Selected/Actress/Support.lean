import YM.SU5.Selected.Actress.Moves
/-!
# Ordered correlations as **time-only** tempered distributions

Support condition along partially tested axes; because each independent gap corresponds to a heat op carrying genuinely nonnegative H, such tests vanish for compact negative-frequency support, with all the other gap variables kept fixed arbitrarily. Not here proving joint support under other test norms/signs. Main root `PVM` positivity already separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open Function Filter Real Set Complex Analysis Boundary Probe OS.Semigroup MeasureTheory Measure
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "U"=> S.edge
local notation "P"=> spectralP S
variable (f: Probe ℝ)(s: HasCompactSupport ⇑f)(p: tsupport f⊆ Set.Iio 0)(x y:H)
local notation "A"=> Alps.evolve S
include s p
lemma view_chart : ∫ t:ℝ, inner ℂ x (U t x) * Probe.hat f t = 0 :=by
 let Q:= spectralP S; have he: Set.Iio (0:ℝ)=(Set.Ici 0)ᶜ:= Set.compl_Ici.symm; have hx:Q.region (Set.Ici 0)ᶜ x=0:=by rw [←he, (show Q.region (Set.Iio 0)=_ from bright_region S)]; simp
 exact ((A).suffices_tests Q (Alps.moment S) (Set.Ici 0) isClosed_Ici x).1 hx f s (he ▸ p) -- Sphere
omit s p
private abbrev iF:= SNAG.send (Alps.evolve S) f
open SNAG (normer)
private lemma half_tape : inner ℂ x ((iF S f) y) = (SNAG.normer ℝ:ℂ)* (∫ z:ℝ, inner ℂ x (U z y)*Probe.hat f z) := by
 let v:=SNAG.send A f; rw [←integral_const_mul]; unfold iF; rw [SNAG.sending,←integral_inner (SNAG.over ..)]; apply integral_congr_ae; apply Eventually.of_forall; intro i; dsimp only;
 rw [inner_smul_right]; unfold SNAG.cut; change (((SNAG.normer ℝ:ℝ):ℂ)* (Probe.hat f i))*_= _; change (((SNAG.normer ℝ:ℝ):ℂ)* (Probe.hat f i))*inner ℂ x (U i y) = _; ring
include s p
lemma view_H : ∫ t:ℝ, inner ℂ x (U t y) * Probe.hat f t=0:=by
 let Q:=iF S f; have he(v:H):inner ℂ v (Q v)=0:= by unfold Q; rw [half_tape,view_chart S f s p,mul_zero]
 have hz:Q=0:=by
    apply ContinuousLinearMap.ext; intro i; refine LinearMap.congr_fun (?_ : Q.toLinearMap=(0:H.Op).toLinearMap) i; apply (ext_inner_map _ _).mp; intro v; apply (starRingEnd ℂ).injective; rw [inner_conj_symm,inner_conj_symm]; exact (he v).trans (inner_zero_right _).symm
 have hv: (SNAG.normer ℝ:ℂ)* (∫ z:ℝ, inner ℂ x (U z y)*Probe.hat f z)=0:= by rw [←half_tape]; change inner ℂ x (Q y) = _; rw [hz]; simp
 exact (mul_eq_zero.mp hv).resolve_left (Complex.ofReal_ne_zero.mpr (inv_ne_zero Probe.prepos.ne'))
omit s p
section joints
variable {d:Type*}(F:d→ H.Op)(l v:List d)
local notation "κ"=> trip S F
variable {a₁:Type*}
-- vanish at disjoint gap; others held literally. can use all distinct (usual indexing).
private lemma equalV (u v:d→ℂ)(h:∀i∈l,u i=v i): κ l u=κ l v:= by induction l with
 | nil=> rfl
 | cons i l p=> rw [trip,trip,h i List.mem_cons_self,p (fun x t=>h _ (List.mem_cons_of_mem _ t))]
variable [DecidableEq d]
include s p
lemma tested_one(z:d→ℂ)(i:d)(w:i∉ l)(h:i∉ v): ∫ t:ℝ, inner ℂ x ((trip S F (l++i::v) (update z i (t:ℂ))) y)*Probe.hat f t=0 :=by
 let L:=(κ l z).adjoint x; let R:= F i (κ v z y)
 have he(a:ℝ): inner ℂ x ((κ (l++i::v) (update z i (a:ℂ))) y)=inner ℂ L (U a R):=by
    let f(t:ℝ):= update z i (t:ℂ); have hf(x t)(e:x≠ i) : f t x=z x:=update_of_ne e ..; change inner ℂ x ((κ _ (f a)) y)=_; rw [unite,trip,equalV _ F v (f a) _ (fun x v=> hf x _ (fun t=>h (t ▸ v))), equalV _ F l (f a) _ (fun x v=> hf x _ (fun t=>w (t ▸ v)))]; unfold f; rw [update_self,balcony_floor]; exact (ContinuousLinearMap.adjoint_inner_left (κ l z) (S.edge a R) x).symm -- arg
 simp_rw [he]; exact view_H S f s p L R
omit s p
variable [Fintype d]
-- full **radian relative time** distribution including arbitrary number (Δt empty). Pi sup norm, Lebesgue (check Mathlib uses pi.measure pi volumes). F preserving typed.[Fintype].
local notation "Θ"=> (d→ℝ)
abbrev readWave (z:d→ℝ):= inner ℂ x (κ l (fun i=> ((z i:ℝ):ℂ)) y)
private lemma wave_bdd:∃ (C:ℝ),∀ (z:d→ℝ),‖readWave S x y F l z‖≤ C:= by
 let B:= (l.map (fun i=> ‖F i‖)).prod; refine ⟨‖x‖ * (B*‖y‖),fun z=>?_⟩; unfold readWave; refine (norm_inner_le_norm (𝕜:=ℂ) ..).trans ?_; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact ((κ l _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (flight S F l _) (norm_nonneg _))
lemma wave_c : Continuous (readWave S x y F l):= continuous_const.inner ((flight_cont S y F l).comp (continuous_pi (fun i=> continuous_ofReal.comp (continuous_apply i)))) -- tune args
local notation "σ"=> readWave S x y F l
private lemma mask_fee(g: Probe (d→ℝ)): Integrable (fun x=> g x*σ x):= by rw [show (fun x=> g x *σ x)= σ • ⇑g from funext (fun i=>mul_comm ..)]; exact Integrable.smul_of_top_right g.integrable (memLp_top_of_bound (wave_c ..).aestronglyMeasurable _ (ae_of_all _ (wave_bdd S x y F l).choose_spec)) -- lemma name left
-- want Probe Distn.
def temporalJoint : Distn (d→ℝ):= by
 let W: Probe Θ→ₗ[ℂ] ℂ:=
    { toFun f:= (∫ x,f x* σ x)
      map_add' := fun f g=>by simp only [_root_.add_apply,add_mul]; rw [integral_add (mask_fee ..) (mask_fee ..)]
      map_smul' := fun c f=>by simp only [_root_.smul_apply,smul_eq_mul]; simp only [mul_assoc, ← integral_const_mul, RingHom.id_apply] } -- `_root_.`
 -- norm integrable W. use weight_eq general. Haar π.
 refine ⟨W,?_⟩; apply continuous_of_continuousAt_zero W; apply Metric.tendsto_nhds.mpr; intro ε h
 let g:=(wave_bdd S x y F l); let a : Probe Θ→L[ℂ] MeasureTheory.Lp (α:=Θ) ℂ 1 volume:= SchwartzMap.toLpCLM ℂ ℂ 1 volume
 let G(f:Probe Θ) := ‖a f‖ * g.choose; have hp(f : Probe Θ): ‖W f‖ ≤ G f:= by
    unfold G; rw [show ‖a f‖=_ from (show ‖a f‖=∫ x,‖f x‖ from SchwartzMap.norm_toLp_one)]
    rw [← integral_mul_const]; let b:=g.choose; refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (ae_of_all _ (fun i=>?_)); rw [norm_mul]; exact mul_le_mul_of_nonneg_left (g.choose_spec i) (norm_nonneg _)
 have he: Tendsto G (𝓝 0) (𝓝 0):= by
    refine Continuous.tendsto' (a.continuous.norm.mul_const g.choose) _ _ ?_; change ‖a 0‖*_=_; rw [map_zero,norm_zero,zero_mul]
 filter_upwards [he.eventually (gt_mem_nhds h)] with v hv; rw [map_zero,dist_zero_right]; exact (hp v).trans_lt hv
#check @SchwartzMap.norm_toLp_one
#check Integrable.smul_of_top_right
#check Continuous.tendsto'
lemma consumes (g:Probe (d→ℝ)): temporalJoint S x y F l g= (∫ x,g x * σ x):=rfl
end joints
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms view_H
#print axioms tested_one
#print axioms consumes
