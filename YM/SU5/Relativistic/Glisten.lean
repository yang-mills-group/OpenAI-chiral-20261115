import YM.SU5.Relativistic.FallT
/-! # kill all slow K weights, find honest finite-time probe in any compact band & priced stencils at both infinities. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "ω"=>2*Real.pi
local notation "ℱ"=>Set.Icc (-π) π

-- purchase killing polynomial
lemma runHigh (k:Behind)(p:k∈sunshine)(a:ℝ): ∃ i, a< amp k i:=by
 have he:0<ω:=by positivity
 obtain ⟨r,h⟩:= exists_nat_gt (|a|/(2*π))
 let i:WalkA:=fun _=>r
 have hu:a < levelx k i 0:=by
    rw [div_lt_iff₀ he] at h; unfold levelx; change a < k 0+ω*(↑(r:ℤ):ℝ); push_cast; linarith only [h,le_abs_self a,(p 0 (Set.mem_univ _)).1]
 exact ⟨i,hu.trans_le ((le_abs_self _).trans (amp_ge k i 0))⟩
private lemma node_cut (x y :Behind)(i j:WalkA)(hx:x∈sunshine)(hy:y∈sunshine)(h:amp x i < amp y j)(b v : Bool): nodes b x i 1 ≠ nodes v y j 1 :=by
 have hA:= amp_pos hx i; have hB:=amp_pos hy j; unfold nodes; intro e; have hp:= Real.exp_injective e; cases b <;> cases v<;> norm_num [sg] at hp <;> linarith
lemma pocket (a:ℝ) : ∃ W:Finset WalkA,∀ k∈sunshine,∀ i∉ W, a ≤ amp k i:=by
 have h:0<ω:=by positivity
 let A:=max 0 a; obtain ⟨n,hn⟩:=exists_nat_gt ((A+π)/ω); let W:Set WalkA:= Set.Icc (fun _=> -(n:ℤ)) (fun _=> n); classical
 refine ⟨(Set.finite_Icc (fun _:Fin 3=> -(n:ℤ)) (fun _=> (n:ℤ))).toFinset,fun i hi j p=>?_⟩
 by_contra! t; rw [Set.Finite.mem_toFinset] at p; apply p
 have he(x:Fin 3): -(n:ℤ) ≤ j x ∧ j x ≤ n:= by
    have hz: |i x+ω*j x|<A:= (amp_ge i j x).trans_lt (t.trans_le (le_max_right ..))
    obtain ⟨v,u⟩:=abs_lt.mp hz; have hv:= (div_lt_iff₀ h).mp hn; have hx:=hi x (Set.mem_univ _)
    constructor
    · exact_mod_cast (show -((n:ℕ):ℝ) ≤ (j x:ℝ) from le_of_lt (by nlinarith only [h,v,u,hv,hx.1,hx.2]))
    exact_mod_cast (show (j x:ℝ) ≤ (n:ℝ) from le_of_lt (by nlinarith only [h,u,hv,hx.1,hx.2]))
 exact ⟨fun i=>(he i).1,fun i=>(he i).2⟩

lemma tariff (a:ℝ) : ∃ (s:Finset ℤ)(c:Behind→ℤ→ℝ), (∀ i, Continuous fun k=> c k i) ∧ ∀ k∈sunshine,∀ b:Bool,
    (∀ j:WalkA, 0 ≤ speaker s c k j b) ∧ (∃ j:WalkA, 0<speaker s c k j b) ∧ (∀ j, amp k j < a → speaker s c k j b=0) :=by
 obtain ⟨W,p⟩:= pocket a; let U:= W ×ˢ (univ:Finset Bool)
 obtain ⟨s,c,h⟩:=score_roots U
 -- syntax ∀
 refine ⟨s,c,h.1,fun k q b=>?_⟩
 have hn i : speaker s c k i b=∏ j∈U,(nodes b k i 1-nodes j.2 k j.1 1)^2:=by
    have hv:= (tally_int s c k i b).symm.trans (h.2 k (nodes b k i 1) (by exact_mod_cast (Real.exp_pos _).ne'))
    dsimp only at hv; exact Complex.ofReal_injective (hv.trans (by push_cast; rfl))
 let B(i):= amp k i; let l:ℝ:=∑ j∈W, B j
 obtain ⟨i,hx⟩:= runHigh k q l
 refine ⟨fun i=> by rw [hn]; exact Finset.prod_nonneg fun j _=> sq_nonneg _,⟨i,?_⟩,fun j hv=>?_⟩
 · rw [hn]; refine Finset.prod_pos fun v e=>sq_pos_of_ne_zero ?_
   exact sub_ne_zero.mpr (node_cut k k v.1 i q q ((Finset.single_le_sum (f:=B) (s:=W) (fun i _=> (amp_pos q i).le) (mem_product.mp e).1).trans_lt hx) v.2 b).symm
 rw [hn]; exact Finset.prod_eq_zero (i:=(j,b)) (mem_product.mpr ⟨ Classical.byContradiction fun g=> hv.not_ge (p k q j g),mem_univ _⟩ : (j,b) ∈ U) (by simp)

variable {U:Set Behind}(H:IsCompact U)(h:U⊆sunshine)
local notation "V"=> U ×ˢ Set.Icc (-π) π
attribute [local instance] screen_fin
lemma circle_continuous (f:Behind → ℝ→ℂ)(k:ℤ)(p:ContinuousOn (uncurry f) V)(Q:IsCompact U) : ContinuousOn (fun u=> pluse k (f u)) U:=by
 let F:=fun x:Behind×ℝ=> surge k x.2 * f x.1 x.2
 have he:ContinuousOn F V:=((surge_cont.comp (continuous_const.prodMk continuous_snd)).continuousOn).mul p
 obtain ⟨B,v⟩:=(Q.prod isCompact_Icc).exists_bound_of_continuousOn he
 have hp(a)(p:a∈U) : ContinuousOn (fun t:ℝ=> F (a,t)) ℱ := he.comp (continuous_const.prodMk continuous_id|>.continuousOn) fun i g=> ⟨p,g⟩
 let μ: Measure ℝ:= volume.restrict screen
 have ht : ∀ᵐ a:ℝ ∂μ,a∈ℱ:= (ae_restrict_mem paneM).mono (fun _ p=>Ioc_subset_Icc_self p)
 intro x H'; have hU : ∀ᶠ i in 𝓝[U] x,i∈U := self_mem_nhdsWithin; change Tendsto (fun a:Behind=>∫ t,F (a,t) ∂μ) (𝓝[U] x) (𝓝 (∫ t,F (x,t) ∂μ)); refine tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun _=> B) (by filter_upwards [hU] with a p; exact ((hp _ p).mono Ioc_subset_Icc_self).aestronglyMeasurable paneM) (hU.mono fun a p=> ht.mono fun t g=> v _ ⟨p,g⟩) (integrable_const _) ?_
 exact ht.mono fun a g=> (show ContinuousWithinAt (F ∘ fun t=> (t,a)) U x from ContinuousWithinAt.comp_of_eq (g:=F) (f:=fun t:Behind=> (t,a)) (he (x,a) ⟨H',g⟩) ((continuous_id.prodMk continuous_const).continuousWithinAt) (show MapsTo (fun t=> (t,a)) U V from fun t v=>⟨v,g⟩) rfl)
lemma continuous_cut (f:Behind→ ℝ→ℂ)(p:ContinuousOn (uncurry f) V){k:Behind}(h:k∈U):IntegrableOn (f k) screen:=by
 have hp(a)(p':a∈U) : ContinuousOn (f a) ℱ := p.comp (continuous_const.prodMk continuous_id|>.continuousOn) fun i g=> ⟨p',g⟩
 exact (hp k h).integrableOn_Icc.mono_set Ioc_subset_Icc_self
end YM.CF.Crest.Sleet
