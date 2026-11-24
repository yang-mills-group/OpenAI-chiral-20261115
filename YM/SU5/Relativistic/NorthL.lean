import YM.SU5.Relativistic.Streak
/-! # Energy aliases. Need CONTROL signs beyond given sponsorship. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "ω"=> 2 * Real.pi

-- use general τ over compact k-set, not statement merely at fixed k.
variable {U:Set Behind}(H:IsCompact U)(h:U⊆sunshine)
local notation "Z"=>Set.Icc (-π) π
local notation "V"=>U ×ˢ Set.Icc (-π) π
attribute [local instance] screen_fin

lemma slat_cost {k:Behind}(w:k∈sunshine)(j:Cover)(t:ℝ) (u:t∈Set.Icc (-π) π) (i:Axis): ContinuousAt (fun p:Behind×ℝ => slat (tack p.1 p.2) j i) (k,t):=by
 obtain ⟨e,f⟩:= tack_equiv ℤ; obtain ⟨⟨x,n⟩,rfl⟩:= e.surjective j; simp_rw [f,short_exact]
 let A(p:Behind × ℝ):=amp p.1 x
 have he : 0<A (k,t):=amp_pos w x
 unfold shortLap bleat smoothZip zip skirt
 have hm(i:Fin 3): Continuous (fun p:Behind×ℝ=>levelx p.1 x i):= (continuous_apply i).comp ((levelx_c x).comp continuous_fst)
 refine ContinuousAt.mul ?_ ?_
 · exact Complex.continuous_ofReal.continuousAt.comp (Continuous.continuousAt (f:=fun p:Behind×ℝ=>tack _ _ i) ((continuous_apply i).comp (tack_c.comp (((levelx_c x).comp continuous_fst).prodMk (continuous_snd.add continuous_const)))))
 fun_prop (disch:=first|assumption| (norm_cast; change A (k,t)^2+_ ≠ _; positivity))

include H h
lemma costume (a:Axis) : ∃ d:Cover→ℝ, Summable d ∧ (∀ j,0≤d j) ∧ ∀ p:Behind × ℝ, p∈ V → ∀ j:Cover,‖slat (tack p.1 p.2) j a‖ ≤ d j:=by
 obtain ⟨C,k,d⟩:= boundC a
 obtain ⟨B,p⟩:= (H.prod isCompact_Icc).exists_bound_of_continuousOn (f:=fun p:Behind×ℝ=> slat (tack p.1 p.2) 0 a) (fun p i => (slat_cost (h i.1) _ p.2 i.2 a).continuousWithinAt)
 let m:Cover→ℝ:=Pi.single (0:Cover) |B|
 refine ⟨fun i=> C*income i+m i,(wallet.mul_left C).add (hasSum_pi_single (0:Cover) _).summable,?_ ,?_⟩
 · intro j; apply add_nonneg (mul_nonneg k.le (income_2 j).le); by_cases ht:j=0 <;> simp [m,Pi.single_apply,ht]
 intro t u j; by_cases hz:j=0
 · subst j; change _ ≤ _+ (Pi.single (0:Cover) |B|:Cover→ℝ) (0:Cover); rw [Pi.single_eq_same]; exact ((p t u).trans (le_abs_self _)).trans (le_add_of_nonneg_left ((mul_pos k (income_2 _)).le))
 change _ ≤ C*income j+m j; unfold m; rw [Pi.single_eq_of_ne hz,add_zero]; exact d (tack _ _) (spectrum_b _ (h u.1) _ u.2) (tac_nz (h u.1)) _ hz
lemma heat_cont (i:Axis):ContinuousOn (fun p:Behind × ℝ => heatLine p.1 p.2 i) (U×ˢ Set.Icc (-π) π):=by
 obtain ⟨C,w,_,v⟩:= costume H h i
 apply continuousOn_tsum
 · intro j x hx; exact (slat_cost (h hx.1) _ x.2 hx.2 i).continuousWithinAt
 · exact w
 intro n x hx; exact v x hx n
-- all-k pluse computed density
lemma pluse_spans (i:Axis) (k:ℤ) : ContinuousOn (fun p:Behind=> pluse k (fun t =>heatLine p t i)) U:=by
 let f:=fun p:Behind×ℝ=> surge k p.2 * heatLine p.1 p.2 i
 have he:ContinuousOn f V:=((surge_cont.comp (continuous_const.prodMk continuous_snd)).continuousOn).mul (heat_cont H h i)
 obtain ⟨B,v⟩:=(H.prod isCompact_Icc).exists_bound_of_continuousOn he
 have hp(a)(p:a∈U) : ContinuousOn (fun t:ℝ=> f (a,t)) Z := he.comp (continuous_const.prodMk continuous_id|>.continuousOn) fun i g=> ⟨p,g⟩
 let μ: Measure ℝ:= volume.restrict screen
 have ht : ∀ᵐ a:ℝ ∂μ,a∈Z:= (ae_restrict_mem paneM).mono (fun _ p=>Ioc_subset_Icc_self p)
 intro x H'; have hU : ∀ᶠ i in 𝓝[U] x,i∈U := self_mem_nhdsWithin; change Tendsto (fun a:Behind=>∫ t,f (a,t) ∂μ) (𝓝[U] x) (𝓝 (∫ t,f (x,t) ∂μ)); refine tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun _=> B) (by filter_upwards [hU] with a p; exact ((hp _ p).mono Ioc_subset_Icc_self).aestronglyMeasurable paneM) (hU.mono fun a p=> ht.mono fun t g=> v _ ⟨p,g⟩) (integrable_const _) ?_
 exact ht.mono fun a g=> (show ContinuousWithinAt (f ∘ fun t=> (t,a)) U x from ContinuousWithinAt.comp_of_eq (g:=f) (f:=fun t:Behind=> (t,a)) (he (x,a) ⟨H',g⟩) ((continuous_id.prodMk continuous_const).continuousWithinAt) (show MapsTo (fun t=> (t,a)) U V from fun t v=>⟨v,g⟩) rfl)
omit H h
variable {k : Behind}(p:k∈sunshine)
def liftH (k: Behind)(i:Axis) (j: WalkA)(t:ℝ):ℂ:= ↑(tack (levelx k j) t i) * shortLap k j t
lemma vertical_s (a:ℝ)(x:ℝ): (x:ℂ)*smoothZip a 8 x= Complex.I * biasStamp (smoothZip a 8) x:=by unfold biasStamp; simp [←mul_assoc]
include p
lemma lift_integrable(i:Axis)(j:WalkA): Integrable (liftH k i j):=by
 have h:=amp_pos p j; let T:=levelx k j
 induction i using Fin.lastCases with
 | last=> unfold liftH; simp only [tack, Fin.lastCases_last] -- maybe tack
          convert (bias_paid (a:=amp k j) h 7).const_mul (bleat k j*Complex.I) using 1
          ext1 t; change _ = bleat k j*I*biasStamp (smoothZip (amp k j) 8) t; rw [shortLap, mul_left_comm,vertical_s,mul_assoc]
 | cast i => unfold liftH; simp only [tack,Fin.lastCases_castSucc]; exact ((smooth_paid h 8).const_mul (bleat k j)).const_mul _
lemma radical (i:Axis)(n:ℤ) : HasSum (fun j: WalkA=> integrated (liftH k i j) n) (pluse n (fun t=>heatLine k t i)):=by
 let z:= fun t:ℝ=> tack k t; let f(x:Cover)(t:ℝ):= surge n t*slat (z t) x i
 have hp:∀ᵐ t:ℝ ∂(volume.restrict screen), t∈ Z:= (ae_restrict_mem paneM).mono (fun _ p=>Ioc_subset_Icc_self p)
 obtain ⟨C,w,_,v⟩:= costume (U:={k}) isCompact_singleton (Set.singleton_subset_iff.mpr p) i
 have hz:HasSum (fun j:Cover=> ∫ t in screen,f j t) (pluse n (fun t=>heatLine k t i)):=by
    refine hasSum_integral_of_dominated_convergence (fun x _=> C x) ?_ ?_ (Eventually.of_forall (fun x=>w)) (integrable_const _) ?_
    · intro j; have hw(t:ℝ)(u:t∈Z): ContinuousAt (f j) t:= ((surge_cont.comp (continuous_const.prodMk continuous_id)).continuousAt).mul ((slat_cost p j t u i).comp (continuousAt_const.prodMk continuousAt_id)) -- .comp 
      exact ((show ContinuousOn (f j) Z from fun a t=> (hw a t).continuousWithinAt).mono Ioc_subset_Icc_self).aestronglyMeasurable paneM
    · intro j; apply hp.mono; intro t u; unfold f; rw [norm_mul,surge_norm,one_mul]; exact v (k,t) ⟨Set.mem_singleton _,u⟩ j
    exact hp.mono fun a g=> ((spending (x:=tack k a) (spectrum_b k p a g) (tac_nz p) i).of_norm.hasSum).mul_left _
 obtain ⟨e,h⟩:= tack_equiv ℤ
 apply (e.hasSum_iff.mpr hz).prod_fiberwise; intro j
 simp only [Function.comp_apply,h]; have ht:=timefold n (liftH k i j) (lift_integrable p i j); convert ht using 1; ext1 l; unfold f; simp_rw [z,short_exact]; rfl
end YM.CF.Crest.Sleet
