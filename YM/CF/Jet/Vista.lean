import YM.CF.Jet.Taste
import YM.CF.Jet.Stokes

set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Set MeasureTheory Function Metric Filter Drapes YM.PolyDisc
open scoped Topology Matrix MatrixOrder BigOperators ContDiff NNReal
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]{S:Set E}
def equalizer (f:S→ℂ) (x:E):= @dite _ (x∈S) (Classical.propDecidable _) (fun h=> f ⟨x,h⟩) (fun _=>0)
lemma interiorC {f:S→ℂ}(h:Looks S f)(ht:Continuous f)(x:E)(v:S∈𝓝 x):AnalyticAt ℂ (equalizer f) x:=by
 classical
 let a:=Module.finBasis ℂ E; let P:=a.equivFun.toContinuousLinearEquiv; let N:= Fin (Module.finrank ℂ E); let W:=Plain N
 let F:Plain N→ℂ:= equalizer f ∘ P.symm
 let z:= P x
 let T:=interior S; have he:x∈T:= mem_interior_iff_mem_nhds.mpr v
 let U:= P.symm ⁻¹' T; have hu:IsOpen U:=isOpen_interior.preimage P.symm.continuous
 have hp:z∈ U:=by show P.symm _∈ T; simpa [z]
 obtain ⟨r,hR,R⟩:= Metric.mem_nhds_iff.mp (hu.mem_nhds hp); have hb:0<r/2:=half_pos hR
 suffices hm:AnalyticAt ℂ F z by
   have ht :AnalyticAt ℂ (F ∘ P) x:= hm.comp (P.analyticAt ..)
   simpa [F,z, Function.comp_def] using ht
 apply Taste.hol (R:=r/2); have hi {y:W} (g:Accept z (r/2) y): y∈U:= R (show dist y z<r from lt_of_le_of_lt ((dist_pi_le_iff hb.le).mpr g) (half_lt_self hR))
 constructor; exact hb
 · have hg: ContinuousOn (equalizer f) S:= by rw [continuousOn_iff_continuous_restrict]; exact ht.congr (fun x=> (by change f x=equalizer f x.val; exact Eq.symm (by unfold equalizer; rw [dif_pos x.property])))
   exact fun y g=> (hg.continuousAt (mem_interior_iff_mem_nhds.mp (show P.symm y∈T from hi g))).comp P.symm.continuousAt
 intro y g i
 let A (t:ℂ):=update y i t; have hc:Differentiable ℂ A:= differentiable_pi.mpr (fun k=>by by_cases G:k=i <;> simp [A,G,differentiable_fun_id,differentiable_const])
 let Y:= P.symm ∘ A
 have hY : Differentiable ℂ Y:= P.symm.differentiable.comp hc
 let V:= A ⁻¹' U; have hV: IsOpen V:=hu.preimage hc.continuous
 let k:=y i; have hh:k∈V:=by show A _∈ U; rw [show A k=y from Function.update_eq_self _ _]; exact hi g
 let B(t:ℂ) : S:= if ht:t∈ V then ⟨Y t, interior_subset ht⟩ else ⟨x,interior_subset he⟩
 have hf {t:ℂ}(p:t∈V): (B t).val=Y t:= by unfold B; rw [dif_pos p]
 have hF := (h V hV B (hY.differentiableOn.congr (fun t t' => hf t'))).differentiableAt (hV.mem_nhds hh)
 apply hF.congr_of_eventuallyEq
 filter_upwards [hV.mem_nhds hh] with t l
 change equalizer f (Y t)=f (B t); rw [← hf l]; exact dif_pos (B t).property
end
lemma fderiv_edge {E Y : Type} [NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup Y][NormedSpace ℂ Y]
    {x y:E}{R B:ℝ}{f:E→Y}(hR:0<R)(hy:y∈ball x (R/2))(h:∀ z∈ball x R,DifferentiableAt ℂ f z)(H:∀ z∈ball x R,‖f z‖≤B): ‖fderiv ℂ f y‖ ≤ B/(R/2) :=by
 have hb:0<R/2:=half_pos hR; have hB:= (norm_nonneg _).trans (H x (mem_ball_self hR))
 apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity); intro v hv
 let g (t:ℂ):=y+t • v; have hg:Differentiable ℂ g:=by unfold g; fun_prop
 have he:g 0=y:=by simp [g]
 have hd : HasDerivAt g v 0:=by simpa [g] using! (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add y)
 have hk(t) (e:t∈closedBall (0:ℂ) (R/2)):g t∈ball x R:=by
   refine lt_of_le_of_lt (dist_triangle (g t) y x) ?_
   rw [dist_eq_norm (g t), show g t-y=t • v by simp [g], norm_smul,hv,mul_one]
   rw [mem_closedBall,dist_zero_right] at e; rw [mem_ball] at hy; linarith
 have hc:=(h (g 0) (hk _ (mem_closedBall_self hb.le))).hasFDerivAt.comp_hasDerivAt 0 hd; rw [he] at hc
 rw [← hc.deriv]
 apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hb _ (fun t e=> H (g t) (hk _ (sphere_subset_closedBall e)))
 have ht:DifferentiableOn ℂ (f ∘ g) (closedBall 0 (R/2)):= fun t e=> ((h _ (hk t e)).comp t (hg _)).differentiableWithinAt
 exact ⟨ht.mono ball_subset_closedBall, ht.continuousOn.mono closure_ball_subset_closedBall⟩
lemma bound_in {E F:Type}[NormedAddCommGroup E][NormedSpace ℂ E]
   [NormedAddCommGroup F][NormedSpace ℂ F] (k:ℕ){f:E→F}{x:E}{R M:ℝ}(ht:∀ y∈ball x R, ContDiffAt ℂ ω f y)(hR:0<R)(h:∀ y∈ball x R,‖f y‖ ≤ M):‖iteratedFDeriv ℂ k f x‖ ≤ Push.Uniform.cauchyCost k R M :=by
  induction k generalizing F R M with
  | zero=> rw [norm_iteratedFDeriv_zero]; exact h _ (mem_ball_self hR)
  | succ k ih=>
    have hr : ball x (R/2)⊆ball x R:= ball_subset_ball (half_lt_self hR).le
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.norm_map,Push.Uniform.cauchyCost]; apply ih
    · intro y hy; exact (ht y (hr hy)).fderiv_right (by simp)
    · positivity
    intro y hy; exact fderiv_edge hR hy (fun y hh=> (ht y hh).differentiableAt (by simp)) h
lemma allows_looks {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E][FiniteDimensional ℂ E] {S:Set E}{f:S→ℂ}(p:Looks S f)(h:Continuous f){x:E}{K r:ℝ}(g:ball x r⊆ S)(hr:0<r)(k:ℕ)(hq:∀ i,‖f i‖≤ K): Allows k (equalizer f) x (K*((1+(2:ℝ)^k/r)^k)) :=by
 have ht y (hg:y∈ ball x r):ContDiffAt ℂ ω (equalizer f) y:=(interiorC p h y (mem_of_superset (isOpen_ball.mem_nhds hg) g)).contDiffAt
 have hx:= ht x (mem_ball_self hr); have hm :0 ≤ K:=(norm_nonneg _).trans (hq ⟨x,g (mem_ball_self hr)⟩)
 refine ⟨(hx.of_le le_top).restrict_scalars ℝ,fun i hi=>?_⟩
 rw [← ((hx.of_le (m:=(i:WithTop ℕ∞)) le_top)).restrictScalars_iteratedFDeriv, Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
 apply le_trans ((bound_in i ht hr (fun y e=> by rw [show equalizer f y=f ⟨_,g e⟩ from dif_pos _]; exact hq _)).trans (Push.Uniform.cauchyCost_le _ hm hr)); apply mul_le_mul_of_nonneg_left _ hm
 apply le_trans ?_ (pow_le_pow_right₀ (show (1:ℝ)≤1+2^k/r from le_add_of_nonneg_right (by positivity)) hi); gcongr
 apply le_trans ?_ (show (2:ℝ)^k/r≤1+(2:ℝ)^k/r from le_add_of_nonneg_left zero_le_one); gcongr; norm_num
end YM.CF.Jet
