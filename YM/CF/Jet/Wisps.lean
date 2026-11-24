import YM.CF.Jet.Trefoil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice Cube Lat
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X]
lemma payment_for (n:ℕ){S:Set E}(h:IsCompact S)(f:E→X)(g:∀ x∈S,ContDiffAt ℝ (↑n:WithTop ℕ∞) f x): ∃ K:ℝ,0≤K ∧ ∀ x∈S, Allows n f x K :=by
 have H (j:ℕ)(hj:j≤n): ContinuousOn (fun x=> iteratedFDeriv ℝ j f x) S := fun i hi=> ((g _ hi).continuousAt_iteratedFDeriv (by exact_mod_cast hj)).continuousWithinAt
 choose B H using fun j:Fin (n+1)=> h.exists_bound_of_continuousOn (H j.val (by have hx:=j.isLt; omega))
 refine ⟨∑ j,|B j|,sum_nonneg (fun _ _=>abs_nonneg _),fun x hx=>⟨g _ hx,fun j hj=>?_⟩⟩
 let i:Fin (n+1):=⟨j,by omega⟩; exact (H i x hx).trans ((le_abs_self _).trans (single_le_sum (f:=fun j=>|B j|) (fun j _=>abs_nonneg _) (mem_univ i)))
lemma compact_allow {K:ℝ}(n:ℕ)(h:0≤K) [FiniteDimensional ℝ E] (f:E→X)(g:ContDiff ℝ (↑n:WithTop ℕ∞) f): ∃ C:ℝ,0≤C∧∀ (x:E), ‖x‖ ≤ K → Allows n f x C :=by -- K not variable
 letI:=FiniteDimensional.proper ℝ E; obtain ⟨B,h,H⟩:=payment_for n (isCompact_closedBall (0:E) K) f (fun x hx=>g.contDiffAt)
 exact ⟨B,h,fun x hx=> H x (by simpa using hx)⟩
lemma Allows.weave {n:ℕ}{f:E→X}{A:X→ℝ}{x:E}{K:ℝ}(h:Allows n A (f x) 0)(g:Allows n f x K): Allows n (A ∘ f) x 0:=by simpa [composeCost,Function.comp_def] using h.comp g

def glue (x:Vect):= expNegInvGlue (‖x‖-broad)
lemma leveled : glue =ᶠ[𝓝 0] fun _=> 0:=by
  filter_upwards [ball_mem_nhds (0:Vect) broad_pos] with y hy; exact expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (le_of_lt (by simpa using hy)))
lemma glu_glob (n:ℕ):ContDiff ℝ (↑n:WithTop ℕ∞) glue:= contDiff_iff_contDiffAt.mpr (fun x=> by
  by_cases p:x=0; rw [p]; exact contDiffAt_const.congr_of_eventuallyEq leveled
  exact (expNegInvGlue.contDiff (n:=n)).contDiffAt.comp x ((contDiffAt_norm ℝ p).sub contDiffAt_const))
lemma inv_glue (n:ℕ){x:ℝ}(h:expNegInvGlue x=0):Allows n expNegInvGlue x 0:=by
 have ht:=expNegInvGlue.contDiff (n:=n); refine ⟨ht.contDiffAt, fun i hi=>?_⟩
 have hc: Set.Iio (0:ℝ)⊆ {t | ‖iteratedFDeriv ℝ i expNegInvGlue t‖ ≤ 0}:=fun z hz=>by
    have he:expNegInvGlue =ᶠ[𝓝 z] fun _=>0 := (show ∀ᶠ v:ℝ in 𝓝 z,v<0 from gt_mem_nhds hz).mono (fun _ g=> expNegInvGlue.zero_of_nonpos g.le)
    exact ((allows_const z (v:=(0:ℝ)) (n:=i) (norm_zero.le)).germ he.symm).norm_le i le_rfl
 have hy := closure_minimal hc (isClosed_le (ContDiff.continuous_iteratedFDeriv (show (↑i:WithTop ℕ∞)≤ (n:ℕ) by exact_mod_cast hi) ht).norm continuous_const)
 exact hy (by rw [closure_Iio]; exact expNegInvGlue.zero_iff_nonpos.mp h)
lemma glu_dead (n:ℕ){x}(h:glue x=0) :Allows n glue x 0:=by
 by_cases t:x=0
 · subst x; exact (allows_const _ (norm_zero.le)).germ leveled.symm
 let f(i:Vect):=‖i‖-broad; have he:ContDiffAt ℝ (↑n:WithTop ℕ∞) f x:= (contDiffAt_norm ℝ t).sub contDiffAt_const
 obtain ⟨C,-,hC⟩:=payment_for n (S:={x}) isCompact_singleton f (fun y hy=> (Set.mem_singleton_iff.mp hy).symm ▸ he)
 exact Allows.weave (inv_glue n h) (hC x (Set.mem_singleton _))
lemma shaved (n:ℕ): ContDiff ℝ (↑n:WithTop ℕ∞) (fun x: Vect×Vect=> shave margin x.1 x.2):=by
 let Y:Vect→ ℝ:= fun x=>‖x‖^2
 have he:ContDiff ℝ (↑n:WithTop ℕ∞) Y:=by
    rw [show Y=(fun x=>inner ℝ x x) from funext fun x=> (real_inner_self_eq_norm_sq _).symm]; exact ContDiff.inner ℝ contDiff_id contDiff_id
 have hg : ContDiff ℝ (↑n:WithTop ℕ∞) (fun y:Vect=> baluster margin ‖y‖):= he.add ((expNegInvGlue.contDiff (n:=n)).comp (f:=fun y=> margin^2-Y y) (contDiff_const.sub he))
 let T(s:Vect×Vect):=baluster margin ‖s.1‖
 have hT:ContDiff ℝ (↑n:WithTop ℕ∞) T:=hg.comp contDiff_fst
 have ht:= (ContDiff.inner ℝ (contDiff_fst (E:=Vect)) contDiff_snd).div hT (fun s=> (baluster_pos margin_pos _).ne') -- context
 exact contDiff_snd.sub (ht.smul contDiff_fst)
end YM.CF.Jet
