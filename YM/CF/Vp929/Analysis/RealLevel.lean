import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Points on the real stencil avoiding all exceptional germ tests (finitely many tests at a time). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Complex Set Function Filter Topology Metric MeasureTheory
section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {V:Set ℂ} {x:ℝ} {z:ℂ}
private lemma coming (x:ℝ) : Tendsto ((↑):ℝ→ℂ) (𝓝[≠] x) (𝓝[≠] (x:ℂ)):= tendsto_nhdsWithin_iff.mpr ⟨continuous_ofReal.continuousAt.continuousWithinAt,(show ∀ᶠ (y:ℝ) in 𝓝[≠] x,(y:ℂ)∈ { (x:ℂ)}ᶜ from (show ∀ᶠ (y:ℝ) in 𝓝[≠] x,y≠x from self_mem_nhdsWithin).mono (fun y p=> mt ofReal_inj.mp p))⟩
lemma eq_realOn {f g:ℂ→ E} (v:IsPreconnected V)(p:IsOpen V)(w:(x:ℂ)∈V) (hf:DifferentiableOn ℂ f V) (hg:DifferentiableOn ℂ g V)(H: ∃ᶠ (y:ℝ) in 𝓝[≠] x,f y=g y) : EqOn f g V:= by
 refine (hf.analyticOnNhd p).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd p) v w ?_
 intro h; exact H ((coming x).eventually h)
theorem axis_eq {f g:ℂ→ E} (h:Differentiable ℂ f) (q:Differentiable ℂ g)(p: ∀ᶠ (y:ℝ) in 𝓝 x, f y=g y):f=g:= funext fun y=> eq_realOn isPreconnected_univ isOpen_univ (mem_univ _) h.differentiableOn q.differentiableOn (Eventually.frequently (p.filter_mono (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds))) (mem_univ y)
lemma axis_basis {f:ℂ→E} (h:Differentiable ℂ f)(p:f z ≠0):∀ᵐ t:ℝ,f t ≠0:=by
 have H :{t:ℝ|f t ≠0}∈ codiscreteWithin univ:= mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr (by
   intro x hx; simp only [compl_univ, union_empty]; by_contra h'; have P: ∃ᶠ (t:ℝ) in 𝓝[≠] x, f t=0:= h'
   exact p (eq_realOn isPreconnected_univ isOpen_univ (mem_univ _) h.differentiableOn (differentiableOn_const _) P (mem_univ _)))
 exact (by simpa using (  ae_restrict_le_codiscreteWithin (μ:=(volume:Measure ℝ)) MeasurableSet.univ) : ae (volume:Measure ℝ)≤codiscreteWithin univ) H
lemma plentiful [TopologicalSpace F] [FirstCountableTopology F] {f:ℂ→F→E}(h:∀ u:F, Differentiable ℂ fun z=>f z u){x:F}(hx:x∈ tsupport (f z)) : ∀ᵐ k:ℝ,x∈ tsupport (f k):= by
 obtain ⟨b,hb,H⟩:= (mem_closure_iff_seq_limit).mp hx; filter_upwards [ae_all_iff.mpr (fun i:ℕ=> axis_basis (h (b i)) (hb i))] with x hx
 exact mem_closure_of_tendsto H (Eventually.of_forall hx)
variable {s:Set ℝ}
theorem strong_axis [MeasurableSpace F] {f: F→ℂ→E} (h:∀ i,Differentiable ℂ (f i)) (v: IsOpen s) (p:s.Nonempty) (m:∀ t∈s, StronglyMeasurable (fun i=> f i (t:ℂ))): StronglyMeasurable (fun i=> f i z) := by
 classical
 obtain ⟨c,hc⟩:=p
 have H(p:ℕ):∀ t:ℝ,t∈s→ StronglyMeasurable (fun i=> iteratedDeriv p (f i) (t:ℂ)):=by
    induction p with
    | zero=> simpa using m
    | succ p ih=>
       intro t ht; let g(p:ℕ)(t:ℝ)(i:F):= iteratedDeriv p (f i) (t:ℂ); let A(x:ℝ)(i:F):= if x∈s then (((x:ℂ)-t)⁻¹ • (g p x i-g p t i)) else 0
       apply stronglyMeasurable_of_tendsto (𝓝[≠] t) (f:=A)
       · intro x; unfold A; split
         next h=>exact ((ih x h).sub (ih t ht)).const_smul _
         next _ => exact stronglyMeasurable_const
       refine tendsto_pi_nhds.mpr fun i=>?_ ; have I: Differentiable ℂ (iteratedDeriv p (f i)):= ((h i).contDiff).differentiable_iteratedDeriv' _
       rw [iteratedDeriv_succ]; apply Tendsto.congr' _ ((I _).hasDerivAt.tendsto_slope.comp (coming t)); filter_upwards [eventually_nhdsWithin_of_eventually_nhds (v.mem_nhds ht)] with y hy; unfold A; rw [if_pos (show y∈s from hy)]; rfl
 let U(n:ℕ)(i:F):=(n.factorial:ℂ)⁻¹ • (z-(c:ℂ))^n • iteratedDeriv n (f i) (c:ℂ)
 exact stronglyMeasurable_of_tendsto (atTop (α:=ℕ)) (f:=fun n i=>∑ j∈Finset.range n,U j i) (fun n=> Finset.stronglyMeasurable_fun_sum _ fun j _=> ((H j c hc).const_smul _).const_smul _) (tendsto_pi_nhds.mpr fun i=>(Complex.hasSum_taylorSeries_of_entire (h i) (c:= (c:ℂ)) (z:=z)).tendsto_sum_nat)
end
end YM.CF.VolumeRate
