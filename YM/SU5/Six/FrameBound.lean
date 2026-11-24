import YM.Hilbert.Kolmogorov
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
noncomputable section
namespace YM.FrameBound
open Function Filter Metric Finset
open scoped Topology BigOperators InnerProductSpace
variable (I:Type)[Fintype I] (H:Hilbert)
def combination (v:I→H) (a:I→ℂ): H:=∑ i,a i • v i
def Coercive (v:I→H) (c:ℝ): Prop:=∀ a:I→ℂ,c*(∑ i,‖a i‖^2) ≤ ‖combination I H v a‖^2
private abbrev ℰ := EuclideanSpace ℂ I
lemma sq_coefficients (v:ℰ I): ‖v‖^2 = ∑ i:I, ‖v i‖^2 := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sq_sqrt ?_
  positivity
lemma extend_bound (v:I→H){δ:ℝ}
    (h:∀ a:ℰ I, ‖a‖=1 → δ ≤ ‖combination I H v a.ofLp‖^2) : Coercive I H v δ:= by
  intro x
  let X:ℰ I := WithLp.toLp 2 x
  by_cases p:X=0
  · have hx:x=0:=congrArg WithLp.ofLp p
    subst x; simp
  let c:ℂ := (‖X‖:ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr p).ne'
  have hv : ‖c‖ = ‖X‖ := by simp [c]
  let Y:= c⁻¹ • X
  have he : ‖Y‖=1 := by rw [norm_smul, norm_inv,hv,inv_mul_cancel₀ (norm_pos_iff.mpr p).ne'] -- unfold
  have w := h Y he
  have hx : x = (c • Y).ofLp := by rw [smul_inv_smul₀ hc]
  have hy : combination I H v x = c • combination I H v Y.ofLp:= by
    unfold combination
    exact (congrArg (fun a:I→ℂ=>∑ i,a i • v i) hx).trans (by simp [smul_sum,mul_smul])
  rw [← show ‖X‖^2=∑ i,‖x i‖^2 from sq_coefficients I X, hy,norm_smul,hv,mul_pow,mul_comm δ]
  gcongr

-- Uniformity of lower bound: not automatic from positive bounds observed
-- in finitely many coordinate directions! Conditional costs here must work for
-- ALL fixed linear combinations; costs can however give different lower bounds.
theorem eventual {v:ℕ→I→H}
    (b:∀ i,∃ c:ℝ,∀ᶠ n:ℕ in atTop, ‖v n i‖≤c)
    (p:∀ a:I→ℂ, a≠0 → ∃ d:ℝ,0<d∧∀ᶠ n:ℕ in atTop, d< ‖combination I H (v n) a‖^2) :
    ∃ δ:ℝ,0<δ ∧ ∀ᶠ n:ℕ in atTop, Coercive I H (v n) δ := by
  by_contra! h
  -- for each m choose a failure at some n≥m
  let d (m:ℕ):ℝ:= ((m:ℝ)+1)⁻¹
  have dp(m:ℕ):0<d m:=by unfold d; positivity
  have he(m:ℕ):∃ n≥m,∃ a:ℰ I, ‖a‖=1∧‖combination I H (v n) a.ofLp‖^2<d m:=by
    obtain ⟨n,t,u⟩:= ((h (d m) (dp m)).and_eventually (eventually_ge_atTop m)).exists
    refine ⟨n,u,?_⟩
    by_contra! f
    exact t (extend_bound I H (v n) f)
  choose n w a t e using he
  have hn:Tendsto n atTop atTop := tendsto_atTop_mono w tendsto_id -- tune
  obtain ⟨A,m,f,u,hf⟩:= (isCompact_sphere (0:ℰ I) 1).tendsto_subseq (x:=a) (fun n=>by simpa using t n)
  have hne: A.ofLp ≠ 0:=by intro hz; have : A=0:=congrArg (WithLp.toLp 2) hz; simp [this] at m
  let y:= n ∘ f
  have hy:Tendsto y atTop atTop:= hn.comp u.tendsto_atTop
  obtain ⟨D,hD,qD⟩:= p A.ofLp hne
  let W(k):=combination I H (v (y k)) A.ofLp
  let U(k):=combination I H (v (y k)) (a (f k)).ofLp
  have hd:Tendsto d atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add tendsto_const_nhds)
  have hu:Tendsto U atTop (𝓝 0):=by
    have he:Tendsto (fun k=> ‖U k‖^2) atTop (𝓝 0):= squeeze_zero (fun _=>sq_nonneg _) (fun k=> (e (f k)).le) (hd.comp u.tendsto_atTop)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp he
    rw [Real.sqrt_zero] at ht; exact ht.congr fun i=> Real.sqrt_sq (norm_nonneg _)
  have hk:Tendsto (fun k=>W k-U k) atTop (𝓝 0):=by
    let g(i:I)(k:ℕ):= A i-a (f k) i
    let L(i:I)(k:ℕ):= (g i k) • v (y k) i
    have hl(i:I):Tendsto (g i) atTop (𝓝 0):= by simpa using ((tendsto_const_nhds (x:=A i)).sub (((PiLp.continuous_apply 2 _ i).tendsto A).comp hf)) -- tune
    have hb(i:I): Tendsto (L i) atTop (𝓝 0):= by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      obtain ⟨c,hc⟩ := b i
      have hi:= (tendsto_zero_iff_norm_tendsto_zero.mp (hl i)).mul_const c
      rw [zero_mul] at hi
      apply squeeze_zero' (Eventually.of_forall fun k=> norm_nonneg _) _ hi
      filter_upwards [hy.eventually hc] with k h
      exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
    have hsum:Tendsto (fun k=>∑ i:I,L i k) atTop (𝓝 (∑ _:I,(0:H))) := tendsto_finsetSum _ fun i _=> hb i
    rw [sum_const_zero] at hsum
    exact hsum.congr fun k=> by simp only [L,g,sub_smul,W,U,combination,sum_sub_distrib]
  have hW:Tendsto W atTop (𝓝 0) := by
    have hb:=hk.add hu
    rw [zero_add] at hb; exact hb.congr fun i=> sub_add_cancel ..
  obtain ⟨i,h',H'⟩ := ((hy.eventually qD).and ((hW.norm.pow 2).eventually (gt_mem_nhds (show ‖(0:H)‖^2<D from by simpa using hD)))).exists
  exact lt_asymm h' H'
end YM.FrameBound
