import Mathlib.Analysis.Calculus.LHopital
import Zephyr.Chern.Bud
set_option autoImplicit false
noncomputable section
namespace YM.CF.Bay.D
open Function Filter Topology Zephyr.Chern

variable {f:ℝ→ℂ}

lemma dew_of_bud (p:Bud f)(χ:ℂ→L[ℝ]ℝ){c:ℝ}
    (h:Tendsto (fun t:ℝ=>χ (f t-f 0) / t^2) (𝓝[>] 0) (𝓝 c)):
    χ (deriv f 0)=0 ∧ χ (bud f 2)=c:=by
 have ht:Tendsto (fun t:ℝ=>χ (f t-f 0)/t) (𝓝[>] 0) (𝓝 0):=by
    have he:=h.mul (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x:=𝓝 (0:ℝ))))
    rw[mul_zero] at he
    refine he.congr' (Eventually.of_forall fun t=>?_)
    by_cases hp:t=0
    · simp[hp]
    dsimp; field_simp
 let F(t):=χ (f t-f 0)
 have dF(t)(u:DifferentiableAt ℝ f t): HasDerivAt F (χ (deriv f t)) t:=
   χ.hasFDerivAt.comp_hasDerivAt t (u.hasDerivAt.sub_const _)

 have h₀:= hasDerivAt_iff_tendsto_slope_zero.mp (dF 0 p.ha)
 have eh : χ (deriv f 0)=0:=tendsto_nhds_unique (h₀.mono_left (nhdsGT_le_nhdsNE _))
    (by simpa [F,div_eq_mul_inv,mul_comm] using ht)
 refine ⟨eh,?_⟩
 let S:= 𝓝[>] (0:ℝ); let c':=χ (deriv (deriv f) 0)
 have e := (hasDerivAt_iff_tendsto_slope_zero.mp (χ.hasFDerivAt.comp_hasDerivAt 0 p.2.hasDerivAt)).mono_left (nhdsGT_le_nhdsNE _)
 have he:Tendsto (fun t:ℝ=> χ (deriv f t)/(2*t)) S (𝓝 (χ (bud f 2))):=by
    have hu:Tendsto _ _ (𝓝 ((2⁻¹:ℝ) • c')):=e.const_smul (2⁻¹:ℝ)
    have ee:(2⁻¹:ℝ) • c'=χ (bud f 2):=by
       unfold c'
       rw[show ((2⁻¹:ℝ) • χ (deriv (deriv f) 0))= (2⁻¹:ℝ) • χ (deriv (deriv f) 0) by simp, ←map_smul]
       congr 1; simp[Complex.real_smul,bud,div_eq_mul_inv,mul_comm]
    rw[ee] at hu
    refine hu.congr (fun t=>?_)
    simp only[Function.comp_apply,eh, sub_zero,smul_eq_mul,zero_add]
    rw[div_eq_mul_inv,mul_inv]; ring
 have hj:Tendsto (fun t:ℝ=>F t/t^2) S (𝓝 (χ (bud f 2))):=by

    refine HasDerivAt.lhopital_zero_nhdsGT (f':=χ∘(deriv f)) ((eventually_nhdsWithin_of_eventually_nhds p.1).mono (fun t=>dF t))
      (g':=(fun t:ℝ=>2*t)) (Eventually.of_forall fun t=>by simp_rw [sq,two_mul]; exact (by simpa only[mul_one,one_mul] using! (hasDerivAt_id' t).mul (hasDerivAt_id' t)))
      ?_ ?_ ?_ he
    · filter_upwards [self_mem_nhdsWithin] with t ht; exact mul_ne_zero two_ne_zero (show (0:ℝ)<t from ht).ne'
    · have :=tendsto_nhdsWithin_of_tendsto_nhds (s:=Set.Ioi (0:ℝ)) (dF 0 p.ha).continuousAt.tendsto;simpa[F] using this
    · exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (tendsto_id (x:=𝓝 (0:ℝ))).pow 2)
 exact tendsto_nhds_unique hj h

lemma bingo (p:Bud f){c:ℂ}
   (h:Tendsto (fun t:ℝ=>t⁻¹^2 • (f t-f 0)) (𝓝[>] 0) (𝓝 c)):
   bud f 1=0∧ bud f 2=c:=by
 have t(χ:ℂ→L[ℝ]ℝ): χ (deriv f 0)=0 ∧ χ (bud f 2)=χ c:=dew_of_bud p χ (by
    have hz:= (χ.continuous.tendsto c).comp h
    simpa only [Function.comp_def,inv_pow, map_smul, smul_eq_mul, div_eq_inv_mul] using hz)
 obtain ⟨u,o⟩:=t Complex.reCLM; obtain ⟨v,w⟩:=t Complex.imCLM
 exact ⟨Complex.ext u v,Complex.ext o w⟩

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.bingo
