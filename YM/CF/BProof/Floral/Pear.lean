import YM.CF.BProof.Floral.Hol
import YM.CF.Jet.Stokes
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology NNReal ENNReal ContDiff
namespace YM.CF.Floral
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {D:Set ℂ}{B:Set E}
variable (F:ℂ→ E→ℂ) {k j:ℕ} {C:ℝ}
lemma hol_iterated (d:IsOpen D)(b:IsOpen B)(H:∀ x∈B,Hol D (fun z=> F z x))
    (h: ∀ x∈B,∀ z∈D, Jet.Allows k (F z) x C) (p:j≤k)(x:E)(g:x∈B)(v:Fin j→E): Hol D fun z=>iteratedFDeriv ℝ j (F z) x v:=by
 induction j generalizing x with
 | zero=> simpa [iteratedFDeriv_zero_apply] using H x g
 | succ j ih=>
    let A (t:ℝ):= x+t • v 0; have ha:A 0=x:=by simp [A]
    let G(z:ℂ)(t:ℝ):= iteratedFDeriv ℝ j (F z) (A t) (Fin.tail v)
    have he(t)(l:A t∈B):Hol D (fun z=>G z t):=ih (by omega) _ l _
    have ht(z)(l:z∈D)(t)(q:A t∈B):HasDerivAt (G z) (iteratedFDeriv ℝ (j+1) (F z) (A t) v) t:=by
       rw [iteratedFDeriv_succ_apply_left]
       exact (ContinuousMultilinearMap.apply ℝ _ ℂ (Fin.tail v)).hasFDerivAt.comp_hasDerivAt t (((h _ q z l).smooth.differentiableAt_iteratedFDeriv (m:=j) (by exact_mod_cast show j < k by omega)).hasFDerivAt.comp_hasDerivAt t (show HasDerivAt A (v 0) t from by simpa [A] using ((hasDerivAt_id' t).smul_const (v 0)).const_add x))
    let l:=𝓝[≠] (0:ℝ)
    let W t z:=slope (G z) 0 t; let c:=C*∏ i, ‖v i‖; let S:=A ⁻¹' B
    have h0:A 0∈B:=ha ▸ g
    obtain ⟨r,hr,Hb⟩:= Metric.mem_nhds_iff.mp ((b.preimage (show Continuous A by unfold A; fun_prop)).mem_nhds (show (0:ℝ) ∈ S from h0))
    have hx:ball (0:ℝ) r ∈ l:= mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℝ) hr)
    refine chalk (C:=c) (F:=W) (l:=l) d ?_ ?_ ?_
    · filter_upwards [hx] with t g
      exact ((he t (Hb g)).sub (he 0 h0)).const_smul ((t-0)⁻¹)
    · filter_upwards [hx,self_mem_nhdsWithin] with t m hp z hv
      have hK:∀ y∈ball (0:ℝ) r, ‖iteratedFDeriv ℝ (j+1) (F z) (A y) v‖≤c:=fun y hy=> le_trans (ContinuousMultilinearMap.le_opNorm ..) (mul_le_mul_of_nonneg_right ((h _ (Hb hy) z hv).norm_le (j+1) p) (Finset.prod_nonneg fun i _=> norm_nonneg _)) -- bill?
      have hu:0<‖t‖:= norm_pos_iff.mpr hp
      have hy:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun y hy=>(ht z hv y (Hb hy)).hasDerivWithinAt) hK (convex_ball (0:ℝ) r) (mem_ball_self hr) m
      change ‖(t-0)⁻¹ • (G z t-G z 0)‖ ≤ _; rw [norm_smul,sub_zero,norm_inv,inv_mul_le_iff₀ hu,mul_comm]; rwa [sub_zero] at hy
    · intro z hv; simpa only [ha,W] using (ht z hv 0 h0).tendsto_slope -- rw let depend warning
end YM.CF.Floral
