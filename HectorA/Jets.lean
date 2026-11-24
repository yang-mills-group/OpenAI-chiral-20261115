import Mathlib
set_option autoImplicit false
noncomputable section
namespace Yoland
open Filter Function Finset
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace Classical
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]
variable {f:ℝ→X}{x:ℝ}{Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]
lemma garage (h:AnalyticAt ℝ f x)(g:∀n:ℕ,iteratedDeriv n f x=(0:X)): f =ᶠ[𝓝 x] 0:=by
 obtain ⟨p,r,hp⟩:=h
 filter_upwards [hp.eventually_hasSum_sub] with z ht
 have he(n:ℕ):p n (fun _=>z-x)=0:=by
    have hy:=hp.factorial_smul (z-x) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,g,smul_zero] at hy
    have hZ:= hy -- factorial • nsmul
    let v:= p n (fun _=>z-x); rw [← Nat.cast_smul_eq_nsmul ℝ] at hZ
    have ht1:(n.factorial:ℝ)≠0:=by exact_mod_cast n.factorial_ne_zero
    calc _ = ((n.factorial:ℝ)⁻¹*(n.factorial:ℝ)) • v:=by rw [inv_mul_cancel₀ ht1,one_smul]
         _ = 0 := by rw [mul_smul]; unfold v; rw [hZ,smul_zero]
 simp_rw [he] at ht; exact ht.unique hasSum_zero
lemma transport (h:AnalyticAt ℝ f x)(L:X→L[ℝ]Y)(n:ℕ): iteratedDeriv n (L ∘ f) x=L (iteratedDeriv n f x):=by
 unfold iteratedDeriv; rw [L.iteratedFDeriv_comp_left (n:=(n:WithTop ℕ∞)) h.contDiffAt le_rfl]; rfl
variable (hf:AnalyticOnNhd ℝ f (Set.Ioi 0))
include hf
lemma aoe(n:ℕ){x:ℝ}(p:0<x):AnalyticAt ℝ (iteratedDeriv n f) x:=by
 induction n generalizing x with
 | zero => simp only [iteratedDeriv_zero]; exact hf x p
 | succ n ih=>rw [iteratedDeriv_succ]; exact (ih p).deriv -- tune
#check ContinuousLinearMap.iteratedFDeriv_comp_left
#check AnalyticAt.contDiffAt
#check aoe
end Yoland
