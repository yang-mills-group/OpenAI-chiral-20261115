import YM.OS.Core
set_option autoImplicit false
noncomputable section
open Function Filter Set
open scoped Topology InnerProductSpace NNReal ComplexConjugate
namespace YM.OS.Semigroup
variable {X:Hilbert}{i:Axis}(S:Semigroup X i)
private lemma tendhalves (t:ℝ≥0): Tendsto (fun n:ℕ=>t * ((2:ℝ≥0)⁻¹)^n) atTop (𝓝 0):= by
 have g:=tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(2:ℝ≥0)⁻¹) (zero_le) (by norm_num)
 simpa using g.const_mul t
/-- symmetric heat does not kill positive time. -/
theorem heat_alive(t:ℝ≥0): Injective (S.E t):= by
 intro v w h; let x:X:=v-w
 have e:S.E t x=0:= sub_eq_zero.mpr h ▸ (S.E t).map_sub v w -- check
 have p(q:ℝ≥0) (u:S.E q x=0): S.E (q/2) x=0:=by
   have ht:=S.swing (q/2) x (S.E (q/2) x)
   rw [←ContinuousLinearMap.comp_apply,←S.time,add_halves q,u,inner_zero_right] at ht
   exact inner_self_eq_zero.mp ht
 let y(n:ℕ):ℝ≥0:= t*((2:ℝ≥0)⁻¹)^n
 have H(n:ℕ): S.E (y n) x=0:= by
   induction n with
   | zero=>simpa [y] using e
   | succ n hn=> simpa only [y,pow_succ,← mul_assoc,div_eq_mul_inv] using p (y n) hn
 have hy := ((S.continuousE x).tendsto 0).comp (tendhalves t)
 have h0:Tendsto (fun n=> S.E (y n) x) atTop (𝓝 0):= by simpa only [H] using (tendsto_const_nhds (x:=(0:X.space)) (f:=atTop (α:=ℕ)))
 have g: S.E 0 x=0:=tendsto_nhds_unique hy h0
 exact sub_eq_zero.mp (show x=0 by simpa [S.eZero] using g)
end YM.OS.Semigroup
namespace YM
namespace Preen
open Analysis -- Hilbert
variable {X:Hilbert} (k:X) (v:‖k‖=1)
def paster:X.space→L[ℂ] X.space:=(Submodule.span ℂ ({k}:Set X.space))ᗮ.starProjection
#check Submodule.starProjection_orthogonal
#check Submodule.starProjection_orthogonal_val
include v
theorem pasted (x:X) : paster k x=x-inner ℂ k x • k:=by
 unfold paster; rw [Submodule.starProjection_orthogonal,ContinuousLinearMap.sub_apply,Submodule.starProjection_singleton (𝕜:=ℂ)] -- check
 simp [v]
omit v in
theorem pasted_cost:‖paster k‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> by rw [one_mul]; exact Submodule.norm_starProjection_apply_le _ _)
theorem together (x y:X): inner ℂ (paster k x) (paster k y)=inner ℂ x y- (star (inner ℂ k x))*inner ℂ k y:=by
 have he:inner ℂ k k=1:=by rw [inner_self_eq_norm_sq_to_K,v]; norm_num
 rw [pasted k v,pasted k v,inner_sub_right,inner_sub_left,inner_sub_left]
 rw [inner_smul_right,inner_smul_left,inner_smul_right,inner_smul_left, he, ← inner_conj_symm (𝕜:=ℂ) x k]
 change _=inner ℂ x y - (starRingEnd ℂ) (inner ℂ k x) * inner ℂ k y
 ring
variable {j:Axis}(S:OS.Semigroup X j)(p:∀ t:ℝ≥0,S.E t k=k)
include p
theorem keep_heat (t:ℝ≥0)(x:X):S.E t (paster k x)=paster k (S.E t x):=by
 rw [pasted k v,pasted k v,map_sub,map_smul,p,← OS.Semigroup.swing S, p]
end Preen
end YM
