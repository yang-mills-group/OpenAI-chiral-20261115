import YM.SU5.Intrinsic.Coil.Cork
import Mathlib.Analysis.Normed.Group.Tannery
import YM.CF.Vow.Pear

/-! # actual first term reading of the canopy operator -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Metric Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault Push.AbsoluteSums Push.AbsoluteSums.Trees
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{μ ψ k q H:ℝ} {B:ℕ}

namespace Carbon
lemma tangent {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](u:ℕ→E)(t:Summable (fun i=> ‖u i‖)) :
 HasDerivAt (fun z:ℂ=>∑' j:ℕ,z^(j+1) • u j) (u 0) 0:=by
 let f(i:ℕ)(z:ℂ):= z^i • u i
 have he(i:ℕ):Continuous (f i):=by unfold f; fun_prop
 let h(i:ℕ):ℝ:=‖u i‖
 let S:=ball (0:ℂ) 1
 have ht:ContinuousOn (fun z:ℂ=> ∑' i:ℕ,f i z) S:=continuousOn_tsum (fun i=>(he i).continuousOn) t (fun i j p=>by unfold f; rw [norm_smul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp p).le))
 have hf:∑' i:ℕ,f i 0=u 0:=by unfold f; rw [tsum_eq_single 0, pow_zero,one_smul]; intro b hb; simp [hb]
 let g(z:ℂ):= ∑' i:ℕ,z^(i+1) • u i; have hy(z:ℂ):g z=z • (∑' i,f i z):=by unfold g f; rw [←tsum_const_smul'']; simp_rw [pow_succ',mul_smul]
 apply hasDerivAt_iff_tendsto_slope.mpr
 refine (((ht.continuousAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_ |>.mono_right (?_: 𝓝 (∑' i,f i 0)≤_))
 · filter_upwards [self_mem_nhdsWithin] with z p; have hp:z≠0:=p
   change _=slope g 0 z; rw [slope_def_module,hy, hy, sub_zero,zero_smul,sub_zero]; exact (inv_smul_smul₀ hp _).symm
 rw [hf]

open Push.AbsoluteSums.Gas Push.AbsoluteSums.Ursell
variable {g:Pax n}{G:Aura n → ℝ}
lemma receipt_term (a:ℂ)(i j:ℕ)(X:Aura n) : funge X (a • g) i j=a^(j+1) • funge X g i j:=by
 unfold funge; rw [smul_sum]; refine sum_congr rfl fun l _=>?_; unfold Vow.sta; split; rename_i h
 · unfold guava; simp only [Pi.smul_apply,Fintype.card_option,Fintype.card_fin, ←Finset.smul_prod,Finset.card_univ]; rw [smul_comm (a^(j+1))]
 rw [smul_zero]
variable (P:BudgetPoint)(X:Aura n)(V:Orbit n)
variable (T:Ready stern B G μ ψ k q)(p:0≤μ)(hv:∀ i:Aura n, Medal P i.val ∅ (g i) H (G i))(hW:1≤H)
local notation "∆"=> fun j=>funge X g 0 j V
include T p hv hW
set_option maxHeartbeats 600000 in
private lemma pointer (e:visible P X.val ∅ V.1): Summable (fun j:ℕ=> ‖(∆) j‖):=by
 let f(j:ℕ):= ∑ i:Tuple (Aura n) j, sepV G X 0 ⟨j,i⟩
 obtain ⟨i,b,t⟩:=e
 have he:= (glomM (m:=0) X T p).sigma; apply Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (f:=f) _ (by simpa only [tsum_fintype] using he)
 intro j; unfold funge; rw [Finset.sum_apply]; apply le_trans (norm_sum_le ..); refine sum_le_sum fun l _=>?_ ; have he := ponder X (Sigma.mk j l) hW hv 0; rw [he.same V (i,V.2) t (fun _ _=>rfl)]; exact he.capF hW _ b
lemma token : HasDerivAt (fun a:ℂ=> (FeeD P (a • g)) X V) (zenS P X.val ∅ (g X) V) 0:=by
 unfold zenS; split
 next h=>
    rw [←sheerH X g]; have he:= tangent (fun j=>funge X g 0 j V) (pointer P X V T p hv hW h)
    apply he.congr_of_eventuallyEq; filter_upwards with a; unfold FeeD spinD lasting zenS; rw [if_pos h]; simp_rw [receipt_term]; rfl
 next h=> exact (show HasDerivAt _ _ _ from ((hasDerivAt_const (0:ℂ) (0:Cipher n)).congr_of_eventuallyEq (Eventually.of_forall fun a:ℂ=> if_neg h)))
end Carbon
end YM.CF.Coil
open YM.CF.Coil
#print axioms Carbon.token
