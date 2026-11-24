import YM.SU5.Reconstruction.Anvil.Display
import YM.SU5.Reconstruction.Trap.Lantern
/-! SOT quantitative receipt even without nontriviality inputs on H. -/
set_option autoImplicit false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric OS Semigroup Picket
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "Z"=>polarize S
lemma sunny_bound (x:Meter)(t:ℝ)(A:H.Op) : ‖sunny S x t A‖=‖A‖:=by
 have h(x:Meter)(t:ℝ):Z x t∈ unitary H.Op:=(physical_shifts S x t).symm ▸ ((mobile S _).units)
 calc _ = _ := CStarRing.norm_mul_coe_unitary (Z x t*A) (⟨Z (-x) (-t),h _ _⟩ : unitary H.Op) -- tune order
      _ = _ := CStarRing.norm_coe_unitary_mul (⟨Z x t,h _ _⟩ : unitary H.Op) A
lemma sunny_pay {r:ℝ}{A:H.Op}(p:‖A+1‖≤r)(x:Meter)(t:ℝ):‖sunny S x t A +1‖≤r:=by
 rw [show sunny S x t A+1=sunny S x t (A+1) from ?_, sunny_bound S]; exact p
 unfold sunny; rw [mul_add,add_mul,mul_one,spin_add,add_neg_cancel,add_neg_cancel,spin_zero]
lemma sunshine_pair {A B:H.Op}(x y:Meter)(e f:ℝ)(p:‖A+1‖≤1/64)(h:‖B+1‖ ≤1/64): ‖sunny S x e A * sunny S y f B-1‖ ≤ 1/16:= by
 let A':=sunny S x e A; let B':=sunny S y f B; let C:=A'+1; let D:=B'+1
 have hc:‖C‖ ≤ 1/64:=sunny_pay S p x e; have hd:‖D‖ ≤1/64:=sunny_pay S h y f
 change ‖A'*B'-1‖≤ _; rw [show A'*B'-1=C*D - C-D from by unfold C D; noncomm_ring]
 exact (le_trans ((norm_sub_le ..).trans (add_le_add_left (norm_sub_le ..) _)) ((add_le_add (add_le_add ((norm_mul_le ..).trans (mul_le_mul hc hd (norm_nonneg _) (by norm_num))) hc) hd).trans (by norm_num)))
lemma telegraph (A:H.Op)(x:H)(u:‖x‖=1)(v:‖A-1‖ ≤1/16): 1-1/16 ≤ ‖inner ℂ x (A x)‖ := by
 have he:= ((A-1).le_opNorm x).trans (mul_le_mul_of_nonneg_right v (norm_nonneg _)); rw [u,mul_one] at he
 have hx: ‖1-inner ℂ x (A x)‖≤1/16:=by
    have hg:= norm_inner_le_norm (𝕜:=ℂ) x ((A-1) x); rw [u,one_mul] at hg
    rw [norm_sub_rev,←show inner ℂ x x=1 from (by rw [inner_self_eq_norm_sq_to_K,u]; simp),← inner_sub_right]; exact hg.trans he
 have h:(1:ℝ) ≤ ‖1-inner ℂ x (A x)‖+‖inner ℂ x (A x)‖:=by simpa only [norm_one] using norm_le_norm_sub_add (1:ℂ) (inner ℂ x (A x))
 linarith
end YM.Anvil
#print axioms YM.Anvil.sunshine_pair
