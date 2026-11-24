import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Quilt
import Mathlib.Data.Nat.Log
/-! # Enough copies to eat the volume exponential. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window.SquareScalar
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Lat Cube RP Push.GridApprox Cells
open scoped Classical Topology BigOperators ContDiff InnerProductSpace ComplexOrder ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
variable {P:Patch}{m B:Side}
variable (d:ℕ)(c:RoomCount)(s: Axis)
local notation "Nt" => CSide m B
local notation "N'" => More (CSide m B)
local notation "Γ" => Config SU.group (More (CSide m B))
lemma log_covers (N d:ℕ)(e:0<d)(hw:d≤N):∃ l,d*2^l≤ N ∧ N ≤ 2*d*2^l := by
 let l:=Nat.log 2 (N/d); have hh:0 < N/d:= Nat.div_pos hw e
 refine ⟨l,?_ ,?_⟩
 · rw [mul_comm d]; exact (Nat.le_div_iff_mul_le e).mp (Nat.pow_le_of_le_log hh.ne' le_rfl)
 have hv: N/d < 2^(l+1) := Nat.lt_pow_succ_log_self (by decide) _
 have he:= (Nat.div_lt_iff_lt_mul e).mp hv
 exact he.le.trans_eq (by rw [pow_succ]; ring)
variable (F:Evaluation (CSide m B)→ℂ)(H:FrameBill P m B F)(A : Config SU.group (More (CSide m B))→ℂ){w:ℝ}(hw:boxed P d 0 w A)(hd:2*B.val∣d)
include H hw hd
def mural (d:ℕ)(D:ℝ) := Real.exp ((4*(d:ℝ))^4*|D|)
lemma quiltCharge (hp:0<d)(hl:d ≤ (CSide m B).val) (D:ℝ)
    (e:∀ (X:Config SU.group (More (CSide m B))→ℂ) (v:ℝ), Envelope X → (∀ i, ‖X i‖ ≤ v) → ‖F (bosonic (CSide m B) X)‖ ≤ v * Real.exp (D* ((More (CSide m B)).val:ℝ)^4)) :
    ‖F (bosonic (CSide m B) A)‖ ≤ w*mural d D := by
 obtain ⟨l,Q,r⟩:=log_covers _ d hp hl
 have hl:bedroom l 0=0:= by ext i; simp [bedroom]
 let X:=quilt d A l; let T:=(2^l:ℕ)^4
 have hu:boxed P d (bedroom l 0) w A:= hl ▸ hw; obtain ⟨hv,h⟩:=per_tile d F H A hd l hu Q; have hx:=hv.localB
 have ht:= e X (w^T) ⟨hx.borel,hx.cost⟩ hv.costs; let R:=(CSide m B).val; have hz:0≤w:= (norm_nonneg _).trans (hw.costs 1)
 have hh: (((R*2:ℕ):ℝ))^4 ≤ T*(4*(d:ℝ))^4 := by
    have p : (((R * 2:ℕ):ℝ))^4 ≤ ((((2*d*2^l*2:ℕ):ℝ)))^4 := by gcongr -- needs r
    apply p.trans_eq; unfold T; push_cast; ring
 have hv:R*2=(More (CSide m B)).val:=rfl
 rw [hv] at hh
 refine le_of_pow_le_pow_left₀ (by positivity : (2^l:ℕ)^4 ≠ 0) (by unfold mural; positivity) ((h.trans ht).trans ?_)
 rw [mul_pow,mural, ←Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone
 calc
    _ ≤ |D| * ((T:ℝ)*(4*d)^4) := mul_le_mul (le_abs_self _) hh (by positivity) (abs_nonneg _)
    _ = _ := by unfold T; ring
end YM.CF.Window.SquareScalar
