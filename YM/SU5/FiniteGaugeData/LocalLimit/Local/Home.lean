import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Street

/-! # Shift arbitrary centered box into canvas of positive room (no period size used
until consuming `gauge_bill`). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window.SquareScalar
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Lat Cube RP Push.GridApprox Cells
open scoped Classical Topology BigOperators ContDiff InnerProductSpace ComplexOrder ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
variable {N:Side}(B:Side)(P:Patch)(r d:ℕ)
local notation "G" => SU.group
local notation "R₀" => reach P
local notation "Λ" => More N
local notation "Γ" => Config SU.group (More N)
def tickBox (P:Patch)(r:ℕ) : Cover := fun _=>(reach P+r+1:ℕ)
def tile (B:Side)(P:Patch)(r:ℕ) := 2*B.val*(reach P+r+1)*2
lemma tile_dvd : (2*B.val) ∣ tile B P r := ⟨(reach P+r+1)*2,mul_assoc ..⟩
lemma tile_pos : 0 < tile B P r:=by unfold tile; positivity
local notation "s" => (2*B.val) • tickBox P r
lemma displaces : Set.MapsTo (affine 1 (wrap Λ s)) (window (0:Site (More N)) r) (stone P N (tile B P r) 0):=by
 rintro v ⟨x,h,rfl⟩; refine ⟨x+s,?_,by simp [affine]⟩; have hx:=box_test.mp (show x∈box _ from h); intro i
 have he:1 ≤ 2*(B.val:ℤ):=by have h:(0:ℤ)<B.val:= Nat.cast_pos.mpr B.property; linarith
 let v:ℤ:=reach P+r+1; have hv:0 ≤ v:=by unfold v; positivity
 have ht:v ≤ 2*B.val*v:= le_mul_of_one_le_left hv he
 have hi:=hx.1 i; have hu:=hx.2 i
 unfold tile tickBox; rw [Pi.zero_apply,pow_zero,mul_one]; simp only [Pi.add_apply,Pi.smul_apply]; simp only [nsmul_eq_mul]; push_cast; unfold v at *; constructor <;> linarith
lemma back_home (U:Γ) (x:Cover) : pull 1 (wrap Λ x) (pull 1 (wrap _ (-x)) U)= U := by rw [pull_pull]; simp [affine]
lemma canvas (X:Γ→ℂ)(h:Interior (window (0: Site (More N)) r) X)(w:ℝ)(x:∀ i, ‖X i‖≤w):
    boxed P (tile B P r) 0 w (X ∘ pull 1 (wrap (More N) s)):= ⟨h.unchanged _ _ (displaces B P r),fun _i=> x _⟩
end YM.CF.Window.SquareScalar
