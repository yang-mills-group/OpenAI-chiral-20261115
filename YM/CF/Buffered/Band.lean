import YM.CF.Buffered.Reflection

/-!
# The buffered finite-period band

Distance at least `w` to the nth (**gauge**) lattice's specified plane at
integer `s`, and also at least `w` to its opposite. Supports in this project
track both endpoints, matter support by `modesIn`. All transverse coordinates
may be used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP RG Scroll Spire Push.SectorMeasure Nacre Window Tulip Skye
attribute [local instance] opCStarAlgebra

variable {n : Side}
def band (n : Side) (i : Axis) (s : ℤ) (w : ℕ) : Support (More n) :=
  univ.filter (fun x => w ≤ (x i - (s:Per (More n))).val ∧ (x i - (s:Per (More n))).val + w ≤ n.val)
variable (i : Axis) (s : ℤ)
lemma band_spec (w : ℕ) (x : Seat n) : x∈band n i s w ↔
    w ≤ (x i - (s:Per (More n))).val ∧ (x i - (s:Per (More n))).val+w ≤ n.val := by
  simp only [Buffered.band, mem_filter, mem_univ, true_and]
lemma band_anti {u v : ℕ} (h : u ≤ v) : band n i s v ⊆ band n i s u := fun _ p =>
  (band_spec i s u _).mpr ⟨h.trans ((band_spec ..).1 p).1, (Nat.add_le_add_left h _).trans ((band_spec ..).1 p).2⟩
lemma band_zero (n : Side) : band n i 0 0 = RP.north n i := by ext x; simp [band_spec,nextPlane]
lemma band_shift_point (n : Side) (z : ℤ) (x : Seat n) :
    (lagX (z • step i)).anon n x i = x i + (↑(2*z) : Per (More n)) := by
  simp [Shape.anon,affine,lagX,wrap_here, two_smul,two_mul]
lemma band_shift_back (n : Side) (z : ℤ) (x : Seat n) :
    (lagX (z • step i)).anon n ((lagX ((-z) • step i)).anon n x)=x := by
  simp [Shape.anon,affine,lagX]
lemma band_shift (n : Side) (z : ℤ) (w : ℕ) (x : Seat n) :
    x∈band n i s w ↔ (lagX (z • step i)).anon n x∈ band n i (s+2*z) w := by
  rw [band_spec,band_spec,band_shift_point,Int.cast_add]
  rw [show x i + (↑(2*z) : Per (More n))-(s+(↑(2*z):Per (More n))) = x i-(s:Per (More n)) from by abel]
end YM.CF.Buffered
