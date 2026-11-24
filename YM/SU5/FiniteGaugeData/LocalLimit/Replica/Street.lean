import YM.Cells.Interior
import YM.CF.Continuum.CanalTwo

/-!
# Place power-of-2 copies under buffered reflections.

Unfold from a single displaced box. For each axis (of the four), on each doubling,
we slide the entire pattern of reflected image marks by the previous extent. This avoids
extra divisibility constraints on the period while preserving any needed margins on
that step. Gauge period = `More N`. Widths here are gauge-grid lengths.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Window.SquareScalar
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Lat Cube RP Push.GridApprox Cells
open scoped Classical Topology BigOperators ContDiff InnerProductSpace ComplexOrder ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
variable {N:Side}{P:Patch}(d:ℕ) (s:Axis)
local notation "G" => SU.group
local notation "R₀" => reach P
local notation "Λ" => More N
local notation "Γ" => Config SU.group (More N)
-- Counts dyadic exponents axiswise
abbrev RoomCount := Four ℕ
def Realm (P:Patch)(d:ℕ)(c:RoomCount) := {x:Cover|∀ s,reach P < x s ∧ x s + reach P < ↑(d* (2:ℕ)^c s)}
def stone (P:Patch)(N:Side)(d:ℕ)(c:RoomCount) := wrap (More N) '' Realm P d c
def spanAlong(s:Axis)(c:RoomCount) := update c s (c s+1)
def ferry (s:Axis)(d:ℕ)(c:RoomCount) : Cover := (d*2^c s) • step s
local notation "S₀" d:max c:max => stone P N d c
variable (c:RoomCount)
lemma rayRoom (e: d *2^c s ≤ N.val): S₀ d c ⊆ ↑(buffered s P N):=by
 rintro v ⟨x,p,rfl⟩; have hv:=(show ∀ i, _ from p) s
 have hs: 0 ≤ x s:=by
    obtain ⟨u,w⟩:=(show ∀ i, (R₀:ℤ) < x i ∧ _ from p) s; omega
 have hn:(x s).toNat < (Λ).val:=by change _ < N.val*2; omega
 have he : wrap Λ x s = ↑(x s).toNat:=by change ((x s): Per Λ)=_; rw [← Int.cast_natCast,Int.toNat_of_nonneg hs]
 apply Finset.mem_filter.mpr; rw [he,ZMod.val_natCast_of_lt hn]; exact ⟨mem_univ _,by omega,by omega⟩

local notation "K₀" => spanAlong s c
local notation "σ" => ferry s d c
local notation "Y" => Set.image (affine (Signed.mirror s) (0: Site Λ)) (stone P N d c)
lemma carry : Set.MapsTo (affine 1 (wrap Λ σ)) (stone P N d c) (stone P N d (spanAlong s c)):=by
 rintro v ⟨x,p,rfl⟩; refine ⟨x+σ,?_ ,by simp [affine]⟩; intro i; have h1:=(show ∀ i, _ from p) i
 by_cases h:i=s
 · subst i; simp only [spanAlong, update_self, Pi.add_apply,ferry, step_apply,if_true,Pi.smul_apply, nsmul_eq_mul, mul_one]
   rw [pow_add,pow_one]; simp only [Pi.mul_apply, Pi.natCast_apply, step_apply, if_true, mul_one]; push_cast at *; rcases h1 with ⟨h,w⟩; constructor
   · exact h.trans_le (le_add_of_nonneg_right (by positivity))
   linarith
 simp only [spanAlong, update_of_ne h, Pi.add_apply,ferry, step_apply,if_neg h,Pi.smul_apply, smul_zero,add_zero]; exact h1
lemma grab : Set.MapsTo (affine 1 (wrap Λ σ)) Y (stone P N d (spanAlong s c)):=by
 rintro v ⟨x,⟨x,h,rfl⟩,rfl⟩; refine ⟨(Signed.mirror s).act x+σ,?_ ,by simp [affine]⟩; intro i; obtain ⟨hx,hv⟩:=(show ∀ i, _ from h) i
 by_cases p:i=s
 · subst i; simp only [spanAlong, update_self, Pi.add_apply,ferry, step_apply,if_true,Pi.smul_apply, nsmul_eq_mul,mul_one,Signed.act,Signed.mirror,Equiv.refl_symm,Equiv.refl_apply,decide_true]
   rw [pow_add,pow_one]; simp only [Pi.mul_apply, Pi.natCast_apply, step_apply, if_true, mul_one]; push_cast at *; constructor <;> linarith
 have u:s≠i:=Ne.symm p; simp only [spanAlong, update_of_ne p, Pi.add_apply,ferry, step_apply,if_neg p,Pi.smul_apply, smul_zero,add_zero, Signed.act,Signed.mirror,Equiv.refl_symm,Equiv.refl_apply, u, p, decide_false,Bool.false_eq_true, ite_false]; exact ⟨hx,hv⟩

structure boxed (P:Patch)(d:ℕ)(c:RoomCount)(w:ℝ) {N:Side} (X:Config SU.group (More N)→ℂ) : Prop where
 localB : Interior (stone P N d c) X
 costs(i) : ‖X i‖≤w
variable (X:Config SU.group (More N)→ℂ){w:ℝ}(U:boxed P d c w X)
/-- multiplication of the current positive-side array by its (gauge) reflected
copy, followed by the shift compatible with donors when `2*B∣d`. -/
def copy (s:Axis)(d:ℕ)(c:RoomCount) (X:Γ→ℂ) : Γ→ℂ := ((θBack s X)*X) ∘ pull 1 (wrap Λ (ferry s d c))
include U
lemma copy_cost : boxed P d K₀ (w^2) (copy s d c X):=by
 let J:= (θBack s X); let S:=wrap (More N) (ferry s d c); let M:=pull 1 S (K:=SU.group.El)
 have ht:Interior (Set.image (affine (Signed.mirror s) (0: Site (More N))) (stone P N d c)) J:= (U.localB.unchanged (Signed.mirror s) 0 (Set.mapsTo_image ..)).real; let a:= ht.unchanged 1 S (grab (P:=P) d s c)
 constructor
 · exact a.times (U.localB.unchanged 1 S (carry d s c))
 intro v
 change ‖J (M v)*X (M v)‖ ≤ _; rw [norm_mul,pow_two]; exact mul_le_mul (by unfold J θBack; rw [comp_apply,norm_star]; apply U.costs) (U.costs _) (norm_nonneg _) ((norm_nonneg _).trans (U.costs v))
end YM.CF.Window.SquareScalar
