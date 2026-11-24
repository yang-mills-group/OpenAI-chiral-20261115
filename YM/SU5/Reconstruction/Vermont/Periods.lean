import YM.SU5.Reconstruction.Vermont.Reeler
import YM.SU5.Reconstruction.Crease.Proscenium
/-!
# Support of Wick-stage real readings. No enlargement needed beyond these linearized segments.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail BridgeClub ContinuousLinearMap Picket
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(M:Set E4→ Net H)(U:Set E4)
local notation "Π"=> ℝ≥0
local notation "χ"=>S.edge
lemma unedge (t:ℝ): S.edge (-t)*S.edge t=1:=by rw [← edge_adds, neg_add_cancel, S.birth]; rfl
@[simp] lemma unedge' (t:ℝ): S.edge t * S.edge (-t)=1:= by simpa only [neg_neg] using unedge S (-t)
-- attach start t of slab DUR.Pose shift. takes cost motion λ; applies entire Wick clock calendar. Analytical boundary at REAL mink includes global time edge displacement by length. cancel.
-- λ any real in computation; support notation uses sign already, so ok.
def stroke (A:ℂ→ H.Op)(t ζ:ℝ)(d:ℝ≥0): H.Op:= parcelUp S ((t*ζ) • basis a) (A (sideways t)* (S.edge (-(t*(d:ℝ))))) -- t=λ, ζ=start low
local notation "Ψ"=>stroke S
noncomputable def period (j:Axis)(U:Set E4)(t ζ:ℝ)(d:ℝ≥0): Set E4 := ⋃ u:ℝ, ⋃ (_h:u∈ Set.Icc ζ (ζ+(d:ℝ))), ((fun x:E4=> x+(t*u) • basis j) '' U)
local notation "τ"=> period a U
variable (t ζ:ℝ)
lemma starch (A:ℂ→ H.Op)(d:Π): stroke S A t ζ d= χ (t*ζ)*A (sideways t)*(χ (-(t*(ζ+(d:ℝ))))):= by
 rw [stroke,tickParcel,← mul_assoc,mul_assoc, ← edge_adds]; rw [show -(t*(d:ℝ)) + -(t*ζ) = -(t*(ζ+(d:ℝ))) from (by ring)] -- tune
lemma seats (d e f :Π)(b:ℝ)(u:ζ≤ b)(v : b+(d:ℝ) ≤ ζ + e) : period a U t b d ⊆ τ t ζ e:=by
 rintro x p; obtain ⟨z,v1⟩:= mem_iUnion.mp p; obtain ⟨k,z1⟩:= mem_iUnion.mp v1; exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨(show z∈Icc ζ (ζ+(e:ℝ)) from ⟨u.trans k.1,k.2.trans v⟩),z1⟩⟩
variable (m:Monotone M)(pT: ∀ (V:Set E4) (B:H.Op)(v:E4), B∈ M V → parcelUp S v B∈ M ((fun x=> x+v) '' V))
include pT m
lemma poised {A:ℂ→H.Op}{d c:Π}(p: WickScript S (M U) A d c) : stroke S A t ζ d∈ M (period a U t ζ d):=by
 induction p generalizing ζ with
 | weather d=> rw [stroke, shifted_side, mul_comm (d:ℝ), unedge']; unfold parcelUp; rw [mul_one, BridgeClub.mail]; exact one_mem _
 | now A t' a1 e=>
    rw [stroke, NNReal.coe_zero,mul_zero,neg_zero, show χ 0=1 from S.birth, mul_one]; apply m (show ((fun x=> x+(t*ζ) • basis a) '' U) ⊆ _ from ?_) (pT U A _ a1)
    exact Set.subset_iUnion₂_of_subset ζ (show ζ∈ Icc ζ (ζ+((0:Π):ℝ)) from by simp) (Subset.refl _) -- tune name
 | @link A B d e c u _ _ ih h=>
    have u₀:=m (seats (a:=a) U t ζ d (d+e) d ζ le_rfl (add_le_add_right (le_add_of_nonneg_right (e:ℝ≥0).property) _)) (ih ζ) -- name arg order left or right
    have u₁ := m (seats (a:=a) U t ζ e (d+e) e (ζ+(d:ℝ)) (le_add_of_nonneg_right d.property) (by push_cast; rw [add_assoc])) (h (ζ+(d:ℝ)))
    apply Eq.mp _ (mul_mem u₀ u₁); congr 1; -- tune goal
    rw [starch, starch,starch, NNReal.coe_add, add_assoc]; simp only [mul_assoc, ← mul_assoc (χ (-(t*(ζ+↑d)))) (χ (t*(ζ+↑d))), unedge,one_mul]
 | @plus A B d c u _ _ ih h=>
   rw [starch, mul_add,add_mul,← starch S t ζ A,←starch S t ζ B]; exact add_mem (ih ζ) (h ζ)
 | @scale A d c _ t' ih=> rw [starch, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← starch S t ζ A]; exact (M _).toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem _ (ih ζ)
 | charge _ t ih=> exact ih ζ
end YM.Lens
