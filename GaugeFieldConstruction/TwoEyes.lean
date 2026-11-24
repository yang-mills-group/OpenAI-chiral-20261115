import GaugeFieldConstruction.Stars

/-! ∂ₖ and even ∂ₖ² injective on this seven-dimensional T shelf. -/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration
open Function U1 Cauchy Row Record Conj Module Submodule Floor Raw
open scoped BigOperators

private lemma battery {M X : Type*} [AddCommMonoid M] [Module ℂ M] [AddCommMonoid X] [Module ℂ X]
    (F : M→ₗ[ℂ]X) (P : Module.End ℂ M) (Q : Module.End ℂ X) (h : ∀ i, F (P i) = Q (F i))
    (x n) : F (P^[n] x)=Q^[n] (F x) := by
  induction n with
  | zero => rfl
  | succ n ih=> rw [iterate_succ_apply',iterate_succ_apply',h,ih]

lemma bright (k : Axis) (n : ℕ) (X : SymT) (h : ∀ i : Raw.Sym,(P k)^[n] (shells four (X.val i))=0) : X=0 := by
  apply (package four symAct).injective; rw [map_zero]; apply Prod.ext
  · suffices liftG X=0 by exact this
    apply Subtype.ext
    apply release recG symAct _ (liftG X).property.1 k driveG n
    intro i
    have hp : ∀ p : Shell, coG (P k p)=recG.P k (coG p) := fun p=> rfl
    change (recG.P k)^[n] (coG (shells four (X.val i)))=0; rw [← battery coG _ _ hp,h i,map_zero]
  refine Prod.ext (funext fun i=>?_) (funext fun i=>?_)
  · suffices liftF X i=0 by exact this
    apply Subtype.ext
    apply release ph symAct _ (liftF X i).property.1 k driveF n
    intro j
    have hp : ∀ p:Shell, coF (first i) (P k p)=ph.P k (coF (first i) p) := fun p=> rfl
    change (ph.P k)^[n] (coF _ (shells four (X.val j)))=0
    rw [←battery _ _ _ hp,h j,map_zero]
  exact lift3 X i
end YM.GaugeFieldConstruction.Calibration
