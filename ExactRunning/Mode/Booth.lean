import ExactRunning.Mode.Underfoot
/-!
# Gap of full symbol on cut

This transports the *factorization* of the vacuum operator, not
just an identity of its determinants, so e.g. nonsingularity can
be concluded at an individual real momentum outside the mesh.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

namespace Tub
variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q : Crate} {u : Filling ι P Q}

def negate (T : Tub ι P Q u) : Tub ι P Q (fun m z => -u m z) :=
  (T.scale (-1)).shift (fun _=>Filter.Eventually.of_forall fun _=>neg_one_smul ..)

@[simp]
lemma negate_symb (T : Tub ι P Q u) (p : Momentum) :
    T.negate.symb p = -(T.symb p) := by simp [negate]

end Tub

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing

-- The coordinates u, y, w of the collapse, at mode p.
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]

lemma stage_det (U : Matrix γ α ℂ) (M : Matrix γ β ℂ) :
    let T := fromBlocks
      (fromBlocks (1 : Matrix α α ℂ) (0:Matrix α β ℂ) 0 0)
      (fromRows 0 Mᴴ) (-(fromCols U M))
      (1 : Matrix γ γ ℂ)
    T.det = (Mᴴ * M).det := by
  intro T
  let P := fromBlocks 1 (0:Matrix (α⊕β) γ ℂ) (fromCols U M) 1

  have h : P.det=1 := by simp [P]
  rw [← mul_one T.det, ← h, ← Matrix.det_mul]
  simp only [T,P,fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
    Matrix.mul_one,Matrix.one_mul,zero_add,add_zero,neg_add_cancel,det_fromBlocks_zero₂₁,
    fromRows_mul_fromCols,fromBlocks_add,det_fromBlocks_zero₁₂,det_one,mul_one,one_mul]

variable (X)

lemma sector_top (M : Matrix β (α⊕γ) ℝ) : M * (πl α γ ℝ)ᵀ = M.submatrix id Sum.inl := by
  ext i j
  simp [πl,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]

def feeSector :
    Tray G (Front G) X.Scroll
      (fun m z => X.sectors (X.fg_bg m z)) :=
  (X.charters.mul (Tub.fst _ _ _).tr).shift (fun _ => Filter.Eventually.of_forall fun _ => sector_top _)

def roles :
    Tray G X.Hold X.Hold (fun m z =>
      Det.u_y_w (X.sectors (X.fg_bg m z)) (mail (co_bg G m z))) :=
  (.blocks (.blocks (.ident ..) (.nil ..) (.nil ..) (.nil ..))
    (.rows (.nil ..) (belle G).tr)
    (X.feeSector.cols (belle G)).negate (.ident ..))

def tally :
    Tray G X.Hold X.Hold (fun m z =>
      fromBlocks (fromBlocks (epMat E.p E.r (X.fg_bg m z).1) 0 0 (1:Funds (Lines G m 0)))
      0 0 (X.kcoin m)) :=
  .blocks (.blocks X.fas (.nil ..) (.nil ..) (.ident ..)) (.nil ..) (.nil ..) ((Tub.ident _ _).scale _)

variable {p : Momentum} (hp : star p=p) (hs : 0<shadeK p)
include hp hs

lemma roles_det :
    IsUnit (X.roles.symb p).det := by
  have hh := (outerGhost_glow G hp hs).unit
  unfold roles Det.u_y_w
  simp only [Tub.blocks_symb,Tub.nil_symb,Tub.ident_symb,Tub.rows_symb,
    Tub.cols_symb,Tub.negate_symb,(belle G).reverse hp]
  rw [stage_det,← (belle G).reverse hp]
  exact hh

lemma tally_glow :
    Glow (X.tally.symb p) := by
  simp only [tally,kcoin,Tub.blocks_symb,Tub.nil_symb,Tub.scale_symb,Tub.ident_symb]
  exact ((X.fas_glow hp hs).comp (Glow.one _)).comp (Glow.weighted_one _ X.penalty)

lemma joint_glow :
    Glow (X.glows.symb p) := by
  have h := X.glows.align ((X.roles.tr.mul X.tally).mul X.roles) (fun m => ?_) hp
  · rw [h,Tub.mul_symb,Tub.mul_symb,X.roles.reverse hp]
    exact (X.tally_glow hp hs).congr (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (X.roles_det hp hs)))
  dsimp
  rw [Det.u_y_w_gram]
  simp [X.vibrant_zero]

end BlockTie
end ExactRunning
