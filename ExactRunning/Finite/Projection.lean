import ExactRunning.Finite.Ray
import ExactRunning.Thermo.Latitude
import ExactRunning.Det.Fit

/-!
# Projection onto active modes in finite volume

`Co m α` indexes fields on a 4-torus of side m, with internal coordinate
α (e.g., link orientations times color). `D.cut m α` is a real `ModeCut`
specified by `maskM` on plane waves. See also `cut_tune` in Shift.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

namespace Latitude
variable (D : Latitude)

def maskM (α : Type) [DecidableEq α] (p : Momentum) : CompM α α :=
  if D.active p then 1 else 0

lemma maskM_neg (p : Momentum) : D.maskM α (-p) = D.maskM α p := by
  simp [maskM]

private lemma exists_cut (m : Side) (α : Type) [Fintype α] [DecidableEq α] :
    ∃ K : ModeCut (Co m α), Jaunt (approached K.e) (D.maskM α) 0 := by
  have he := exists_jaunt_real m (D.maskM α)
    (fun p q h => by simp only [maskM,Latitude.active,D.mark_rolls h]) (by
      intro p; rw [maskM_neg]; unfold maskM; split
      · exact Matrix.map_one _ (map_zero _) (map_one _)
      exact Matrix.map_zero _ (map_zero _))
  obtain ⟨K,hK⟩ := he
  refine ⟨⟨K,?_,?_⟩,hK⟩
  · apply approached_inj
    have t := hK.adjoin (show rolls (mon (0:Site m)) 0 by rw [mon_zero]; exact rolls.refl _)
    have h : (fun q => (D.maskM α (-(q+0)))ᵀ) = D.maskM α := funext fun q => by
      rw [add_zero,maskM_neg]; unfold maskM; split <;> simp
    rw [h] at t
    exact jaunt_eq t hK
  apply approached_inj
  have t := Ticket.Jaunt0 hK hK
  have h : (fun q => D.maskM α q * D.maskM α q) = D.maskM α :=
    funext fun q => by unfold maskM; split <;> simp
  rw [h] at t
  rw [prom_mul]
  exact jaunt_eq t hK

def cut (m : Side) (α : Type) [Fintype α] [DecidableEq α] : ModeCut (Co m α) :=
  (exists_cut D m α).choose

lemma cut_jaunt (m : Side) (α : Type) [Fintype α] [DecidableEq α] :
    Jaunt (approached (D.cut m α).e) (D.maskM α) 0 := (exists_cut D m α).choose_spec

@[simp] lemma full_cut (m : Side) (α : Type) [Fintype α] [DecidableEq α] :
    full.cut m α = ModeCut.total := by
  have h : Jaunt (approached (1:Matrix (Co m α) (Co m α) ℝ)) (full.maskM α) 0 := by
    have h : (full.maskM α) = fun _ => 1 := funext fun _ => if_pos (full_active _)
    rw [h, approach_one]
    exact Jaunt.noop
  have he := approached_inj (jaunt_eq (full.cut_jaunt m α) h)
  exact ModeCut.ext he
end Latitude
end ExactRunning
