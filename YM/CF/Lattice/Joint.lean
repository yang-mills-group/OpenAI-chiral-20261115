import YM.CF.Lattice.Slow
import YM.CF.Fock.Compressed
/-! Continuous, nowhere zero unit Weyl determinant-line lift at (U,v). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
variable (N : YM.Lattice.Side)
private noncomputable abbrev alt (n : Type*) [d : DecidableEq n] (l : LinearOrder n) : LinearOrder n := { l with
  toDecidableEq := d
  compare_eq_compareOfLessAndEq := by
    haveI : LinearOrder n := l
    have h : d=l.toDecidableEq := Subsingleton.elim _ _
    rw [h]; exact l.compare_eq_compareOfLessAndEq }
noncomputable instance fo : LinearOrder (Model N) := alt _ (LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective)
open scoped Matrix.Norms.L2Operator MatrixOrder
attribute [local instance] opCStarAlgebra
open Lattice SU
open Fock
variable {N}
def turnX (t : Site N → E) (v : Site N → Vect) : Site N → Vect := fun i => turn (t i) (v i)
def turnW (t : Site N→E) (x : Fock.Wave (Model N)) := acts (quantU (n:=Model N) (conjG matter t)).val x

def occP (s : Site N) (U : Bkg N) := projector (frame matter U s).H
def sectionJ (s : Site N) (U : Bkg N) (v : Site N→Vect) := anchored (occP s U) (Cfield v)
def Joint (N : Side) (e : ℝ) := {p : Bkg N × (Site N → Vect) | PlaqBound matter p.1 (1/60) ∧ (∀ x, ‖p.2 x‖=1) ∧ Slow p.1 p.2 e}
lemma sectionJ_cov (t : Site N→E) (s : Site N) (p : Bkg N × (Site N → Vect)) (g : PlaqBound matter p.1 (1/60)) :
    sectionJ s (gauge t p.1) (turnX t p.2)=turnW t (sectionJ s p.1 p.2) := by
  unfold sectionJ occP turnX turnW; rw [twist_projection matter t p.1 s g,C_gauge]; exact anchor_g ..
lemma occProj (s : Site N) (U : Bkg N) (g : PlaqBound matter U (1/60)) : IsStarProjection (occP s U) := (band matter U s g).projection
/-- Uniform in volume, any index sector, simultaneous gauge transformations. -/
theorem lifting : ∃ δ:ℝ, 0<δ ∧ ∀ (N : Side) (s : Site N),
    ContinuousOn (fun p => sectionJ s p.1 p.2) (Joint N δ) ∧
    ∀ p∈ Joint N δ, Sea (occP s p.1) (sectionJ s p.1 p.2) := by
  obtain ⟨δ,he,hδ⟩ := compressible
  refine ⟨δ,he,?_⟩; intro N s
  have hp := projector_cont matter s matter_cont
  have ht (x) (hx : x∈Joint N δ) : Nonsing (occP s x.1) (Cfield x.2) :=
    nonsingSmall (P:=occP s x.1) ⟨Cfield x.2,C_unit _ hx.2.1⟩ ((hδ N s _ _ hx.1 hx.2.1 hx.2.2).trans_lt (by norm_num))
  constructor
  · have h : ContinuousOn (fun p => (occP s p.1,Cfield p.2)) (Joint N δ) :=
      (hp.comp continuous_fst.continuousOn (fun _ g => g.1)).prodMk (C_cont.comp continuous_snd).continuousOn
    intro p g
    let F := fun p : Bkg N × (Site N → Vect) => (occP s p.1,Cfield p.2)
    have hy : filled (occP s p.1) (Cfield p.2)≠0 := nonemptyFill _ _ (occProj s p.1 g.1) (C_skew p.2 g.2.1) (ht p g)
    have H : ContinuousAt (fun t : Op (Model N) × Op (Model N) => anchored t.1 t.2) (F p) := anchor_cont _ _ hy
    exact H.comp_continuousWithinAt (f:=F) (h p g)
  exact fun p g => anchorSea _ _ (occProj _ _ g.1) (C_skew _ g.2.1) (ht p g)
end YM.CF.Lat
