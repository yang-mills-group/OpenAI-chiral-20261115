import YM.CF.Continuum.Algebra
import YM.CF.Skye.Pine
import YM.CF.Spire.Elys

/-! # Reflect the orbit of the normalized effective amplitudes -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Finset Fock Lattice Wilson Lat Cube SU Scroll Spire Tulip Mir Mir.Trip Phase RP Skye Dial
open MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {m B : Side}
local notation "Λ" => CSide m B

def sweep (N : Side) (i : Axis) : Spire.Sweep N := ⟨Signed.mirror i, 0, false⟩
def reflectedOrbitFun (m B : Side) (i : Axis) (x : Orbit (CSide m B)) :=
  (flashA (sweep _ i) x.1, bun (sweep (CSide m B) i) x.2)
variable (i : Axis)

lemma sweep_inv {N : Side} : (sweep N i)⁻¹=sweep N i := by
  change (Sweep.mk (Signed.mirror i)⁻¹ _ _) = _
  have p : (Signed.mirror i)⁻¹=Signed.mirror i := rfl
  change Sweep.mk _ (-(Signed.mirror i)⁻¹.act 0) false= _; simp [p,sweep]
lemma cast_sweep {N : Side} : castX (sweep N i) = shape i := by
  let h : Lattice.lift (0:Site N)=0 := funext fun t=>by simp [Lattice.lift]
  unfold castX shape sweep; congr
lemma tilt_prep : prepU (castX (sweep (CSide m B) i)) (pinLift i) (xtra false) Λ=fullTurn m B i := by
  rw [cast_sweep]; rfl
lemma reflected_first : flashA (sweep (CSide m B) i)=mirrorPane m B i := by
  funext V; rw [revoke, mirrorPane_eq]
  change polarT false ∘ pull _ ((assembly Λ).root 0) V=pull _ _ V
  rw [map_zero]; rfl
lemma flip_shapes (V : Pane Λ) :
    flashA (sweep (CSide m B) i) V=stir (xtra false) (shape i) V := by
  unfold flashA; rw [cast_sweep]; rfl

lemma keepsVolume : MeasurePreserving (reflectedOrbitFun m B i)
    ((prior SU.group (More Λ)).prod (depot Λ)) ((prior SU.group (More Λ)).prod (depot Λ)) := by
  have h : MeasurePreserving (flashA (sweep (CSide m B) i)) (prior SU.group (More Λ)) (prior SU.group (More Λ)) := by
    rw [reflected_first,mirrorPane_eq]; exact Wilson.prior_pull (Signed.mirror i) (n:=More Λ) 0
  exact h.prod (tuft (sweep _ i))
lemma reflected_invol : Involutive (reflectedOrbitFun m B i) := fun x=> by
  have hx : flashA (sweep (CSide m B) i) (flashA (sweep (CSide m B) i) x.1)=x.1 := by
    nth_rw 1 [←sweep_inv (N:=CSide m B)]; exact revB ..
  have he : bun (sweep (CSide m B) i) (bun (sweep (CSide m B) i) x.2)=x.2 := by
    nth_rw 1 [←sweep_inv (N:=CSide m B)]; exact tuftT ..
  exact Prod.ext hx he

def orbitFlip (m B : Side) (i : Axis) : Orbit (CSide m B) ≃ᵐ Orbit (CSide m B) :=
  ⟨(reflected_invol i).toPerm (reflectedOrbitFun m B i), (keepsVolume i).measurable,(keepsVolume i).measurable⟩

lemma orbitFlip_gauge (x : Orbit Λ) : (orbitFlip m B i x).1=mirrorPane m B i x.1 :=
  congrFun (reflected_first ..) x.1
lemma fullTurn_physical (T : FC (Single Λ)) : tourP (fullTurn m B i) false true T=theta (fullTurn m B i) T := rfl

lemma inner_turn (x y : Wave (SpinFields m B)) :
    inner ℂ (arum (fullTurn m B i) false true (mateK Λ) x) (arum (fullTurn m B i) false true (mateK Λ) y)=
      star (inner ℂ x y) := by
  have h := tickR (shape i) inert (pinLift i) (mirrorX i) Λ
  exact arum_globe (fullTurn m B i) false true (Tset Λ) (touchP _ ▸ tickB Λ) h x y
lemma vacuum_turn : arum (fullTurn m B i) false true (mateK Λ) (mateK Λ)=mateK Λ :=
  arum_self (fullTurn m B i) false true (Tset Λ) (touchP _ ▸ tickB Λ) (tickR (shape i) inert (pinLift i) (mirrorX i) Λ)
end YM.CF.Window
