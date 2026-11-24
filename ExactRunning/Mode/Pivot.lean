import ExactRunning.Mode.Platoon
/-!
# Unrestricted high gap

Nonsingularity at every real coarse momentum, needed even at zero for high with no cut.

`free`: away from zero, transport the change-of-completion matrix (no
conclusion from the uncompressed whole-period numerical determinant identity
alone). The old completion is a principal block of the full, and obtained
from the new one by congruence; thus both are nonsingular. `freeAll`: adds zero by testing the constant Fourier
mode in finite volume.
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
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing

variable (X)

def lever (m : Side) : Funds (Bodies G m (X.up m)) :=
  1 + stood (X.S m) (G:=G) 1 *
    ((grenade X.μ 1)⁻¹ * (X.settings (m:=m) 1 + -X.restored 1))

def blade :
    Tray G X.Barrel X.Barrel (fun m _ => X.lever m) :=
  let q := X.blow.reverse0 (fun p hp=> (X.blow_glow hp).unit)
    (fun _=> fund_det (grenade_safe _ X.hμ))
  ((Tub.ident (Du G) X.Barrel).plus
     (X.platoon.mul (q.mul (X.rudder.freeze.plus (X.clears.freeze.negate))))).shift <| by
    intro m; simp_rw [lever,X.fg_bg_zero];rfl

lemma pivot_front (m) :
    (X.lever m)ᵀ * X.high (m:=m) 1 1 * X.lever m = (X.vibrant 1 1).toBlocks₁₁ := by
  have hh := X.wort (m:=m) X.sitting_zero X.stable_zero
  have hs : X.thick 1 1 * X.lever m = X.thick 1 1 := by
    rw [lever,Matrix.mul_add, ← Matrix.mul_assoc,hh.1,Matrix.zero_mul,Matrix.mul_one,add_zero]

  have hs' : (X.lever m)ᵀ * X.thick 1 1 = X.thick 1 1 :=
    by simpa only [transpose_mul,hh.2.2] using congr_arg transpose hs
  have ht : X.restored 1 * X.lever m = X.settings 1 := by
    rw [lever,Matrix.mul_add,← Matrix.mul_assoc, X.restored_stood X.explosives_zero,
      Matrix.mul_one, ← Matrix.mul_assoc, Prod.fst_one, Matrix.mul_nonsing_inv _ (fund_det (grenade_safe _ X.hμ)), Matrix.one_mul]
    abel
  rw [X.vibrant_shape X.sitting_zero, Det.joint, toBlocks_fromBlocks₁₁]
  rw [high,Matrix.mul_add,Matrix.add_mul,hs',hs, ← ht,transpose_mul]
  simp only [Matrix.mul_assoc]

variable {p : Momentum}
lemma free (hp : star p=p) (hs : 0<shadeK p) :
    IsUnit (X.pulse.symb p).det := by
  let A := (X.glows.symb p).toBlocks₁₁
  let B := X.blade.symb p
  have ha := (X.joint_glow hp hs).principal.unit
  let L := Tub.fst (Du G) X.Barrel (Front G)
  have h := ((X.blade.tr.mul X.pulse).mul X.blade).align ((L.mul X.glows).mul L.tr) (fun m => ?_) hp
  · have e : Bᴴ * X.pulse.symb p * B = A := by
      simpa only [A, B, L, Tub.mul_symb, X.blade.reverse hp, Tub.tr_symb, Tub.fst_symb, topLeft_eq] using h
    change IsUnit A.det at ha
    rw [isUnit_iff_ne_zero] at ha ⊢
    intro hz; apply ha; rw [← e, Matrix.det_mul, Matrix.det_mul, hz, mul_zero, zero_mul]
  · change (X.lever m)ᵀ * X.high (X.fg_bg m 0) (co_bg G m 0) * X.lever m =
        πl _ _ ℝ * X.vibrant (X.fg_bg m 0) (co_bg G m 0) * (πl _ _ ℝ)ᵀ
    rw [topLeft_eq, X.fg_bg_zero, co_bg_zero]; exact X.pivot_front m

lemma unit_of_rails {α : Type} [Fintype α] [DecidableEq α]
    {F : Momentum→ CompM α α} {U : Funds (Co m α)}
    (h : Jaunt (approached U) F 0) (k : IsUnit U.det) (i : Site m)
    (he : rolls (mon i) p) :
    IsUnit (F p).det := by
  have hs : IsUnit (approached U).det :=
    Complex.ofRealHom.map_det U ▸ k.map Complex.ofRealHom
  rw [← Matrix.isUnit_iff_isUnit_det,← Matrix.mulVec_injective_iff_isUnit]
  intro x y e
  have hj : tune i x = tune i y :=
    mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hs)
      ((h i p he x).trans ((congr_arg _ e).trans (h i p he y).symm))
  funext j
  have hy := congr_fun hj (0,j)
  simpa [tune,cell] using hy

lemma freeAll (p) (hp : star p=p) :
    IsUnit (X.pulse.symb p).det := by
  by_cases h : 0<shadeK p
  · exact X.free hp h
  let m := walent X.lo
  obtain ⟨T⟩ := X.test (m:=m) (Nat.le_succ ..)
  apply unit_of_rails (X.pulse.rails m) _ 0
  · rw [mon_zero]; exact (shade_missing h hp).symm
  rw [repack_det, X.fg_bg_zero, co_bg_zero]
  exact T.high_unit

end BlockTie
end ExactRunning
