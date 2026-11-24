import YM.SU5.MacroSix.Budget
import YM.SU5.Voyager.Shine

/-! # On the selected character: incision and one-body vectors -/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Aria

namespace Spine
variable (P : Spine) (s n t : ℕ) (j : Axis) (Z : Window.Family)
  (x : P.Spectrum0 3)
local notation "M" => timeMesh P.par
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 β
local notation "G" => P.ManyF 3 β
local notation "H" => P.ColorHil 3 β
local notation "E" => (S).E
local notation "Ω" => P.heaven 3 β
local notation "ω" => P.colorZero 3 β
local notation "Π" => P.wealth 3 β
local notation "F₀" => P.stockS Z (P.flash n)
local notation "t'" => P.travelTime s n
local notation "F₁" => P.sixBody s n Z
local notation "v" => P.birthCloud x Z s n

private lemma view_sub_of (A : Hilbert) (k x y : A)
    (a : inner ℂ k k = inner ℂ k x - inner ℂ k y)
    (b : inner ℂ x k = inner ℂ x x - inner ℂ x y)
    (c : inner ℂ y k = inner ℂ y x - inner ℂ y y) : k = x-y := by
  have hb (u : A) (p : inner ℂ u k = inner ℂ u x - inner ℂ u y) :
      inner ℂ u (k-(x-y))=0 := by rw [inner_sub_right, inner_sub_right, p, sub_self]
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp (by
    rw [inner_sub_left, inner_sub_left,hb _ a,hb _ b,hb _ c]; ring))

lemma viewF_sub (y : P.Spectrum0 j) {f g : P.Test} (p : P.birthF j s f)
    (q : P.birthF j s g) (u : P.birthF j s (f-g)) :
    P.viewF j y s u = P.viewF j y s p - P.viewF j y s q := by
  have he (b : P.Test) (z : P.birthF j s b) :
      inner ℂ (P.viewF j y s z) (P.viewF j y s u) =
        inner ℂ (P.viewF j y s z) (P.viewF j y s p) -
          inner ℂ (P.viewF j y s z) (P.viewF j y s q) := by
    let X := P.singleState j s y
    have ht : X (P.reflectTest j b * (f-g)) = X (P.reflectTest j b * f) -
        X (P.reflectTest j b * g) := by rw [mul_sub,map_sub]
    exact ((P.released_gram j y s z u).trans ht).trans (congrArg₂ (· - ·)
      (P.released_gram j y s z p).symm (P.released_gram j y s z q).symm)
  exact view_sub_of (P.ColorHil j y) _ _ _ (he _ u) (he _ p) (he _ q)

/-- v_Zi `(I-E₃(t'_i)) v⁰` of the theorem. -/
def darkField : G := v - E t' v

/-- Unprojected (still **selected**) body vector at base position. -/
def openField : H := P.viewF 3 β s (P.timeTest_birth s n Z)

local notation "θ" => P.openField s n Z x
local notation "u₀" => P.darkField s n Z x
local notation "E'" => (P.physicalEnergy 3 β).E
local notation "w" => P.sixWidth s n 3

lemma openField_eq : θ = P.shard x Z s n - E' t' (P.shard x Z s n) :=
  let p := P.brightC Z s n
  let a := P.advanceCount n
  (P.viewF_sub s 3 β p (P.passesLater 3 s a p) (P.timeTest_birth s n Z)).trans
    (congrArg (P.shard x Z s n - ·) (P.releasedLater 3 β s a p))

private lemma transport_sub_center {B : Hilbert} (T : B.Op) (x y u : B) (c : ℂ)
    (p : T u=u) (q : x=y+c • u) : x - T x = y - T y := by
  rw [q,map_add,map_smul,p]; abel

lemma darkField_selected : Π θ = u₀ := by
  let m := Π
  let g := P.shard x Z s n
  have he : m g=P.lucid x Z s n := rfl
  have hp : θ = g - E' t' g := P.openField_eq s n Z x
  have ht : m (E' t' g) = E t' (P.lucid x Z s n) := P.bankHeat 3 β t' g
  exact (congrArg m hp).trans (((map_sub m g (E' t' g)).trans (congrArg₂ (· - ·) he ht)).trans
    (transport_sub_center (E t') (P.lucid x Z s n) (v) Ω _
      (P.heaven_hot 3 β t') (P.halo_split ..)))

lemma darkField_orthogonal : inner ℂ Ω u₀ = 0 := by
  let K := P.birthCloud x Z s n
  have he : inner ℂ Ω (E t' K) = inner ℂ Ω K := ((S).swing t' Ω K).symm.trans
    (congrArg (fun x : G ↦ inner ℂ x K) (P.heaven_hot 3 β t'))
  exact (inner_sub_right (𝕜:=ℂ) Ω K _).trans
    ((congrArg (inner ℂ Ω K - ·) he).trans (sub_self _))

/-- Heat due to body-width placement in the slab operator. -/
lemma bodyEngine_paid : (F₁).engine P 3 β ω = E' w θ :=
  let p := P.timeTest_birth s n Z
  let T := F₁
  let k := T.u 3
  let h := P.passesLater 3 s k p
  calc _ = P.viewF 3 β s h := (P.engine_view 3 β T).trans
                             (P.identical_F 3 β s _ _ (T.card_price P 3))
       _ = _ := P.releasedLater 3 β s k p

lemma bodyFlash_paid : flashY x F₁ 3 = E w u₀ :=
  let e := E w
  (congrArg (Π) (P.bodyEngine_paid s n Z x)).trans ((P.bankHeat 3 β w θ).trans
    (congrArg e (P.darkField_selected s n Z x)))

-- One-height calculations identifying the ordering apparatus with this character.
-- Includes the moved, full-width (not narrow) proofs.
lemma oneTest_centered : P.singleState 3 s x (P.timeTest n Z) = 0 := by
  rw [timeTest,map_sub,P.slide_single,sub_self]

lemma oneMirror_centered : P.singleState 3 s x ((F₁).kiss P 3).F = 0 := by
  have he : P.singleState 3 s x (P.reflectTest 3 (F₁).F) =
      star (P.singleState 3 s x (F₁).F) :=
    (congrArg (P.chi 3 x) (P.reading_star 3 s (F₁).F).symm).trans (map_star ..)
  exact he.trans ((congrArg star (P.oneTest_centered s n Z x)).trans (star_zero _))

lemma carry_single (f : P.Test) (a : ℕ) :
    P.singleState 3 (s+a) x (P.conveying s a f) = P.singleState 3 s x f :=
  congrArg (P.chi 3 x) (P.carryReads 3 s a f)

lemma cruise_single (L : List Axis) (r : Cover) (f : P.Test) :
    P.singleState 3 t x (P.cruise L r f) = P.singleState 3 t x f := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [P.cruise_step, AlgHom.comp_apply]
    exact (P.single_agrees 3 i x t _).symm.trans (((P.slide_single i _ _ _ _).trans
      (P.single_agrees 3 i x t _)).trans ih)

-- common fullScroll pair will use this
/-- Actual moved body, ready at any `t ≥ B.s`. -/
def fieldAt (B : P.Apron) (r : Cover) : P.Test := P.chartAll r (B.full P t)

lemma fieldAt_single (B : P.Apron) (r : Cover) (h : B.s ≤ t) :
    P.singleState 3 t x (P.fieldAt t B r) = P.singleState 3 B.s x B.F := by
  have he := P.carry_single B.s x B.F (t-B.s)
  rw [Nat.add_sub_of_le h] at he
  exact (P.cruise_single t x Vacancy.ordinate r _).trans he

lemma fieldAt_singlet (B : P.Apron) (r : Cover) : P.fieldAt t B r ∈ enclave P.calibration :=
  P.cruise_color Vacancy.ordinate r (B.fullColor P t)

-- actual physical support receipt; `scenery` uses coordinates doubled as in Drape
lemma fieldAt_budget (K : P.Register) (B : P.Apron) (r : Cover) (h : B.s ≤ t) :
    P.fieldAt t B r ∈ keep P.par P.width t P.calibration true
      (B.scenery P (P.laysM (P.vtile t r))) := P.calibrated_location t B r K h

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bodyFlash_paid
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.fieldAt_single
