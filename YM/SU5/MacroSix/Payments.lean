import YM.SU5.MacroSix.Fields
/-! # Two-body kernel payments (both `commonWell` and unprojected grid instructions)

At each *ordered-in-time* pose pair. These are different quantities! Only
assert point-wise equality of the two at grid positions satisfying the additional
all-axes qualification. The separate convergence theorem after macroscopic quadrature
will identify the limit also without that additional qualification.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 360000
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
namespace HeatTwo
variable {j : Axis} (H : Hilbert) (T : OS.Semigroup H j)

lemma combine_heat (x : H) (s t : ℝ≥0) : T.E s (T.E t x)=T.E (s+t) x := by
  rw [T.time]; rfl

/-- Remove twice the width padding in the *representation* of the value (not the
support qualification or the slab width!). -/
lemma unfolded (X : Bool → H.Op) (u v : Bool → ℝ) (Ω x y : H) (k K : H.Op) (w : ℝ≥0)
    (a b : ℝ) (ha : v false = a+w) (hb : u true = b-w) (ht : v false < u true)
    (hx : (X false).adjoint Ω = k (T.E w x)) (hy : (X true) Ω = K (T.E w y))
    (hk : k (T.E w x)= T.E w (k x)) (hK : K (T.E w y) = T.E w (K y)) :
    Aria.receive T Ω X u v [false,true] = inner ℂ (k x) (T.E (b-a).toNNReal (K y)) := by
  let s := (u true - v false).toNNReal
  have he : (b-a).toNNReal = w + (s + w) := by
    ext; push_cast; rw [Real.coe_toNNReal,Real.coe_toNNReal] -- goals order
    · rw [hb,ha]; ring
    · exact sub_nonneg.mpr ht.le
    have hu := w.property; linarith
  unfold Aria.receive
  change inner ℂ Ω (T.E (u false - u false).toNNReal (X false (T.E s (X true Ω)))) = _
  rw [sub_self, Real.toNNReal_zero, T.eZero, ContinuousLinearMap.id_apply,
    ← ContinuousLinearMap.adjoint_inner_left, hx, hy, hk, hK, T.swing, he,
    combine_heat H T, combine_heat H T, add_assoc]

lemma dividePair (x y : H) (a b c : ℝ) (ha : a ≤ c) (hb : c ≤ b) :
    inner ℂ x (T.E (b-a).toNNReal y) =
      inner ℂ (T.E (c-a).toNNReal x) (T.E (b-c).toNNReal y) := by
  rw [T.swing, combine_heat, ← Real.toNNReal_add (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
    show c-a + (b-c) = b-a by abel]
variable {A : Type*} [AddCommGroup A]
private lemma move_backward (U : A → H.Op) (h : ∀ g x y, inner ℂ (U g x) y = inner ℂ x (U (-g) y))
    (r : A) (Q : H.Op) : ((U r).comp (Q.adjoint.comp (U (-r)))).adjoint =
      (U r).comp (Q.comp (U (-r))) := by
  have he (x : A) : (U x).adjoint = U (-x) := by
    ext1 y
    apply ext_inner_right ℂ; intro z
    rw [ContinuousLinearMap.adjoint_inner_left, h, neg_neg]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, he r, he (-r), neg_neg]; rfl
end HeatTwo

variable (P : Spine) (s n t : ℕ) (Z Z' : Window.Family) (x : P.Spectrum0 3)
local notation "M" => timeMesh P.par
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 β
local notation "G" => P.ManyF 3 β
local notation "S'" => P.physicalEnergy 3 β
local notation "H" => P.ColorHil 3 β
local notation "T" => (S).E
local notation "T'" => (S').E
local notation "Ω" => P.heaven 3 β
local notation "ω" => P.colorZero 3 β
local notation "U" => P.cartage 3 β
local notation "U'" => P.truck 3 β
local notation "θ" i:max => P.openField s n i x
local notation "v" i:max => P.darkField s n i x
local notation "w" => P.sixWidth s n 3
local notation "W" => ((P.sixWidth s n 3):ℝ)
local notation "τ" r:max => Real.toNNReal r
local notation "D" i:max => P.sixBody s n i
local notation "B" => (P.sixBody s n Z).kiss P 3
local notation "L" => ([false,true]:List Bool)

/-- Put reflected Z at first, Z' at second. Note `y` first position below is after any
center reflection in a smear: this also allows that position to be requested independently. -/
def arrayBodies : Bool → P.Apron := usher B (D Z')
local notation "A" => P.arrayBodies s n Z Z'

def fieldOrder (j : Axis) (y z : Vantage) : Prop :=
  y j + (P.sixWidth s n j:ℝ) < z j - (P.sixWidth s n j:ℝ)
local notation "K" => P.fieldOrder s n

def fieldKernel (y z : Vantage) : Matrix Window.Family Window.Family ℂ :=
  Matrix.of fun Z Z' ↦ P.commonWell 3 x (P.arrayBodies s n Z Z') (usher y z) [false,true]

def pose (k : Cover) : Vantage := P.laysM (P.vtile t k)
local notation "p" => P.pose t

/-- The matrix at a fine consultation in the system; same singleState on all heights. -/
def nativeKernel (y z : Cover) : Matrix Window.Family Window.Family ℂ := Matrix.of
  fun Z Z' ↦ P.singleState 3 t x (P.fieldAt t ((P.sixBody s n Z).kiss P 3) y *
    P.fieldAt t (P.sixBody s n Z') z)

lemma arrayOrder (j : Axis) (y z : Vantage) : K j y z ↔ P.Turnstile j A L (usher y z) := by
  unfold Turnstile; rw [List.pairwise_pair]
  change _ ↔ y j + (B).realWidth P j < z j - (D Z').realWidth P j
  rw [(D Z).kiss_width P 3,P.sixBody_width,P.sixBody_width]; rfl

lemma arrayResign (j : Axis) (q : Bool → Vantage) :
    P.resignY j A q false = q false j + (P.sixWidth s n j:ℝ) :=
  congrArg (q false j + ·) (P.sixBody_width s n Z j)

lemma arrayPorch (j : Axis) (q : Bool → Vantage) :
    P.porchY j A q true = q true j - (P.sixWidth s n j:ℝ) :=
  congrArg (q true j - ·) (P.sixBody_width s n Z' j)

lemma array_turn (j : Axis) (q : Bool → Vantage) (h : K j (q false) (q true)) :
    P.Turnstile j A L q := List.pairwise_pair.mpr (by
    rw [P.arrayResign,P.arrayPorch]; exact h)

private lemma heat_commutes_grid (g : P.VMark) (h : ℝ≥0) (z : H) :
    U' g (T' h z) = T' h (U' g z) :=
  DFunLike.congr_fun ((P.voyageF 3 β).hard (look 3) (T' h)
    (fun i _ a ↦ P.colorMoveE 3 β i a h) (g ∘ Subtype.val)) z

private lemma charter_backward (g : P.VMark) (Q : (H).Op) :
    (P.charter 3 β g Q.adjoint).adjoint = P.charter 3 β g Q :=
  HeatTwo.move_backward H (U') (P.truck_inner 3 β) g Q

lemma array_preview (q : Bool → P.VMark)
    (h : K 3 (P.laysM (q false)) (P.laysM (q true))) :
    P.preview 3 β A L q = inner ℂ (U' (q false) (θ Z))
      (T' (τ (P.laysM (q true) 3-P.laysM (q false) 3)) (U' (q true) (θ Z'))) := by
  let f := q false
  let g := q true
  let κ := P.laysM
  let u := P.porchY 3 A (κ ∘ q)
  let z := P.resignY 3 A (κ ∘ q)
  let X := P.commuteLoose 3 β A q
  let k := P.openField s n Z x
  let k' := P.openField s n Z' x
  let c (i : Window.Family) := (D i).engine P 3 β
  have hx : z false = κ f 3 + W := P.arrayResign ..
  have hy : u true = κ g 3 - W := P.arrayPorch ..
  have ht : z false < u true := by rw [hx,hy]; exact h
  have hu (i : Window.Family) (g : P.VMark) :
      P.charter 3 β g (c i) ω = U' g (T' w (θ i)) := by
    have he : c i ω=T' w (θ i) := P.bodyEngine_paid s n i x
    have hf : c i (U' (-g) ω) = T' w (θ i) :=
      (congrArg (c i) (P.truck_empty 3 β (-g))).trans he
    exact congrArg (U' g) hf
  have he : (X false).adjoint=P.charter 3 β f (c Z) :=
    (congrArg (fun r : (H).Op ↦ (P.charter 3 β f r).adjoint) ((D Z).peer P 3 β).symm).trans
      (P.charter_backward x f (c Z))
  have hf : (X false).adjoint ω= U' f (T' w k) :=
    (DFunLike.congr_fun he ω).trans (hu Z f)
  exact HeatTwo.unfolded H S' X u z ω k k' _ _ w _ _ hx hy ht hf (hu Z' g)
    (P.heat_commutes_grid x f w k) (P.heat_commutes_grid x g w k')

lemma nativeKernel_eq (hs : s ≤ t) (y z : Cover) (h : K 3 (p y) (p z)) :
    P.nativeKernel s n t x y z Z Z'=inner ℂ (U' (P.vtile t y) (θ Z))
      (T' (τ (p z 3 - p y 3)) (U' (P.vtile t z) (θ Z'))) := by
  let q := usher y z
  let C := P.fullScroll t A q L
  have he : C=P.fieldAt t B y * P.fieldAt t (D Z') z := by
    change _ * (_ * 1) = _
    rw [mul_one]; rfl
  let b := P.vtile t ∘ q
  have hv : P.preview 3 β A L b = P.singleState 3 t β C := P.turn_purchase 3 β A q t L
    (P.array_turn s n Z Z' 3 _ h) (fun i _ ↦ by cases i <;> exact hs)
  change P.singleState 3 t x _ = _
  exact ((congrArg (P.singleState 3 t x) he.symm).trans (P.single_agrees 3 3 x t C).symm).trans
    (hv.symm.trans (P.array_preview s n Z Z' x b h))

lemma array_memorial (q : Bool → Vantage) (h : K 3 (q false) (q true)) :
    P.memorial 3 β A L q = inner ℂ (U (q false) (v Z))
      (T (τ (q true 3 - q false 3)) (U (q true) (v Z'))) := by
  let f := q false
  let g := q true
  let u := P.porchY 3 A q
  let z := P.resignY 3 A q
  let X := P.commuteTight 3 β A q
  let k := v Z
  let k' := v Z'
  let c (i : Window.Family) := (D i).engine P 3 β
  have hx : z false = f 3 + W := P.arrayResign ..
  have hy : u true = g 3 - W := P.arrayPorch ..
  have ht : z false < u true := by rw [hx,hy]; exact h
  have hu (i : Window.Family) (g : Vantage) :
      P.tableau 3 β g (c i) Ω = U g (T w (v i)) :=
    (P.tableMaps 3 β (D i) g).trans (congrArg (U g) (P.bodyFlash_paid s n i x))
  let X' := P.tableau 3 β f (c Z)
  have he : (X false) = X'.adjoint :=
    (congrArg (fun r : (H).Op ↦ P.tableau 3 β f r) ((D Z).peer P 3 β).symm).trans
      (P.boards_star 3 β f _).symm
  have hz : (X false).adjoint = X' :=
    (congrArg (fun r : (G).Op ↦ r.adjoint) he).trans (ContinuousLinearMap.adjoint_adjoint _)
  have hf : (X false).adjoint Ω = U f (T w k) := (DFunLike.congr_fun hz Ω).trans (hu Z f)
  exact HeatTwo.unfolded G S X u z Ω k k' _ _ w _ _ hx hy ht hf (hu Z' g)
    (P.warm_drive 3 β f w k).symm (P.warm_drive 3 β g w k').symm

lemma fieldKernel_eq (J : P.Ellis 3 x) (y z : Vantage) (h : K 3 y z) :
    P.fieldKernel s n x y z Z Z'= inner ℂ (U y (v Z)) (T (τ (z 3-y 3)) (U z (v Z'))) :=
  let q := usher y z
  (P.common_cult 3 x A q L J (List.Perm.refl _) (P.array_turn s n Z Z' 3 q h)).trans
    (P.array_memorial s n Z Z' x q h)

-- Inner price with explicit real wall c. Used to prove convergence under independent
-- smearing: integrable vector factors, one per test, even with finite-width order prices.
lemma nativeKernel_factors (hs : s ≤ t) (y z : Cover) (h : K 3 (p y) (p z))
    (c : ℝ) (hc : p y 3 ≤ c) (hu : c ≤ p z 3) :
    P.nativeKernel s n t x y z Z Z' =
      inner ℂ (U' (P.vtile t y) (T' (τ (c-p y 3)) (θ Z)))
        (U' (P.vtile t z) (T' (τ (p z 3-c)) (θ Z'))) :=
  (P.nativeKernel_eq s n t Z Z' x hs y z h).trans
    ((HeatTwo.dividePair H S' _ _ _ _ _ hc hu).trans
      (congrArg₂ (inner ℂ) (P.heat_commutes_grid x _ _ (θ Z)).symm
        (P.heat_commutes_grid x _ _ (θ Z')).symm))

lemma fieldKernel_factors (J : P.Ellis 3 x) (y z : Vantage) (h : K 3 y z)
    (c : ℝ) (hc : y 3 ≤ c) (hu : c ≤ z 3) :
    P.fieldKernel s n x y z Z Z' =
      inner ℂ (U y (T (τ (c-y 3)) (v Z))) (U z (T (τ (z 3-c)) (v Z'))) :=
  (P.fieldKernel_eq s n Z Z' x J y z h).trans
    ((HeatTwo.dividePair G S _ _ _ _ _ hc hu).trans
      (congrArg₂ (inner ℂ) (P.warm_drive 3 β _ _ (v Z))
        (P.warm_drive 3 β _ _ (v Z'))))

lemma fieldKernel_plenum (J : P.Ellis 3 x) (hs : s ≤ t) (y z : Cover) (h : K 3 (p y) (p z))
    (hc : P.Plenum A L (usher (p y) (p z))) :
    P.fieldKernel s n x (p y) (p z) Z Z' = P.nativeKernel s n t x y z Z Z' := by
  let q := P.vtile t ∘ usher y z
  let b := P.laysM ∘ q
  have hp : b = usher (p y) (p z) := funext fun i ↦ by cases i <;> rfl
  have hv : P.Turnstile 3 A L b := P.array_turn s n Z Z' 3 b h
  have he := (P.entirely_now 3 x A L J 3 q hv (show P.Plenum A L b from hp.symm ▸ hc)).symm
  have hu := P.common_cult 3 x A b L J (List.Perm.refl _) hv
  exact ((congrArg (fun r ↦ P.commonWell 3 x A r L) hp.symm).trans (hu.trans he)).trans
    ((P.array_preview s n Z Z' x q h).trans (P.nativeKernel_eq s n t Z Z' x hs y z h).symm)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.nativeKernel_factors
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.fieldKernel_factors
