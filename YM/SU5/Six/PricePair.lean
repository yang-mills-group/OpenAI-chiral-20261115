import YM.SU5.Six.DropNight
import YM.SU5.Voyager.Shine
set_option autoImplicit false
set_option maxHeartbeats 80000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine
open Aria Cheer YM.OS

variable (P : Spine) (x : P.Spectrum0 3) (B D : P.Apron)
    (k : Axis) (p q : Vantage)
set_option quotPrecheck false
local notation "ξ" j:max => P.advocate 3 x j
local notation "E" j:max => (P.seasons j (ξ j)).E
local notation "W" j:max => P.cartage j (ξ j)
/-- Relative vectors admitting the indicated increasing strict order of full boxes. -/
def forwardPair : Set Vantage := {r | B.realWidth P k + D.realWidth P k < r k}
local notation "L" => [false,true]
lemma orderPair (h : q-p ∈ P.forwardPair B D k) :
    P.Turnstile k (usher B D) L (usher p q) := by
  change _ + _ < q k - p k at h
  apply List.pairwise_pair.mpr; change p k + B.realWidth P k < q k - D.realWidth P k; linarith
lemma orderPair' (h : p-q ∈ P.forwardPair D B k) :
    P.Turnstile k (usher B D) [true,false] (usher p q) := by
  change _ + _ < p k - q k at h
  apply List.pairwise_pair.mpr; change q k + D.realWidth P k < p k - B.realWidth P k; linarith

/-- Always used on an open qualification; `x` here the **original**
axis-3 character. -/
def bodyPair := P.commonWell 3 x (usher B D) (usher p q) L

lemma bodyPair_fwd (J : P.Ellis 3 x) (h : q-p ∈ P.forwardPair B D k) :
    P.bodyPair x B D p q =
      inner ℂ (glareY x B k) ((E k) (Real.toNNReal ((q-p) k -
        (B.realWidth P k + D.realWidth P k))) ((W k) (q-p) (flashY x D k))) := by
  let g := usher (0 : Vantage) (q-p)
  have hp : g ∈ P.Federation (usher B D) L :=
    ⟨k,L,List.Perm.refl _,P.orderPair B D k 0 (q-p) (by rw [sub_zero]; exact h)⟩
  have e : settler g p = usher p q := by
    funext i; cases i <;> simp [settler, g, usher]
  have hs := (P.common_shift 3 x _ g _ J hp p).2
  rw [e] at hs
  exact hs.trans <| avail_cross x B D k (q-p) J h

lemma bodyPair_bwd (J : P.Ellis 3 x) (h : p-q ∈ P.forwardPair D B k) :
    P.bodyPair x B D p q = P.bodyPair x D B q p := by
  have hv := P.common_cult 3 x _ _ L J (List.Perm.swap true false [])
    (P.orderPair' B D k p q h)
  have hu := P.common_cult 3 x _ _ L J (List.Perm.refl _)
    (P.orderPair D B k q p h)
  exact hv.trans hu.symm
/-- Spatial component in `Space3` conventions. -/
def spacePart (r : Vantage) := YM.spatial (WithLp.toLp 2 r)
@[fun_prop]
lemma continuous_spacePart : Continuous spacePart := by unfold spacePart; fun_prop
lemma spacePart_trans (r : Vantage) :
    transverse 3 (fun i : Trans 3 => r i.val) = shore (spacePart r) := by
  apply Subtype.ext; apply PiLp.ext
  intro i; refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ((transverse 3 (fun i : Trans 3 => r i.val)).property.trans
      (shore (spacePart r)).property.symm : _)
  exact (transverse_eyes 3 (fun i : Trans 3 => r i.val) ⟨j.castSucc, Fin.castSucc_lt_last _ |>.ne⟩).trans
    (congrFun (congrArg WithLp.ofLp (spatial_position (spacePart r) 0)) j).symm
lemma cart_space (r : Vantage) : (W 3) r = (P.seasons 3 (ξ 3)).U (shore (spacePart r)) :=
  (P.uses_cart ..).trans (congrArg _ (spacePart_trans _))

variable (s n : ℕ)
/-- Axis-3 continuation with negative times clipped to zero.
Used as `K` of `Macropositions` only with `r 3 > 2 * costW ... 3`.
Inputs: second minus first pose. Order `θ₃ A`, `A'`.
-/
def rise (r : Vantage) : Matrix Window.Family Window.Family ℂ :=
  P.risingK x s n (spacePart r) (Real.toNNReal (r 3))
lemma rise_inner (r : Vantage) (Z Z' : Window.Family) :
    P.rise x s n r Z Z' =
      inner ℂ (P.incV x Z s n) ((W 3) r ((E 3) (Real.toNNReal (r 3)) (P.incV x Z' s n))) := by
  exact congrArg (fun A : (P.ManyF 3 (ξ 3)).Op => inner ℂ (P.incV x Z s n) (A ((E 3) (Real.toNNReal (r 3)) (P.incV x Z' s n)))) (P.cart_space x r).symm

lemma rise_cont : Continuous (P.rise x s n) := by
  apply Continuous.matrixOf
  apply continuous_pi; intro Z
  apply continuous_pi; intro Z'
  -- `caravan` with continuous heat
  let u := P.incV x Z s n
  let v := P.incV x Z' s n
  let f (r : Vantage) := (E 3) (Real.toNNReal (r 3)) v
  have g : Continuous f := ((P.seasons 3 (ξ 3)).continuousE v).comp
    (continuous_real_toNNReal.comp (continuous_apply 3))
  apply (show Continuous (fun r => inner ℂ u ((W 3) r (f r))) from
    continuous_const.inner (P.caravan 3 (ξ 3) id _ continuous_id g)).congr
  intro r; exact (P.rise_inner ..).symm
section invoice
variable (Z Z' : Window.Family)
/-- First posed body, already opposed, center *after* reflection. -/
def incB := (P.incA Z s n).kiss P 3
lemma incB_width (j : Axis) : (P.incB s n Z).realWidth P j = P.costW s n j := rfl
/-- Charged time width. -/
def dayWidth := whenly (timeMesh P.par) s (P.costU n 3)
lemma dayWidth_eq : (P.dayWidth s n:ℝ) = P.costW s n 3 := (natural_time ..).symm
lemma incF_ticket :
    flashY x (P.incA Z s n) 3 =
      (E 3) (P.dayWidth s n) (P.incV x Z s n) := by
  have hp := P.incF_bright Z s n
  have e := P.passesLater 3 s (P.costU n 3) hp
  have h := Eq.trans (P.engine_view 3 (ξ 3) (P.incA Z s n))
    ((P.identical_F 3 (ξ 3) s _ e ((P.incA Z s n).card_price P 3)).trans
      (P.releasedLater 3 (ξ 3) s (P.costU n 3) hp))
  exact Eq.trans (congrArg (P.wealth 3 (ξ 3)) h) (P.bankHeat ..)
-- Factoring the three heats
private lemma day_comp {H : Hilbert} {j : Axis} (S : Semigroup H j) (a : ℝ≥0)
    (b : ℝ) (hb : (a:ℝ)+(a:ℝ)<b) (U : H.Op)
    (hu : ∀ t (v:H), S.E t (U v) = U (S.E t v)) (v w : H) :
    inner ℂ ((S.E a) v) ((S.E ((b - ((a:ℝ)+(a:ℝ))).toNNReal))
      (U ((S.E a) w))) = inner ℂ v (U ((S.E b.toNNReal) w)) := by
  have he : a + ((b - ((a:ℝ)+(a:ℝ))).toNNReal + a) = b.toNNReal := by
    ext; rw [NNReal.coe_add, NNReal.coe_add,
      Real.coe_toNNReal _ (sub_pos.mpr hb).le, Real.coe_toNNReal _
        (add_nonneg a.prop a.prop |>.trans hb.le)]
    linarith only
  rw [S.swing, hu _ ((S.E a) w), hu, ← ContinuousLinearMap.comp_apply (S.E (b-((a:ℝ)+(a:ℝ))).toNNReal) (S.E a),
    ← S.time, ← ContinuousLinearMap.comp_apply (S.E a), ← S.time,he]

/-- Recognition of `eq:exactS2` as the price of the ordered pair at
poses. See `DropNight` for its spectral and vacuum-(whole p₃=0)-free
formula. `q` is the later pose. `p` is the pose of the opposed body
(itself e.g. the reflection of a forward pose). -/
lemma bodyPair_rise (J : P.Ellis 3 x)
    (h : 2 * P.costW s n 3 < (q-p) 3) :
    P.bodyPair x (P.incB s n Z) (P.incA Z' s n) p q = P.rise x s n (q-p) Z Z' := by
  let d := P.dayWidth s n
  rw [two_mul] at h
  have he : (d:ℝ)+(d:ℝ) = (P.incB s n Z).realWidth P 3 +
      (P.incA Z' s n).realWidth P 3 := congrArg₂ (·+·) (P.dayWidth_eq s n) (P.dayWidth_eq s n)
  have h₁ : (d:ℝ)+(d:ℝ)<(q-p) 3 := he.symm ▸ h
  refine Eq.trans (P.bodyPair_fwd x (P.incB s n Z) (P.incA Z' s n) 3 p q J h) ?_
  let G (a : ℝ) (v w : P.ManyF 3 (ξ 3)) := inner ℂ v ((E 3) (((q-p) 3 - a).toNNReal) ((W 3) (q-p) w))
  refine Eq.trans (congrArg (fun b => G b (glareY x (P.incB s n Z) 3) (flashY x (P.incA Z' s n) 3)) he.symm) ?_
  refine Eq.trans (congrArg₂ (G _) ((flashY_glare x (P.incA Z s n) 3).trans (P.incF_ticket x s n Z))
    (P.incF_ticket x s n Z')) ?_
  exact (day_comp (P.seasons 3 (ξ 3)) d _ h₁ ((W 3) (q-p))
    (P.warm_drive 3 (ξ 3) (q-p)) _ _).trans (P.rise_inner x s n _ Z Z').symm

end invoice
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
