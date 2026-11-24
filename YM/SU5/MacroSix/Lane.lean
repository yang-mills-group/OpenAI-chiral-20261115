import YM.SU5.MacroSix.Success
import YM.SU5.MacroSix.Payments

/-! # All-axis lane qualification and analytic continuation

Can enter any axis on precisely this same `commonWell`; while testing no change of
state. Never applied to the proxy factor law. `fieldKernel` is not interpreted (needn't
be continuous) off the order domain.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria Set
open _root_.YM.MacroSix (Success rectangle)

namespace Spine

private lemma analytic_inside {G : Hilbert} {j : Axis} (T : OS.Semigroup G j)
    (a b : G) (g : ℝ → ℝ) (f : ℝ → ℂ) (D : Set ℝ)
    (p : AnalyticOnNhd ℝ g D) (e : IsOpen D) (u : ∀ x ∈ D, 0 < g x)
    (h : ∀ x∈D, f x= inner ℂ a (T.E (g x).toNNReal b)) : AnalyticOnNhd ℝ f D := by
  let F (z : ℂ) := inner ℂ a (T.F z b)
  have he : AnalyticOnNhd ℂ F OS.Semigroup.inside := fun z v ↦
    ((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ G.space b)).analyticAt _ |>.comp (T.localHeat _ v)
  intro x H
  have ht : AnalyticAt ℝ (fun x ↦ F (g x:ℂ)) x :=
    ((he _ (u x H)).restrictScalars (𝕜:=ℝ)).comp ((Complex.ofRealCLM.analyticAt _).comp (p _ H))
  refine ht.congr ?_
  filter_upwards [e.mem_nhds H] with y Y; have hu := u y Y
  change F _ = _
  rw [h y Y]; apply congrArg (inner ℂ a)
  have hp : (↑(g y):ℂ) = OS.Semigroup.duration (g y).toNNReal :=
    congrArg (fun t : ℝ ↦ (t:ℂ)) (Real.coe_toNNReal (g y) hu.le).symm
  exact DFunLike.congr_fun ((congrArg T.F hp).trans (T.roots_heat (Real.toNNReal_pos.mpr hu))) b

variable (P : Spine) (s n : ℕ) (Z Z' : Window.Family) (x : P.Spectrum0 3)
    (j : Axis) (signs : Axis → Bool)
local notation "β" => P.otherSpectrum 3 j x
local notation "S" => P.seasons j β
local notation "Ω" => P.heaven j β
local notation "H" => P.ManyF j β
local notation "E" => (S).E
local notation "U" => P.cartage j β
local notation "τ" r:max => Real.toNNReal r
local notation "w" k:max => ((P.sixWidth s n k):ℝ)
local notation "B" => (P.sixBody s n Z).kiss P 3
local notation "A" => P.sixBody s n Z'
local notation "L" => P.arrayBodies s n Z Z'
local notation "K" => P.fieldKernel s n x
local notation "l" => ([false,true] : List Bool)

/-- Prescribed sign in *each* coordinate. For one fixed sufficiently late i,
`signs` locates increments outside both shield widths. -/
def laneSign (sign : Bool) : Set ℝ := if sign then Set.Ioi (2*(w j)) else Set.Iio (-(2*w j))

def inLane : Set Vantage := MacroSix.rectangle fun j ↦ P.laneSign s n j (signs j)

def onLane : Set (Vantage × Vantage) := {x | x.2-x.1∈P.inLane s n signs}

lemma laneSign_open (p : Bool) : IsOpen (P.laneSign s n j p) := by
  unfold laneSign; split <;> first| exact isOpen_Ioi | exact isOpen_Iio
lemma laneSign_connected (p : Bool) : IsPreconnected (P.laneSign s n j p) := by
  unfold laneSign; split <;> first| exact isPreconnected_Ioi | exact isPreconnected_Iio
lemma lane_open : IsOpen (P.inLane s n signs) := MacroSix.rectangle_open _ fun i ↦ P.laneSign_open s n i (signs i)
lemma onLane_open : IsOpen (P.onLane s n signs) :=
  (P.lane_open s n signs).preimage (continuous_snd.sub continuous_fst)

lemma rightOf (y z : Vantage) : z j-y j ∈ P.laneSign s n j true ↔ P.fieldOrder s n j y z := by
  change 2*(w j)<z j-y j ↔ y j+_< z j-_; constructor <;> intro h <;> linarith
lemma leftOf (y z : Vantage) : z j-y j ∈ P.laneSign s n j false ↔ P.fieldOrder s n j z y := by
  change z j-y j< -(2*w j) ↔ z j+_< y j-_; constructor <;> intro h <;> linarith
lemma sign_before (y z : Vantage) (p : (y,z)∈P.onLane s n signs) (g : signs j=true) :
    P.fieldOrder s n j y z := (P.rightOf s n j y z).mp (g ▸ (show _ ∈ P.laneSign s n j (signs j) from p j))
lemma sign_after (y z : Vantage) (p : (y,z)∈P.onLane s n signs) (g : signs j=false) :
    P.fieldOrder s n j z y := (P.leftOf s n j y z).mp (g ▸ (show _ ∈ P.laneSign s n j (signs j) from p j))

lemma array_back (y z : Vantage) (h : P.fieldOrder s n j z y) :
    P.Turnstile j L [true,false] (usher y z) := List.pairwise_pair.mpr (by
  change z j+ (A).realWidth P j < y j-(B).realWidth P j
  rw [P.sixBody_width, Apron.kiss_width,P.sixBody_width]; exact h)

lemma plenum_onLane (y z : Vantage) (p : (y,z)∈P.onLane s n signs) : P.Plenum L l (usher y z) := by
  refine ⟨fun j ↦ ?_⟩
  cases he : signs j
  · exact ⟨[true,false],List.Perm.swap ..,P.array_back s n Z Z' j y z (P.sign_after s n j signs y z p he)⟩
  exact ⟨l,List.Perm.refl _, (P.arrayOrder s n Z Z' j y z).mp (P.sign_before s n j signs y z p he)⟩

-- express negative-going lane by opposite ordering and shifting the entire pose pair
variable (J : P.Ellis 3 x)
include J
lemma negative_order (y : Vantage) (h : y j < -(2*w j)) :
    K (0:Vantage) y Z Z' = inner ℂ (glareY x A j)
      (E (τ (-y j-2*w j)) (U (-y) (flashY x B j))) := by
  let p := usher (0:Vantage) y
  let q := usher (-y) (0:Vantage)
  have he : settler p (-y)=q := by
    funext i; cases i <;> simp [settler,p,q,usher]
  have hz : P.fieldOrder s n j y 0 := by
    change y j+ (w j) < (0:Vantage) j-(w j); rw [Pi.zero_apply]; linarith
  have hv := P.array_back s n Z Z' j 0 y hz
  have ht := P.settler_order j L p [true,false] hv (-y); rw [he] at ht
  have hp : p ∈ P.Federation L l := ⟨j,[true,false], List.Perm.swap .., hv⟩
  let u := (A).realWidth P j + (B).realWidth P j
  have hg : (-y) j-u= -y j-2*w j := by
    unfold u; rw [Pi.neg_apply,P.sixBody_width,Apron.kiss_width,P.sixBody_width]; ring
  calc
    _ = P.commonWell 3 x L (settler p (-y)) l := (P.common_shift 3 x L p l J hp (-y)).2.symm
    _ = P.memorial j β L [true,false] q := by rw [he,P.common_cult 3 x L q l J (List.Perm.swap ..) ht]
    _ = P.memorial j β (usher A B) l (usher (0:Vantage) (-y)) := rfl
    _ = inner ℂ (glareY x A j) (E (τ ((-y) j-u)) (U (-y) (flashY x B j))) :=
      memorial_two x A B j (-y)
    _ = _ := congrArg (fun a : ℝ ↦ inner ℂ (glareY x A j) (E (τ a) (U (-y) (flashY x B j)))) hg

lemma positive_order (y : Vantage) (h : 2*w j < y j) : K (0:Vantage) y Z Z' =
    inner ℂ (glareY x B j) (E (τ (y j-2*w j)) (U y (flashY x A j))) := by
  let u := (B).realWidth P j + (A).realWidth P j
  have hu : u=2*w j := by unfold u; rw [Apron.kiss_width,P.sixBody_width,P.sixBody_width]; ring
  exact (avail_cross x B A j y J (show u < y j from hu ▸ h)).trans
    (congrArg (fun a : ℝ ↦ inner ℂ (glareY x B j) (E (τ (y j-a)) (U y (flashY x A j)))) hu)

lemma fieldKernel_cont (y : Vantage × Vantage) (p : P.fieldOrder s n 3 y.1 y.2) :
    ContinuousAt (fun y : Vantage×Vantage ↦ K y.1 y.2 Z Z') y := by
  let T : Vantage×Vantage → (Bool → Vantage) := fun y ↦ usher y.1 y.2
  have he : T y∈P.Federation L l := ⟨3,l,List.Perm.refl _,(P.arrayOrder s n Z Z' 3 _ _).mp p⟩
  have h : Continuous T := continuous_pi fun i ↦ by cases i; exact continuous_fst; exact continuous_snd
  exact (P.common_cont 3 x L (T y) l J he).comp h.continuousAt

lemma fieldKernel_move (y z : Vantage) (p : P.fieldOrder s n 3 y z) : K y z = K 0 (z-y) := by
  ext1 Z Z'; let p' := usher y z
  have ht : settler p' (-y)=usher 0 (z-y) := by funext i; cases i <;> simp [settler,p',usher,sub_eq_add_neg,add_comm]
  -- after ext bind body family inferred fresh; explicit
  let A' := P.arrayBodies s n Z Z'
  have hp : p'∈P.Federation A' l := ⟨3,l,List.Perm.refl _,(P.arrayOrder s n Z Z' 3 _ _).mp p⟩
  exact (P.common_shift 3 x A' p' l J hp (-y)).2.symm.trans
    (congrArg (fun z ↦ P.commonWell 3 x A' z l) ht)

-- flip flag parameter on THIS axis. No additional gap hypotheses; when applying
-- require the signed relative chamber globally.
lemma laneTest (b : Bool) (y : Vantage) :
    AnalyticOnNhd ℝ (fun v : ℝ ↦ K (0:Vantage) (Function.update y j v) Z Z')
      (P.laneSign s n j b) := by
  let Y (x : ℝ) := Function.update y j x
  have he (t : ℝ) : Y t j=t := Function.update_self ..
  have hv (t : ℝ) (k : Axis) (p : k≠j) : Y t k=y k := Function.update_of_ne p ..
  cases b
  · let d (t : ℝ) := -t-2*w j
    let A' := P.laneSign s n j false
    let x₀ := glareY x A j; let z := flashY x B j
    refine analytic_inside S x₀ (U (-y) z) d _ A' (fun t _ ↦ analyticAt_id.neg.sub analyticAt_const)
      (P.laneSign_open s n j false) (fun t p ↦ by
        change t< -(2*w j) at p; unfold d; linarith) ?_
    intro t p
    have hx := P.negative_order s n Z Z' x j J (Y t) ((he t).trans_lt p)
    exact hx.trans (congrArg₂ (fun (t : ℝ) (K' : (H).Op) ↦ inner ℂ x₀ (E (τ t) (K' z)))
      (congrArg d (he t)) (of_slideP x j (-(Y t)) (-y) (fun k e ↦ congrArg Neg.neg (hv t k e))))
  let d (t : ℝ) := t-2*w j
  let A' := P.laneSign s n j true
  let x₀ := glareY x B j; let z := flashY x A j
  refine analytic_inside S x₀ (U y z) d _ A' (fun t _ ↦ analyticAt_id.sub analyticAt_const)
    (P.laneSign_open s n j true) (fun t p ↦ sub_pos.mpr p) ?_
  intro t p
  have hx := P.positive_order s n Z Z' x j J (Y t) ((he t).symm ▸ (show 2*w j<t from p))
  exact hx.trans (congrArg₂ (fun (t : ℝ) (K' : (H).Op) ↦ inner ℂ x₀ (E (τ t) (K' z)))
    (congrArg d (he t)) (of_slideP x j (Y t) y (hv t)))

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.laneTest
