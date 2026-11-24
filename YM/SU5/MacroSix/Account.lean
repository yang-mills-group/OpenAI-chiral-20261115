import YM.SU5.MacroSix.ReflectedPocket
import YM.SU5.MacroSix.Bodies

/-!
# Body stamp in the real character's Spine — geometry and promotion

We guard not just the priced apron in the macro pose, but the ONE mixed (e.g.
stock) Family seen through all the high `t` calculations on that course. Its
step is exactly paid in the P.Register. `RibbonAccount` checks that the actual
cover expansion (both panes) can price 2 disjoint pockets: one creation and one
removal in its terms, with representation-Type labels retained. Require fixed
macroscopic physical regions for those pockets too (`W,X` include SHIELDS).
(Use a slightly larger footprint around either end if desired.) These may vary
with the body being asked for. The *same physical regions* are admissible at
every future rung — no shrinking-stencil encounter needed for this center Ward
test.

Coordinates in all the physical support receipts below are Tapestry coordinates
(doubled vs Vantage pose; spacing one at s=0 for the GAUGE vertices), same as
`scenery`. `ε` and widths in the response theorem use the actual fermion units.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
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
open Germ Alliance Lamour.Bridge.Celeste Sods Prototype Aria Pockets
namespace Spine
variable (P : Spine) (s : ℕ) (j : Axis) (ρ : P.Register)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "l" => P.width
local notation "w" => ruler P.par.block
local notation "Up" S:max => followBox («Λ»:=P.par) («l»:=P.width) S
local notation "ϵ" => Tapestry.shield Λ l s

lemma conform (x : Cover) : IsCompact (Tapestry.shield Λ l s x) := by
  let t := precisionAt Λ s; let C : ℝ := Journey.reserve Λ l
  let k (j : Axis) := Set.Icc (((x j:ℝ)-C)/t) (((x j:ℝ)+C)/t)
  have ht : 0<t := positiveScale Λ s
  convert isCompact_pi_infinite (s:=k) (fun _ ↦ isCompact_Icc) using 1
  ext y; apply forall_congr'
  intro j; rw [abs_le]
  unfold k
  rw [Set.mem_Icc,div_le_iff₀ ht,le_div_iff₀ ht]; change ((-C ≤ t*y j - _) ∧ (t*y j - _ ≤ C)) ↔ _
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

/-- As `printedHere` footprint of the manuscript, expressed in the gauge units. -/
def placard (S : Finset Cover) : Set RSpace := ⋃ x∈(S:Set Cover), Tapestry.shield P.par P.width s x
lemma placard_spec {S : Finset Cover} {W : Set RSpace} :
    printedHere Λ P.width s S W ↔ P.placard s S ⊆ W := by simp only [printedHere,placard,Set.iUnion_subset_iff, Finset.mem_coe]
lemma placard_print (S : Finset Cover) : printedHere Λ P.width s S (P.placard s S) :=
  (P.placard_spec s).2 Set.Subset.rfl
lemma placard_intro {S : Finset Cover} {x : Cover} (p : x∈ S) : ϵ x ⊆ P.placard s S :=
  P.placard_print s S x p
lemma placard_compact (S : Finset Cover) : IsCompact (P.placard s S) :=
  S.finite_toSet.isCompact_biUnion fun i _ ↦ P.conform s i

variable (r : ℤ)
def loft (v : Vantage) (u : Set RSpace) : Set RSpace := (fun x ↦ x+(2:ℕ) • v) '' u
local notation "q·" u:max => loft (P.plenumShift s j r) u
lemma plow_exact {x : Cover} {S : Finset Cover} (h : x∈ S) :
    x+(ruler P.par.block*r) • step j ∈ SlabMark.plow P.calibration j r S := by
  unfold plow Tower.address; rw [ruler_offset]; exact Finset.mem_image_of_mem _ h

lemma loft_prints {S : Finset Cover} {W : Set RSpace} (p : printedHere Λ P.width s S W) :
    printedHere Λ P.width s (plow K j r S) (loft (P.plenumShift s j r) W) := by
  intro y q u h
  obtain ⟨z,v,rfl⟩ := plow_stays K j r S q
  exact ⟨_,p z v (P.step_shield j s r z u h),sub_add_cancel _ _⟩

lemma loft_back (x : Cover) : loft (P.plenumShift s j r) (ϵ x) ⊆ ϵ (x+(w*r)•step j) := by
  rintro y ⟨z,t,rfl⟩
  let a := P.plenumShift s j r
  have hu : x+(w*r) • step j+(w*(-r)) • step j=x := by rw [mul_neg,neg_smul]; exact add_neg_cancel_right ..
  have hv : P.plenumShift s j (-r)=-a := by
    funext i; by_cases g : i=j <;> simp [plenumShift,a,bell,g]
  have he := P.step_shield j s (-r) (x+(w*r) • step j) z (hu.symm ▸ t)
  rwa [hv, smul_neg,sub_neg_eq_add] at he

lemma loft_placard (S : Finset Cover) : loft (P.plenumShift s j r) (P.placard s S)=
    P.placard s (plow K j r S) := by
  apply Set.Subset.antisymm _ ((P.placard_spec s).1 (P.loft_prints s j r (P.placard_print s S)))
  rintro x ⟨u,h,rfl⟩; obtain ⟨i,h,t⟩ := Set.mem_iUnion₂.mp h
  exact P.placard_intro s (P.plow_exact j r h) (P.loft_back s j r i (Set.mem_image_of_mem _ t))

lemma loft_mono (x : Vantage) {R T : Set RSpace} (h : R ⊆ T) : loft x R ⊆ loft x T :=
  Set.image_mono h
lemma loft_assoc (u x : Vantage) (W : Set RSpace) : loft u (loft x W)=loft (u+x) W := by
  unfold loft; rw [Set.image_image]; simp only [smul_add, add_comm _ ((2:ℕ) • x), add_assoc]; simp only [add_left_comm]

lemma loft_disjoint (x : Vantage) {R T : Set RSpace} (h : Disjoint R T) : Disjoint (loft x R) (loft x T) := Set.disjoint_image_of_injective (fun i j ↦ add_right_cancel) h

section build
variable {S T U : Finset Cover} {b : Bool}

lemma ribbon_advances (f : Swatch S) (h : render S K f∈ Pockets.ribbon K S b T U) (v : T ⊆ S) (u : U ⊆ S) :
    render (Up S) K (ρ.loom S s f)∈ Pockets.ribbon K (Up S) b (Up T) (Up U) := by
  let Y := P.run; let H := P.large
  let S' := Up S
  let C (n : ℕ) := coupon P.run P.large S s (P.period (P.projection.rows n)) (P.cutoff (P.projection.columns n)) f
  have he : Tendsto C atTop (𝓝 (ρ.loom S s f)) :=
    cn_apply (X:=Swatch S) (Y:=Swatch (Up S)) (P.limit_witness s S ρ) (tendsto_const_nhds (x:=f))
  obtain ⟨m,p⟩ := (separates K (tips (Up S))).exists
  apply through_glasses m ⟨p⟩ (follow_subset P.par P.width v) (follow_subset P.par P.width u) (texture ..)
  intro x
  let F (f : Swatch S') := render S' K f m x
  let Q := torRibbon b (Satin.region (Up T) ((K).c m)) (Satin.region (Up U) ((K).c m))
  have hf : ∀ᶠ n : ℕ in atTop,F (C n)∈ Q := by
    filter_upwards [(P.all_heights_here ρ).eventually (Exhibition.cone_bill Y H S s (P.talks ρ))] with n p
    exact ribbon_view m (ribbon_coupon Y H s _ _ v u p.1 f h) x
  exact Q.closed_of_finiteDimensional.mem_of_tendsto (((P.evaluate_cont S' m x).continuousAt).tendsto.comp he) hf

lemma through_ribbon {f : P.Test} (h : f.val ∈ Pockets.ribbon K S b T U) (v : T⊆ S) (u : U ⊆ S) :
    (P.promote s ρ f).val ∈ Pockets.ribbon K (Up S) b (Up T) (Up U) := by
  obtain ⟨x,rfl⟩ := accolade K S f ((Tapestry.locates ..).mpr (ribbon_test h v u))
  rw [promote,Exhibition.fromLocal]; exact P.ribbon_advances s ρ x h v u

end build

/-- Receipt. All three supports, *same* geometry, at every actual Family, and all true
paired arguments. lambda is constant across uses of the receipt. -/
structure RibbonAccount (X A B : Set RSpace) (S T U : Finset Cover) (b : Bool) (f : P.Test) : Prop where
  ribbon_ : f.val ∈ Pockets.ribbon P.calibration S b T U
  color : f ∈ enclave P.calibration
  t : T ⊆ S
  u : U ⊆ S
  cloth : printedHere P.par P.width s S X
  pocketUp : printedHere P.par P.width s T A
  pocketDown : printedHere P.par P.width s U B
  zoneUp : A ⊆ X
  zoneDown : B ⊆ X
  compactUp : IsCompact A
  compactDown : IsCompact B
  noOverlap : Disjoint A B

local notation "pin" => Tapestry.mirrorE j (markZ Λ s r)

namespace RibbonAccount
variable {f : P.Test} {S T U : Finset Cover} {X A B : Set RSpace} {b : Bool}
variable (h : P.RibbonAccount s X A B S T U b f)
include h ρ
lemma persists_one : P.RibbonAccount (s+1) X A B (Up S) (Up T) (Up U) b (P.promote s ρ f) :=
  ⟨P.through_ribbon s ρ h.ribbon_ h.t h.u,
    Exhibition.riseGauge P.run P.large s (P.talks ρ) h.color,
    follow_subset P.par P.width h.t,follow_subset P.par P.width h.u,
    shielding Λ l s X S h.cloth, shielding Λ l s A T h.pocketUp,shielding Λ l s B U h.pocketDown,
    h.zoneUp,h.zoneDown,h.compactUp,h.compactDown,h.noOverlap⟩

local notation "Here" => Tower.volumeAround P.par P.width
lemma persists (n : ℕ) : P.RibbonAccount (s+n) X A B (Here n S) (Here n T) (Here n U) b
    (P.conveying s n f) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show P.conveying s (n+1) f = P.promote (s+n) ρ (P.conveying s n f) from
      Subtype.ext (P.promotes_to (s+n) ρ (P.conveying s n f)).symm, ← Nat.add_assoc]
    exact ih.persists_one P (s+n) ρ

omit ρ
lemma bigger {Z : Set RSpace} (p : X ⊆ Z) : P.RibbonAccount s Z A B S T U b f :=
  { h with zoneUp:= Set.Subset.trans h.zoneUp p, zoneDown:= Set.Subset.trans h.zoneDown p,
           cloth:= fun i v ↦ Set.Subset.trans (h.cloth i v) p }

lemma reflective : P.RibbonAccount s ((pin) '' X) ((pin) '' B) ((pin) '' A)
    (negativeSide S r j) (negativeSide U r j) (negativeSide T r j) b (aureole K j r f) := by
  have hc : Continuous (pin) := by
    apply continuous_pi
    intro i; by_cases h : i=j
    · subst i; simp only [mirrorE,↓reduceIte]; exact continuous_const.sub (continuous_apply j)
    simp only [mirrorE,if_neg h]; exact continuous_apply _
  exact ⟨turns_ribbon r j h.ribbon_,P.mirror_keeps j r h.color,
    Finset.image_subset_image h.u,Finset.image_subset_image h.t,reversed Λ l h.cloth,
    reversed Λ l h.pocketDown,reversed Λ l h.pocketUp,
    Set.image_mono h.zoneDown,Set.image_mono h.zoneUp,h.compactDown.image hc,h.compactUp.image hc,
    Set.disjoint_image_of_injective (Tapestry.mirrorTwice _ _).injective h.noOverlap.symm⟩

lemma displaced : P.RibbonAccount s (q· X) (q· A) (q· B)
    (plow K j r S) (plow K j r T) (plow K j r U) b (P.shifts j r f) := by
  have hp (S : Finset Cover) : plow K j r S=negativeSide (negativeSide S 0 j) (gaugeT K r) j := by
    change _ = reflectedBox j (gaugeT K r) (reflectedBox j 0 S)
    rw [support_translation,sub_zero]; rfl
  have hut := h.ribbon_
  refine ⟨?_, P.shifts_keep j r h.color,Finset.image_subset_image h.t,Finset.image_subset_image h.u,
    P.loft_prints s j r h.cloth,P.loft_prints s j r h.pocketUp,P.loft_prints s j r h.pocketDown,
    Set.image_mono h.zoneUp,Set.image_mono h.zoneDown,h.compactUp.image (continuous_id.add continuous_const),
    h.compactDown.image (continuous_id.add continuous_const),loft_disjoint _ h.noOverlap⟩
  rw [hp,hp,hp]; exact turns_ribbon _ _ (turns_ribbon _ _ hut)
end RibbonAccount

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms through_ribbon
#print axioms loft_placard
#print axioms RibbonAccount.reflective
#print axioms RibbonAccount.displaced
#print axioms RibbonAccount.persists
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
