import YM.SU5.MacroSix.Account
import YM.SU5.MacroSix.Payments

/-! # Epoch-independent stamp costs for the actual tests

Expose both singular-placement (reporting the birth/death footprint price,
through `t`, with both orientations) and span versions. This is for the time
INCISION, retaining pockets of each of its summands, not for its fusion with
an overlapping body. -/

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
open Germ Alliance Lamour.Bridge.Celeste Sods Prototype Aria Pockets Designs
namespace Spine
variable (P : Spine) (s : ℕ) (j : Axis) (ρ : P.Register)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "l" => P.width
local notation "ℓ" => Journey.reserve Λ P.width
local notation "w" => ruler P.par.block
local notation "ϵ" => Tapestry.shield Λ P.width s

-- reserve for the body chosen at s; through increasing heights and at centers
-- shifted as in a pose. Show it for the span of such charges (including composite
-- in physical supports if all charged accounts authorized).
def Covered (W : Set RSpace) (b : Bool) : Submodule ℂ P.Test := Submodule.span ℂ
  {f | ∃ A B S T U, P.RibbonAccount s W A B S T U b f}
section stamps
variable {W X : Set RSpace} {b : Bool} {f : P.Test}

lemma accountCovered {S T U : Finset Cover} {A B : Set RSpace}
    (p : P.RibbonAccount s W A B S T U b f) : f∈ P.Covered s W b :=
  Submodule.subset_span (show _ ∈ _ from ⟨A,B,S,T,U,p⟩)

lemma coveredPrices : P.Covered s W b ≤ ((keep Λ P.width s K true W) ⊓ enclave K).toSubmodule :=
  Submodule.span_le.mpr (by
    rintro f ⟨A,B,S,T,U,p⟩
    exact ⟨⟨S,ribbon_test p.ribbon_ p.t p.u,p.cloth⟩,p.color⟩)

lemma covered_bigger (h : W ⊆ X) : P.Covered s W b ≤ P.Covered s X b :=
  Submodule.span_mono (by rintro f ⟨A,B,S,T,U,p⟩; exact ⟨A,B,S,T,U,p.bigger P s h⟩)

lemma covered_promote : P.Covered s W b ≤ Submodule.comap (P.promote s ρ) (P.Covered (s+1) W b) :=
  Submodule.span_le.mpr (by rintro f ⟨A,B,S,T,U,p⟩; exact P.accountCovered _ (p.persists_one P s ρ))
include ρ in
lemma covered_conveying (p : f∈ P.Covered s W b) (t : ℕ) : P.conveying s t f∈ P.Covered (s+t) W b := by
  induction t with
  | zero => exact p
  | succ t ih =>
    rw [show P.conveying s (t+1) f = P.promote (s+t) ρ (P.conveying s t f) from
      Subtype.ext (P.promotes_to (s+t) ρ (P.conveying s t f)).symm,← Nat.add_assoc]
    exact P.covered_promote (s+t) ρ ih

lemma covered_reflects (r : ℤ) : P.Covered s W b ≤
    Submodule.comap (aureole K j r) (P.Covered s (Tapestry.mirrorE j (markZ Λ s r) '' W) b) :=
  Submodule.span_le.mpr (by rintro f ⟨A,B,S,T,U,p⟩; exact P.accountCovered s (p.reflective P s j r))

lemma covered_travels (r : ℤ) : P.Covered s W b ≤
    Submodule.comap (P.shifts j r).toLinearMap (P.Covered s (loft (P.plenumShift s j r) W) b) :=
  Submodule.span_le.mpr (by rintro f ⟨A,B,S,T,U,p⟩; exact P.accountCovered s (p.displaced P s j r))

lemma covered_itinerary (L : List Axis) (a : Cover) (h : f∈ P.Covered s W b) :
    P.cruise L a f∈ P.Covered s (loft (P.jettyT s a L) W) b := by
  induction L with
  | nil =>
    change f∈P.Covered s (loft 0 W) b; simpa only [loft, smul_zero, add_zero, Set.image_id']
  | cons j L ih =>
    rw [P.cruise_step, AlgHom.comp_apply, show P.jettyT s a (j::L)=
      P.plenumShift s j (a j)+ P.jettyT s a L from rfl, ←loft_assoc]
    exact P.covered_travels s j _ ih

end stamps
section six_stock
open Py.Rate.LocalLimit.Papal (Weaver household)
variable (n i : ℕ) (Z : Window.Family)
local notation "F" => P.stockS Z (P.flash n)
local notation "B" => (P.flash n).patio
local notation "Y₁" => nodeC (P.flash n).birth
local notation "Y₂" => nodeC (P.flash n).death
local notation "T'" => P.advanceCount n

lemma dressedStock (A : Lead n) : (P.stockS Z A).val = Lead.sing n A.wave •
    ∑ p∈colors Z, ∑ q∈colors Z, scalar K (coilFlag A p q ∘ Prod.fst) *
      (removal K A.death (dnSpin A.slot) q * creation K A.birth (upSpin A.slot) p) := by
  change household K (A.groundWord Z) = _
  rw [banner_sum]; simp_rw [←stanza_book]
  funext m x; simp_rw [household,Pi.smul_apply,Finset.sum_apply]; rfl

/-- Equality of these exact representation identities, path trace cost, sign
and chiral `InTest` letters at each source; cf. the manuscript's (st).
`SU.Slot` vs Family: this includes the actual starting generation. -/
lemma st_price : (P.flash n).birth=(P.calibration.ℓ+n) • step 3 ∧
    (P.flash n).death=(P.flash n).birth + n • step 3 ∧
    (P.flash n).traceV=List.replicate (2*n) (posDir 3) ∧
    (P.stockS Z (P.flash n)).val = (-(n:ℂ)^3/5) •
    ∑ p∈colors Z, ∑ q∈colors Z,
      scalar K ((fun U : LinksC ↦ (matter (travel U (Y₁) (List.replicate (2*n) (posDir 3)))).val p q) ∘ Prod.fst) *
      (removal K ((P.flash n).death) 2 q * creation K ((P.flash n).birth) 0 p) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  rw [P.dressedStock, show Lead.sing n (P.flash n).wave= (-(n:ℂ)^3/5) by
    simp [flash,Lead.sing,phaseF,neg_div], show upSpin (P.flash n).slot=0 from (show upSpin 0=0 by decide),
    show dnSpin (P.flash n).slot=2 from (show dnSpin 0=2 by decide)]
  rfl

lemma stock_ribbon (A : Lead n) : (P.stockS Z A).val ∈
    Pockets.ribbon K A.patio Z.2 {nodeC A.birth} {nodeC A.death} := by
  rw [P.dressedStock]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i u ↦ Submodule.sum_mem _ (fun j v ↦ mixed_ribbon ?_ ?_)))
  · exact stamp_rl (living_letter _ _ _ _ (up_half _) (mem_singleton_self _) (congrArg Prod.snd ((mem_filter.mp u).2 : family i=Z)))
      (dying_letter _ _ _ _ (dn_half _) (mem_singleton_self _) (congrArg Prod.snd ((mem_filter.mp v).2 : family j=Z)))
  exact ⟨fun h ↦ by contradiction,(coil_paid ..).env,(coil_paid ..).locus⟩

-- explicit intra-summand **physical** price, persists. Given in double physical units
-- `(ρ-2 ℓ h_s)>ρ/2`. Only require this for Ward, via disjointness.
def StockClear : Prop := 2 * Journey.reserve P.par P.width < n
lemma stockClear_event {c r : ℕ → ℕ} (L : Launch P c r) : ∀ᶠ i:ℕ in atTop,P.StockClear (r i) :=
  L.eager.tendsto_atTop.eventually_gt_atTop _

lemma stock_separation (p : P.StockClear n) :
    ∀ x∈ϵ Y₁, ∀ y∈ϵ Y₂, x 3 + P.dew s n < y 3 := by
  let t := precisionAt Λ s
  intro x a y b
  obtain h := (abs_le.mp (a 3)).2
  obtain g := (abs_le.mp (b 3)).1
  have hp : 0<t := positiveScale Λ s
  have e : ((Y₂) (3:Axis):ℤ)= (Y₁) (3:Axis)+ 2*(n:ℤ) := by simp [flash,nodeC,kernel0]; omega
  rw [e] at g; simp only [Int.cast_add,Int.cast_ofNat,Int.cast_natCast,Int.cast_mul] at g
  change x 3+(n:ℝ)/t < y 3
  rw [← lt_sub_iff_add_lt', div_lt_iff₀ hp]
  have hx : 2*(Journey.reserve P.par P.width:ℝ)< (n:ℝ):=by exact_mod_cast p
  unfold t; linarith

lemma noOverlap_ribbon (p : P.StockClear n) : Disjoint (ϵ Y₁) (ϵ Y₂) :=
  Set.disjoint_left.mpr (fun x h v ↦ by
    have he := P.stock_separation s n p x h x v
    have hn : 0<n:= Nat.zero_le _|>.trans_lt p
    linarith [P.dew_pos s hn])

-- main labels at the initial height. Chiral pairs advance: at most mixing within one representation TYPE. Include reflection in other axes too, following the actual θ and its shift rules.
lemma start_ribbon (p : P.StockClear n) : P.RibbonAccount s (P.placard s B) (ϵ Y₁) (ϵ Y₂)
    B {Y₁} {Y₂} Z.2 (P.stockS Z (P.flash n)) := by
  refine ⟨P.stock_ribbon n Z _,P.celebrity (flourish _ _),singleton_subset_iff.mpr (porchBorn _),
    singleton_subset_iff.mpr (porchGone _),P.placard_print s B,
    (by intro x u; rw [mem_singleton.mp u]),(by intro x u; rw [mem_singleton.mp u]),
    P.placard_intro s (porchBorn _),P.placard_intro s (porchGone _),P.conform s Y₁,P.conform s Y₂,
    P.noOverlap_ribbon s n p⟩

lemma placard_mono {S T : Finset Cover} (p : S ⊆ T) : P.placard s S ⊆ P.placard s T :=
  (P.placard_spec s).1 fun i v ↦ P.placard_intro s (p v)

lemma timeCovered (p : P.StockClear n) : P.timeTest n Z∈ P.Covered s (P.placard s (P.timeSupport n)) Z.2 := by
  let A := P.placard s (P.timeSupport n)
  have ht := P.accountCovered s (P.start_ribbon s n Z p)
  refine Submodule.sub_mem _ (P.covered_bigger s (P.placard_mono s (Finset.subset_union_left
    (s₁:=B) (s₂:=plow K 3 (T':ℤ) B))) ht) ?_
  have hx : P.shifts 3 (T':ℤ) F ∈ P.Covered s (loft (P.plenumShift s 3 T') (P.placard s B)) Z.2 :=
    P.covered_travels s 3 (T':ℤ) ht
  rw [P.loft_placard] at hx
  exact P.covered_bigger s (P.placard_mono s (Finset.subset_union_right (s₁:=B))) hx

variable {b : Bool}
-- Full stamp with presentations (allows reflection compositions)
def Apron.covered (D : P.Apron) (b : Bool) := D.F ∈ P.Covered D.s (D.scenery P 0) b
lemma sixStamp (p : P.StockClear n) : Apron.covered P (P.sixBody s n Z) Z.2 :=
  (P.covered_bigger s ((P.placard_spec s).1 ((P.sixBody s n Z).efficiency P))) (P.timeCovered s n Z p)

lemma Apron.reflectCoverage (D : P.Apron) (p : D.covered P b) : (D.kiss P j).covered P b := by
  let V := D.scenery P 0
  have hv : mirrorE j (markZ Λ D.s 0) '' V ⊆ V := by
    rintro _ ⟨x,p,rfl⟩ i; have hp := p i
    change |_ - 2*0| ≤ _; by_cases h : i=j
    · simpa [mirrorE,h,markZ] using hp
    unfold mirrorE; rw [if_neg h]; exact hp
  exact P.covered_bigger D.s hv (P.covered_reflects D.s j 0 p)

lemma Apron.signedCoverage (L : List Axis) (D : P.Apron) (p : D.covered P b) :
    (L.foldr (fun j B₁ ↦ Apron.kiss P j B₁) D).covered P b := by
  induction L with
  | nil => exact p
  | cons i L ih => exact Apron.reflectCoverage P i _ ih

include ρ in
lemma pay_factor (D : P.Apron) {b : Bool} (p : D.covered P b) (t : ℕ) (h : D.s ≤ t)
    (x : Cover) : P.fieldAt t D x∈ P.Covered t (D.scenery P (P.pose t x)) b := by
  have ht := P.covered_conveying D.s ρ p (t-D.s)
  rw [Nat.add_sub_of_le h] at ht
  have hip := P.covered_itinerary t Vacancy.ordinate x ht
  rw [P.jettyT_full] at hip
  refine P.covered_bigger t (Set.Subset.trans ?_ (Set.Subset.refl _)) hip
  rintro v ⟨u,g,rfl⟩
  have hc := P.step_poses D (p:=0) (P.pose t x) (u+(2:ℕ) • P.pose t x)
    (show u+ (2:ℕ) • _ - _∈_ from (by rw [add_sub_cancel_right]; exact g))
  rwa [zero_add] at hc
end six_stock
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms st_price
#print axioms noOverlap_ribbon
#print axioms sixStamp
#print axioms Apron.reflectCoverage
#print axioms pay_factor
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
