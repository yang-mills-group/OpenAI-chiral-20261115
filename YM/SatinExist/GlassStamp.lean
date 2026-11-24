import YM.SatinExist.GlassMotion
import SatinGlasshouseFixedProbesNovember6
import SatinCommonSupportNovember6
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup
open MacroGrid Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "Λ" => P.par
local notation "V" => P.law
local notation "G" => P.history
local notation "Gt" => P.projection.clipped
local notation "W" => timeMesh P.par
local notation "C" => P.room
local notation "ξ" => P.advocate 3 x j
local notation "ζ" => P.glasshouseCharacter 3 x
local notation "χ" => P.orientHouse x j
local notation "Hi" => P.GreatRoom x j
local notation "Hz" => P.PortionHil j ξ
local notation "Hc" => P.ColorHil j ξ
local notation "Bc" => P.stateVox j ξ
local notation "Bg" => P.greatBud x j
local notation "α" => P.foyer x j
local notation "β" => P.colorRoom x j
local notation "α'" => (α).toLinearIsometry.toContinuousLinearMap
local notation "Tg" => Selected.turnstile Y H V G Gt j false (C j) χ
local notation "R″" => Selected.ride Y H V G Gt j false (C j) χ
open YM.SelectionAnalysis
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget
open FirstWindows.LightBudget.Crease
local notation "κ" => P.calibration
local notation "G'" => P.projection
local notation "Z₀" => Selected.fort Y H V G Gt j false (C j) χ
local notation "Td" => FirstWindows.ticket Y H G'
local notation "D" => FirstWindows.Domain Y H G'
local notation "I'" => FirstWindows.insideAt Λ P.width κ
local notation "Foh" => FirstWindows.Chambers.Follows Y H V G' j (C j) χ
local notation "Val" => FirstWindows.osValue Y H V G' 3 (C 3) ζ

lemma foyer_foot (S:Finset Cover)(s:ℕ) : P.pinFoot s S= FirstWindows.bufferedHull P.par P.width s S := by
  ext p; constructor
  · rintro ⟨z,e,h⟩
    refine Set.mem_iUnion₂.mpr ⟨z,e,((2:ℝ) • p),h,?_⟩
    funext i; change (2:ℝ)*p i/ 2=p i; ring
  rintro e
  obtain ⟨z,v,u,h,rfl⟩ := Set.mem_iUnion₂.mp e
  refine ⟨z,v,?_⟩
  have ht : (2:ℝ) • toMatterUnits u=u:= by ext i; change 2*(u i/2)=_; ring
  rwa [ht]

lemma pinFoyer (s:ℕ)(B:P.Test)(S:Set Vantage) : B ∈ insideAt Λ P.width κ true S s ↔
    P.asked_at s B S ∧ B∈enclave P.calibration := by
  constructor
  · intro h
    obtain ⟨⟨Z,p,q⟩,g⟩ := (mem_insideAt ..).1 h
    have ht:P.pinFoot s Z⊆ S:=by rw [P.foyer_foot]; exact (FirstWindows.supported_iff ..).1 q
    exact ⟨⟨Z,p,ht⟩,g rfl⟩
  rintro ⟨⟨Z,p,q⟩,g⟩
  refine (mem_insideAt ..).2 ⟨⟨Z,p,(FirstWindows.supported_iff ..).2 ?_⟩,fun _=>g⟩
  rwa [←P.foyer_foot]

lemma birth_foyer (s:ℕ){F:P.Test}(h:P.birthF j s F) :
    F∈ FirstWindows.insideAt Λ P.width κ true (flank j 0) s ∧
    ∃ d : D true (flank j 0),d.val= FirstWindows.ticket Y H G' s F ∧
      β (P.viewF j ξ s h)= FirstWindows.physicalKet Y H V G' j (C j) χ d := by
  obtain ⟨y,hx⟩:= h
  have hf : F∈ FirstWindows.insideAt Λ P.width κ true (flank j 0) s :=
    (positive_today Y H j s F).2 (by
      rw [←hx]; exact (purpose_ok ..).2 ⟨((purpose_ok ..).1 y.val.property).1,fun _=> y.property⟩)
  let z: insideAt Λ P.width κ true (flank j 0) s:= ⟨F,hf⟩
  let f:= FirstWindows.enclose Y H G' (flank j 0) true s z
  refine ⟨hf,f,rfl,?_⟩
  rw [P.holdsF j ξ s _ y hx, P.colorRoom_actor]
  rw [show f = FirstWindows.enclose Y H G' (flank j 0) true s z from rfl,physical_enclose]
  apply congrArg (Selected.bud Y H V s G Gt j false (C j) χ)
  apply Subtype.ext; exact congrArg (fun i : P.Test => i.val) hx

section space
local notation "Ea" k:max => P.singleState 3 k x
lemma foyer_pair (A B:P.Test)(s:ℕ)(U X:Set Vantage)(p:Disjoint U X)
    (a:A∈ insideAt Λ P.width κ true U s) (b:B∈ insideAt Λ P.width κ true X s) :
    ∃ f : D true (U∪X), f.val = Td s A * Td s B ∧
      Val (⟨f.val,domain_le_lawDomain Y H G' _ f.property⟩) = P.singleState 3 s x (A * B) := by
  have h : A*B ∈ I' true (U∪X) s :=
    Subalgebra.mul_mem _ (FirstWindows.insideAt_mono Set.subset_union_left a) (FirstWindows.insideAt_mono Set.subset_union_right b)
  let f:=FirstWindows.enclose Y H G' (U∪X) true s ⟨A*B,h⟩
  refine ⟨f,ticket_separated Y H G' a b p,?_⟩
  change Val ⟨Td s (A*B),_⟩= _
  rw [os_ticket_val]
  rfl

variable (F U : SampleDose) (A : ℕ → P.Apron) (c r n : ℕ → ℕ) (w : Lead.Clan→SatinJets.Prism)
    (Vt : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
    (g h : ℕ) (X : P.HandleWith x c r A n) {s k : ℕ} {K:P.Register}
local notation "X₋"=> reviewEarlierBox
local notation "X₊"=> reviewLaterBox
local notation "Sold"=> P.soldTrumpet A c r n w
local notation "L₁" t:max i:max a:max=> P.prepared t ((Sold a i).kiss P 3) F
local notation "L₂" t:max i:max a:max=> P.prepared t (Sold a i) U
local notation "s!" i:max => c (n i)
private lemma compact_basis (r : SampleDose)(O : Doorway)(p:tsupport r.val ⊆ O.invites) :
    ∃ ε>0, cthickening ε (tsupport r.val) ⊆ O.invites :=
  r.budget.exists_cthickening_subset_open O.doorOpen p
variable (L : P.FullPrismLab x A c r n w Vt g h X 1 F U X₋ X₊ s k K)
lemma house_location (L : P.FullPrismLab x A c r n w Vt g h X 1 F U X₋ X₊ s k K) :
    ∃ K₁ K₂ : Set Vantage, IsCompact K₁ ∧ IsCompact K₂ ∧
      tsupport F.val ⊆ K₁ ∧ tsupport U.val ⊆ K₂ ∧
      K₁⊆ X₋.invites ∧ K₂⊆ X₊.invites ∧ Disjoint K₁ K₂ ∧
      Nonempty (SpaceFor Λ K₁ K₂) ∧
      ∀ᶠ i in atTop,∀ t, s! i ≤ t → ∀ a:Lead.Clan,
        L₁ t i a∈ insideAt Λ P.width κ true K₁ t ∧ L₂ t i a∈ insideAt Λ P.width κ true K₂ t := by
  obtain ⟨ρ,v₀,f⟩:= compact_basis F _ L.supports.1
  obtain ⟨d,v₁,e⟩:= compact_basis U _ L.supports.2
  let Q:=cthickening ρ (tsupport F.val)
  let R:=cthickening d (tsupport U.val)
  have hQ:IsCompact Q:= F.budget.cthickening; have hR:IsCompact R:= U.budget.cthickening
  have ht : ∀ j:Axis, ∀ x ∈ Q, ∀ y∈R, (x j)< (y j) := fun j x p y q=>
    lt_trans (by simp:x j<x j+2) (thin_separation x y (f p) (e q) j)
  refine ⟨Q,R,hQ,hR,self_subset_cthickening _,self_subset_cthickening _, f,e,
    Set.disjoint_left.mpr (fun i a b => ?_), budget_pair _ _ P.par hQ hR ht,?_⟩
  · -- `implicit` x?
    exact (lt_irrefl _) (ht 0 _ a _ b)
  have hZ(B:P.Apron)(F : SampleDose)(ε:ℝ)(K:Set Vantage)
      (p:thickening ε (tsupport F.val) ⊆ K)(h:∀ x:Vantage,P.Aperture B x⊆ Metric.ball x ε)
      (t:ℕ)(u:B.s≤t): P.prepared t B F∈ I' true K t:= by
    obtain ⟨S,f,v⟩:= P.prepared_at t B F u
    apply (P.pinFoyer ..).2
    refine ⟨⟨S,f,v.trans ?_⟩, P.prepared_color t B F⟩
    intro x q
    obtain ⟨y,z,q⟩ := Set.mem_iUnion₂.mp q; exact p (mem_thickening_iff.mpr ⟨y,z,h y q⟩)
  filter_upwards [L.then_read.widths ρ v₀,L.then_read.widths d v₁] with i h₁ h₂ t p a
  exact ⟨hZ _ F ρ Q (thickening_subset_cthickening ..) ((h₁ a).1.1) t p,
    hZ _ U d R (thickening_subset_cthickening ..) ((h₂ a).2.1) t p⟩
end space
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
