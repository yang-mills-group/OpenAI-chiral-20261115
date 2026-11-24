import YM.SU5.Same.CardOperators

/-!
# On the elected thin character: registration on the CP27 determining Mark system

Show the WithTicket operator and ket identifications for the actual CP18 choices. Relaxed
Wick/projected reading when using BoostBacking/Registered criteria discussed separately. Here
just the actual Mark budgets, axes match and support, estimates **without** such assumptions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
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
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

variable (P : Spine)

lemma glassInside_prepared (X : Finset Cover) (t : ℕ) (B : P.Apron) (F : SampleDose)
    (e : Charm.Locator P.calibration (P.azurePrepared t B F) X) :
    P.prepared t B F ∈ insideAt P.par P.width P.calibration true (P.pinFoot t X) t := by
  rw [mem_insideAt]
  exact ⟨⟨X, e, P.usual_footprint t X ▸ Tower.Reconstruction.has_footprint P.par P.width t X⟩,
    fun _ => (enclave_spec P.calibration).mp (P.prepared_color t B F)⟩
lemma pinFoot_isCompact (X : Finset Cover) (t : ℕ) : IsCompact (P.pinFoot t X) :=
  P.usual_footprint t X ▸ Tower.Reconstruction.footprint_compact ..

local notation "j" => (3:Axis)
local notation "C'" => reviewEarlierBox
local notation "B'" => reviewLaterBox
local notation "Λ" => mirrorE (3:Axis) (0:ℝ)
lemma mirrorE_origin_continuous (k : Axis) : Continuous (mirrorE k 0) := by
  refine continuous_pi fun i=> ?_
  by_cases h : i = k
  · subst i; simp only [mirrorE, ↓reduceIte]; fun_prop
  simp only [mirrorE, if_neg h]; exact continuous_apply _

variable (x : P.Spectrum0 3) (A : ℕ → P.Apron) (c r n : ℕ → ℕ)
    (w : Lead.Clan → Prism) (F U : SampleDose)
local notation "W₁" a:max i:max => (((P.soldTrumpet A c r n w) a i).kiss P 3)
local notation "W₂" b:max i:max => ((P.soldTrumpet A c r n w) b i)
local notation "f₁" t:max a:max i:max => P.prepared t (W₁ a i) F
local notation "f₂" t:max a:max i:max => P.prepared t (W₂ a i) U
local notation "ξ" => P.advocate 3 x 3
local notation "K" => P.calibration
local notation "S" => P.ColorHil j ξ
local notation "S'" => P.ManyF 3 ξ
local notation "R" => P.glassSpace 3 x 3

variable (T' : P.HandleWith x c r A n)
local notation "Z" a:max i:max => P.sold_birth x A c r n w a i T'
local notation "x₁" t:max a:max i:max => P.thinGridKet x t (W₂ a i) (Z a i) (flipDose F j)
local notation "x₂" t:max b:max i:max => P.thinGridKet x t (W₂ b i) (Z b i) U
local notation "Yc" t:max V:max => insideAt P.par P.width P.calibration true V t

/-- A capsule inside the fixed boxes, taking the earlier stencil as reflection to
positive time for preparing the bra. Not granting a rotation of either box. The
positive-time ket readings are **in the full, unprojected `glassSpace`**. -/
structure GlassTicketPair (a b : Lead.Clan) (d : marks (timeMesh P.par)) (i t : ℕ)
    (X Y : Finset Cover) (O M' : (R).Op) : Prop where
  leftLoc : Charm.Locator P.calibration (P.azurePrepared t (W₁ a i) F) X
  rightLoc : Charm.Locator P.calibration (P.azurePrepared t (W₂ b i) U) Y
  leftSupport : P.pinFoot t X ⊆ (C').invites
  rightSupport : P.pinFoot t Y ⊆ (B').invites
  leftReady : f₁ t a i ∈ Yc t (P.pinFoot t X)
  rightReady : f₂ t b i ∈ Yc t (P.pinFoot t Y)
  leftMark : P.WithTicket 3 x 3 (Λ '' (P.pinFoot t X)) d t (P.reflectTest 3 (f₁ t a i))
    (x₁ t a i) O
  rightMark : P.WithTicket 3 x 3 (P.pinFoot t Y) d t (f₂ t b i) (x₂ t b i) M'
  paid : (P.azurePrism x A c r n w F U i t) a b =
    inner ℂ (O (P.glassVac 3 x 3)) (M' (P.glassVac 3 x 3))
  centered_l : inner ℂ (P.glassVac 3 x 3) (O (P.glassVac 3 x 3)) = 0
  centered_r : inner ℂ (P.glassVac 3 x 3) (M' (P.glassVac 3 x 3)) = 0

variable (V : ∀ z : Axis, List Axis → ℝ → P.ColorHil z (P.advocate 3 x z))
    (g h : ℕ) {μ : ℝ} {s k : ℕ} {K' : P.Register}
variable (D : P.FullPrismLab x A c r n w V g h T' μ F U reviewEarlierBox reviewLaterBox s k K')
local notation "m!" i:max => c (n i)
include D

private lemma glassPermit (d : marks (timeMesh P.par)) (p : (2:ℝ) ≤ d) (i t : ℕ) (z : m! i ≤ t)
    (a b : Lead.Clan) (X Y : Finset Cover) (e : Charm.Locator P.calibration (P.azurePrepared t (W₁ a i) F) X)
    (e' : Charm.Locator P.calibration (P.azurePrepared t (W₂ b i) U) Y)
    (q : P.pinFoot t X ⊆ (C').invites) (q' : P.pinFoot t Y ⊆ (B').invites)
    (E : P.ThinSeam x (W₂ a i) (W₂ b i) (Z a i) (Z b i) F U) :
    ∃ O M', P.GlassTicketPair x A c r n w F U T' a b d i t X Y O M' := by
  let v := P.glassInside_prepared X t (W₁ a i) F e
  let v' := P.glassInside_prepared Y t (W₂ b i) U e'
  let A' := f₁ t a i
  let B₀ := f₂ t b i
  let Aplus := P.reflectTest 3 A'
  let Q := Λ '' (P.pinFoot t X)
  let W := P.pinFoot t Y
  have ht : Q ⊆ Chambers.strip j 0 d := by
    rintro _ ⟨y,t,rfl⟩
    obtain ⟨a,b⟩ := q t j (Set.mem_univ _)
    have hx : y 3 < -1 := b
    have hu : -2 < y 3 := a
    change 0 ≤ _ ∧ _ ≤ _
    simp only [mirrorE,↓reduceIte,mul_zero,zero_sub]; constructor <;> linarith
  have hu : W ⊆ Chambers.strip j 0 d := by
    intro w p'
    obtain ⟨a,b⟩ := q' p' j (Set.mem_univ _)
    exact ⟨le_trans zero_le_one (show (1:ℝ)≤ _ from a.le), le_trans b.le p⟩
  have hz : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_two p
  obtain ⟨k,hk,b1,h1⟩ := E.earlier t z
  obtain ⟨b2,h2⟩ := E.laterK t z
  have hy : Aplus = k := by change P.reflectTest 3 (f₁ t a i)= k; rw [←hk]; exact aureoleTwice ..
  have e1 : P.birthF j t Aplus := hy.symm ▸ b1
  have h1 : P.viewF j ξ t e1 = x₁ t a i := (P.identical_F j ξ t e1 b1 hy).trans h1
  have h₂ : P.viewF j ξ t b2 = x₂ t b i := h2
  have z1 : P.singleState j t x Aplus = 0 := by
    have h := (P.common_reading t x A' j).2.2.1
    change P.singleState j t x Aplus = _ at h
    rw [(show P.singleState j t x A' = 0 from (D.then_read.bothZero a i t z).1),star_zero] at h
    exact h
  have z2 : P.singleState j t x B₀ = 0 := (D.then_read.bothZero b i t z).2
  obtain ⟨O,hX⟩ := P.can_ticket 3 x j Q d t Aplus (mirror_inside P.run P.large j A' t v) ht hz e1
  obtain ⟨M',hY⟩ := P.can_ticket 3 x j W d t B₀ v' hu hz b2
  refine ⟨O,M',e,e',q,q',v,v',h1 ▸ hX,h₂ ▸ hY,?_,?_,?_⟩
  · rw [←hX.hit,←hY.hit,h1,h₂,LinearIsometryEquiv.inner_map_map, P.fullPrism_azure_actual x A c r n w V g h T' F U D i t z]
    exact E.raw t z z
  · rw [←hX.hit,←P.toGlass_vacuum 3 x j,LinearIsometryEquiv.inner_map_map,P.view_scalar,P.single_agrees]
    exact z1
  rw [←hY.hit,←P.toGlass_vacuum 3 x j,LinearIsometryEquiv.inner_map_map,P.view_scalar,P.single_agrees]
  exact z2

/-- The Glasshouse budget is available **inside either requested finite locator**
and inside the two fixed Euclidean boxes. The strip duration for both budgets can be fixed
before refining, not re-choosing a phase. -/
lemma glassPermit_finer (d : marks (timeMesh P.par)) (p : (2:ℝ) ≤ d) :
    ∀ᶠ i in atTop, ∀ t : ℕ, m! i ≤ t → ∀ (a b : Lead.Clan) (X Y : Finset Cover),
    Charm.Locator P.calibration (P.azurePrepared t (W₁ a i) F) X →
    Charm.Locator P.calibration (P.azurePrepared t (W₂ b i) U) Y →
      ∃ (O M' : (R).Op) (X' Y' : Finset Cover), X' ⊆ X ∧ Y' ⊆ Y ∧
        P.GlassTicketPair x A c r n w F U T' a b d i t X' Y' O M' := by
  filter_upwards [P.fullPrism_azure_common_boxes x A c r n w V g h T' F U D, D.then_read.epoch]
    with i hi q t v a b X Y pX pY
  obtain ⟨X',Y',f₀,f₁',s',u⟩ := hi t v a b X Y pX pY
  obtain ⟨O,M',hO⟩ := P.glassPermit x A c r n w F U T' V g h D d p i t v a b (X'∩X) (Y'∩Y)
    f₀ f₁' s' u (q a b)
  exact ⟨O,M',X'∩X,Y'∩Y,Finset.inter_subset_right,Finset.inter_subset_right,hO⟩

/-- Freestanding actual existence of those budgets at any such fixed common strip time. -/
lemma glassPermit_all (d : marks (timeMesh P.par)) (p : (2:ℝ) ≤ d) :
    ∀ᶠ i in atTop, ∀ t : ℕ, m! i ≤ t → ∀ a b : Lead.Clan,
      ∃ (O M' : (R).Op) (X Y : Finset Cover),
        P.GlassTicketPair x A c r n w F U T' a b d i t X Y O M' := by
  filter_upwards [P.fullPrism_azure_boxes x A c r n w V g h T' F U D,
    P.glassPermit_finer x A c r n w F U T' V g h D d p] with i box useF t v a b
  obtain ⟨X,Y,pX,pY,_⟩ := box t v a b
  obtain ⟨O,M',X',Y',_,_,e⟩ := useF t v a b X Y pX pY
  exact ⟨O,M',X',Y',e⟩

local notation "ι₂" => P.fortIn 3 x j
local notation "R'" => P.glassFort 3 x j
local notation "Ω" => P.glassVac 3 x j
local notation "X!" z:max => DoseTravel.beam (S') F (P.earlierProfile x V w μ z)
local notation "Y!" z:max => DoseTravel.beam (S') U (P.laterProfile x V w μ z)
local notation "ζ" => P.toFort 3 x j

/-- Even strong (norm) convergence in the CP27 (loose Mark) GNS, on the diagonal
schedules of CP18. Hence in principle a route to corresponding Wick programs; still
no operator norm or even matrix-element convergence as operators, and no Poincaré/locality conclusion. -/
theorem glassPair_limit (d : marks (timeMesh P.par)) (t : ℕ → ℕ) (a b : Lead.Clan)
    (O M' : ℕ → (R).Op) (p : ∀ᶠ i in atTop, m! i ≤ t i) (u : ∀ᶠ i in atTop,
      ∃ X Y, P.GlassTicketPair x A c r n w F U T' a b d i (t i) X Y (O i) (M' i)) :
    Tendsto (fun i => O i Ω) atTop (𝓝 (ι₂ (ζ (X! a)))) ∧
    Tendsto (fun i => M' i Ω) atTop (𝓝 (ι₂ (ζ (Y! b)))) ∧
    inner ℂ (ι₂ (ζ (X! a))) (ι₂ (ζ (Y! b))) = P.readPrism x V w μ F U a b := by
  let g' := (P.toGlass 3 x j)
  have eq (y : S') : ι₂ (ζ y) = g' (P.enter j ξ y) := rfl
  refine ⟨?_,?_,?_⟩
  · rw [eq]; refine ((g'.continuous.tendsto _).comp (D.then_read.bothM a t p).1).congr'
      (u.mono fun i u => ?_)
    obtain ⟨X,Y,e⟩ := u; exact e.leftMark.hit
  · rw [eq]; refine ((g'.continuous.tendsto _).comp (D.then_read.bothM b t p).2).congr'
      (u.mono fun i u => ?_)
    obtain ⟨X,Y,e⟩ := u; exact e.rightMark.hit
  rw [LinearIsometry.inner_map_map,LinearIsometryEquiv.inner_map_map]; rfl

#print axioms glassPermit_all
#print axioms glassPair_limit
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
