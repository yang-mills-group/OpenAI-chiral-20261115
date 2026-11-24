import YM.SU5.MacroSix.Channel
import YM.SU5.MacroSix.TuneSelector
import YM.SU5.Relativistic.TrueSeparation

/-! # Pe path-integral reading of the macro measurements: optional far detector

(Qualified) physical interpretation at ALL these later heights in the
question. Top consultation of these probes can stay *geometry AND label*
disjoint even in this presentation reading x from the single-U signed law
by a limit. No claim that an interpreting device fulfilling the stated
perturbation (ε) budgets is required to solve such a later period/Orbit price
**uniformly** in detector, labels, Fock volume. Note:

* using the library's `atCutoff`, top means top-cutoff reading at those `k` and period indices to be
  removed INNERMOST. `taking` (many-height polynomial) has exact formula there,
  not just one for the value after path selection; when using this method detector
  itself can require multiple marks in the signal/background ratio. We're using
  precisely the library that initializes the common enrolled reading, not a
  proof of `Wallpaper` or an estimate changing the election. It's extra to the sector
  definition in `Macropositions`.
* this gives an ordered, selectable limit of those readings, with all factors'
  actual locations at the physical prices: the two requested ones disjoint,
  the extra detector can be taken in two future/past unions of footprints arbitrarily time-distant
  from them. AtCutoff too keeps these separate prices of the two requested marks and of the whole detector. This checking of
  translations/sign/character normalization is optional implementation of the
  pricing of M. Do not demand an ordinary cutoff-independent boundary mark of
  the detector. Do not compare the split (height-t singleState marginal) to
  changing raw projections of the PE detector.
* the other computation is just to stop at the character calculation on its
  generator. Doesn't require calibration of the detector at all.
-/

set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
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
open Reconstruction Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open _root_.YM.OS.Ground TopologicalSpace
namespace Spine
variable (P : Spine) (R : P.Register) (j : Axis) (c : P.Poll j)
    (s t k : ℕ) (x : P.Spectrum0 j)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "H" => P.large
local notation "N" => side P.run t (P.run.uv k)
local notation "V₀" => P.run.uv k
local notation "Ξ" => P.Effect
local notation "𝔼" s:max U:max => PolAt Y H s U
variable (U V W : Set RSpace) (i : ℕ)
def detectorBudget (i : ℕ) : Set RSpace :=
  footprint P.par P.width (c i).t (Future.opening P.run P.large j (c i)) ∪
    footprint P.par P.width (c i).t (Future.closing P.run P.large j (c i))
local notation "β" i:max => P.detectorBudget j c i
local notation "v" i:max => P.pollTicket j c i

lemma detectorGeometry : IsCompact (P.detectorBudget j c i) ∧
    P.pollTicket j c i∈ PolAt Y H (c i).t (P.detectorBudget j c i) := by
  obtain ⟨p,h⟩:= Future.picture Y H j (c i)
  have ht:{(c i).t}⊆Set.univ ∩ Set.Iic (c i).t:=by simp
  refine ⟨(footprint_compact ..).union (footprint_compact ..),?_⟩
  change Future.boundary Y H j (c i)∈ _; rw [Future.twoEnds]
  exact Subalgebra.mul_mem _ (circum_widens Y H Set.subset_union_right ht p)
    (circum_widens Y H Set.subset_union_left ht h)

lemma detectorDisjoint (u : IsCompact U) : ∀ᶠ i in atTop, Disjoint U (P.detectorBudget j c i) := by
  filter_upwards [eventually_sans Λ U j u] with i h
  obtain ⟨p₁,p₂⟩:= Future.labels_far Y H j (c i)
  exact h.mono_right (Set.union_subset_union p₁ p₂)

lemma into_cabin (p : IsCompact U) : ∃ d : ℝ, U ⊆ cabin d := by
  obtain ⟨d,h⟩ := (p.image continuous_norm).bddAbove
  exact ⟨d,fun x p i ↦ (norm_le_pi_norm x i).trans (h (Set.mem_image_of_mem _ p))⟩

local notation "ν" => prior SU.group (More (side P.run t (P.run.uv k)))
local notation "F₀" i:max => Reconstruction.atCutoff P.run P.large t k i
local notation "I₀" => bareAmplitude Y t k
local notation "t₀" a:max b:max => taking Y H a b
local notation "t₁" a:max b:max => Reconstruction.readingAtTop Y H a b

def FootBill (F : P.Effect) (S : Finset Cover) :=
  covariant (toMark (F₀ F)) ∧ SupportedPhysically P.par P.width (P.run.uv k) S U ∧
    AtSupport false (Satin.region S (side P.run t (P.run.uv k))) (toMark (F₀ F))

structure TopBill (L G F : P.Effect) : Prop where
  paid : P.PaidPe (P.run.uv k) t k
  footprints : ∃ S₁ S₂ S₃ : Finset Cover,
    P.FootBill t k U L S₁ ∧ P.FootBill t k V G S₂ ∧ P.FootBill t k W F S₃ ∧
      FullDistances (S₁∪S₂∪S₃) (side P.run t (P.run.uv k))
  duo : atCutoff Y H t k (L*G)= (F₀ L)*(F₀ G)
  full : atCutoff Y H t k (L*G*F)=(F₀ L)*(F₀ G)*(F₀ F)
  partition : (∫ x, I₀ 1 x ∂ν) ≠ 0
  integrable_base : Integrable (I₀ 1) ν
  signal : (t₀ t k) (L*G*F)=
    (∫ U : Pane N, I₀ ((F₀ L)*(F₀ G)*(F₀ F)) U ∂ν)/(∫ x, I₀ 1 x ∂ν)
  denominator : (t₀ t k) F=
    (∫ U : Pane N, I₀ (F₀ F) U ∂ν)/(∫ x, I₀ 1 x ∂ν)
  integrablePair : Integrable (I₀ ((F₀ L)*(F₀ G)*(F₀ F))) ν ∧ Integrable (I₀ (F₀ F)) ν

variable (L G F : P.Effect)

lemma TopBill.same_numerator (B : P.TopBill t k U V W L G F) :
    ∫ u, I₀ ((F₀ L)*(F₀ G)*(F₀ F)) u ∂ν =
       (∫ u, I₀ (F₀ (L*G*F)) u ∂ν) := by rw [B.full]

/-- Pair specifically two observations and one detector read. If detector itself consists of
subobservations may also use `pairAtCutoff` and `atTop_flavor` on those labels on the same
paid physical set, before switching to any limiting value. -/
lemma pe_bill_of (X : IsCompact (U∪V∪W))(a : L∈ PolAt Y H s U)(b : G∈ PolAt Y H s V)
    (d : F∈PolAt Y H s W)(e : Disjoint U V)(g : Disjoint (U∪V) W) :
    ∀ᶠ t in atTop, ∀ k, Pay Y s t k → P.TopBill t k U V W L G F := by
  obtain ⟨d',X'⟩:= into_cabin _ X
  have hx : U∪V⊆ Tapestry.cabin d':= Set.Subset.trans Set.subset_union_left X'
  have hw : W⊆ Tapestry.cabin d':= Set.Subset.trans Set.subset_union_right X'
  have hy := Set.Subset.trans (Set.subset_union_left (s:=U) (t:=V)) hx
  have hz := Set.Subset.trans (Set.subset_union_right (s:=U) (t:=V)) hx
  let B:=U∪V
  have hp : L*G∈PolAt Y H s B := (PolAt Y H s B).mul_mem ((isotone Y H Set.subset_union_left) a)
    ((isotone Y H Set.subset_union_right) b)
  have hb : L*G*F∈PolAt Y H s (U∪V∪W) := (PolAt Y H s _).mul_mem
    ((isotone Y H Set.subset_union_left) hp) ((isotone Y H Set.subset_union_right) d)
  filter_upwards [wide_calendar Y d'] with t q k
  intro p
  let ν' := prior SU.group (More (side Y t (P.run.uv k)))
  let Q := atCutoff Y H t k
  have ht : Q (L*G) = Q L*Q G := pairAtCutoff Y H t k s q hy hz e Set.univ Set.univ
    ((well_spec ..).1 a).1 ((well_spec ..).1 b).1 p
  have hq: Q (L*G*F)=Q L*Q G*Q F := (pairAtCutoff Y H t k s q hx hw g Set.univ Set.univ
    ((well_spec ..).1 hp).1 ((well_spec ..).1 d).1 p).trans (congrArg (fun x ↦ x*(Q F)) ht)
  obtain ⟨π,h',c⟩:= identifyRevenue Y H t k s (inside_budget Y H hb) p
  obtain ⟨δ,-,c'⟩:= identifyRevenue Y H t k s (inside_budget Y H d) p
  let T := bareAmplitude Y t k
  let S := Q L*Q G*Q F
  refine ⟨P.account_pe ⟨p.1, le_rfl⟩,?_,ht,hq,h',(partitionIncome Y t k p.1).1,
    c.trans (congrArg (fun A ↦ (∫ x,T A x ∂ν')/(∫ x,T 1 x ∂ν')) hq),c',hq ▸ π,δ⟩
  obtain ⟨U',p₁,e',f,-⟩:= P.atTop_flavor t k s _ a p
  obtain ⟨V',p₂,a₁,b₁,-⟩:= P.atTop_flavor t k s _ b p
  obtain ⟨W',p₃,a₂,b₂,-⟩:= P.atTop_flavor t k s _ d p
  refine ⟨U',V',W',⟨f,p₁,e'⟩,⟨b₁,p₂,a₁⟩,⟨b₂,p₃,a₂⟩,unwrap Y t d' q _ _ ?_⟩
  intro i h
  rcases Finset.mem_union.mp h with y | y
  · rcases Finset.mem_union.mp y with z|z; exact hy (p₁.contains z); exact hz (p₂.contains z)
  exact hw (p₃.contains y)

local notation "μ" x:max => P.period (WedgeStage.vol x)
local notation "η" x:max => P.cutoff (WedgeStage.uv x)

/-- User-level statement. We may hold both `j,c` selector and property of M, and PE funding
path before poses as in the theorem. Late detector, then late inner consultation; still
these same two costs. -/
structure PricePaid : Prop where
  valuation : Tendsto (fun i ↦ P.RatioOn R j c i (L*G)) atTop (𝓝 (P.spirits R j x (L*G)))
  detector : ∀ᶠ i in atTop, let F:=P.pollTicket j c i
    let W:=P.detectorBudget j c i
    s≤ (c i).t ∧ F∈ PolAt Y H (c i).t W ∧ Disjoint (U∪V) W ∧
    (∀ᶠ n in followStage, Pay P.run (c i).t (μ n) (η n) ∧
      P.TopBill (μ n) (η n) U V W L G F ∧ taking P.run P.large (μ n) (η n) F ≠ 0 ∧
       (∫ x,bareAmplitude Y (μ n) (η n) (atCutoff Y H (μ n) (η n) F) x ∂prior SU.group (More (side Y (μ n) (P.run.uv (η n))))) ≠ 0) ∧
    Tendsto (fun n ↦ (t₀ (μ n) (η n)) (L*G*F) / (t₀ (μ n) (η n)) F)
       followStage (𝓝 (P.RatioOn R j c i (L*G)))

lemma Selects.pairsCost {U V}
    (C : P.Selects R j x c) (a : L∈PolAt Y H s U)(b : G∈ PolAt Y H s V)(p : IsCompact U)(q : IsCompact V)
    (d : Disjoint U V) : P.PricePaid R j c s x U V L G := by
  let F₁:= (L*G)
  let Q:= (C.poll F₁ s ((shorter P.Test s).mul_mem (inside_budget Y H a) (inside_budget Y H b)))
  refine ⟨Q.1,?_⟩
  let X:= U∪V
  filter_upwards [P.detectorDisjoint j c X (p.union q),Q.2] with i he h
  let hp:s≤(c i).t:= h.1
  intro f w
  have hv:=P.detectorGeometry j c i
  let Pcut:=P.run.uv
  have ht := P.pe_bill_of (c i).t U V (β i) L G (P.pollTicket j c i) ((p.union q).union hv.1)
    (polAt_up Y H hp a) (polAt_up Y H hp b) hv.2 d he
  have hw:Tendsto (fun n ↦ μ n) followStage atTop := P.law.pick.grow_i.tendsto_atTop.comp overStage
  let T (n : WedgeStage) := t₀ (μ n) (η n)
  have hn:= ((shorter P.Test _).mul_mem (Altitude.climbs P.Test hp ((shorter P.Test _).mul_mem
    (inside_budget Y H a) (inside_budget Y H b))) (inside_budget Y H hv.2))
  refine ⟨hp,hv.2,he,?_,?_⟩
  · filter_upwards [hw.eventually ht,h.2.2.1] with n t p
    let A:= t _ p.1
    let B₀:= Reconstruction.readingAtTop Y H (μ n) (η n)
    have hy : T n f=B₀ f:=(identifyRevenue Y H _ _ _ (inside_budget Y H hv.2) p.1).2.2
    refine ⟨p.1,A,(hy.symm ▸ p.2: T n f≠0),fun r ↦ ?_⟩
    apply p.2
    exact div_eq_zero_iff.mpr (Or.inl r)
  refine h.2.2.2.congr' (h.2.2.1.mono fun n q ↦ ?_)
  exact congrArg₂ (HDiv.hDiv (γ:=ℂ)) (identifyRevenue Y H (μ n) (η n) _ hn q.1).2.2.symm
    (identifyRevenue Y H (μ n) (η n) _ (inside_budget Y H hv.2) q.1).2.2.symm

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms pe_bill_of
#print axioms Selects.pairsCost
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
