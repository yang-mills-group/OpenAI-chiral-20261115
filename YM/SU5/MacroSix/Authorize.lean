import YM.SU5.MacroSix.Ceremony
/-!
# Supplement: actual normalized signed consultation order at the elected vacuum

For specificity if wanting to work the `t:trans6` prices all the way to primitive
`Journey.sharp`/`compass` readings. In particular not replacing the character by a family
of marks on different periods. The `PricePaid` check already grants this on the sector law.
We assemble some additional statements making clear the realizability and **order** of all
those physical measurements and the signal. Even if using the far detector,
`Pay, Support, Poll`, preservation of the footprints and priceability with the **original Pe**
labels (and association with the expression in terms of one SU configuration
at the top) at all these heights, are simultaneous.
These facts are optional for the character's definition or use; no ratio definition is needed
in e.g. the Ward prediction, or in defining the response tests. We're not changing the
normalization ground reading or asserting any convergence of a moving-height sequence of
bare measurements on the contour ALONE while reading the character.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option maxRecDepth 3600
set_option synthInstance.maxSize 28000
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
open Reconstruction PhaseChoice Tapestry.Altitude Tapestry.Exhibition
open Aria Pockets
open _root_.YM.MacroSix
namespace Spine
variable (P : Spine) (R : P.Register) (s t n : ℕ) (f g : Vantage→ℝ)
    (c : P.Poll 3) (x : P.Spectrum0 3) (J : P.Ellis 3 x) (p v : ℕ)
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "K"=> P.calibration
local notation "P₁"=> P.detectorBudget
local notation "ν"=> taking Y H p v
local notation "κ" a:max=> (Journey.side Y p a)
local notation "A" a:max=> breathing Y H a p v
variable (F G D : P.Effect) (U₁ V W : Set RSpace)


-- break into opaque contracts (keeps kernel reduction costs down on this history's data).
structure TorCare (S : Finset Cover) : Prop where
  there : SupportedPhysically P.par P.width s S U₁
  supported : AtSupport false (Satin.region S (κ s)) (attire ((A s) F))
  upright : covariant (attire ((A s) F))
  readable : taking P.run P.large p v F = Journey.compass P.run p v s (attire ((A s) F))

private lemma care_at (h: F∈PolAt Y H s U₁)(j : Pay Y s p v) :∃ S,P.TorCare s p v F U₁ S := by
  obtain ⟨T,hp,w⟩:= breathing_location Y H s ((well_spec ..).1 h).1
  exact ⟨T,hp,w p v j, paid_coherence Y H p v s j F h (inside_budget Y H h),
    taking_phys Y H s p v F j (inside_budget Y H h)⟩

structure Sewn : Prop where
  together : ∃ S₁ S₂ S₃, P.TorCare s p v F U₁ S₁ ∧ P.TorCare s p v G V S₂ ∧
    P.TorCare s p v D W S₃ ∧ FullDistances (S₁∪S₂∪S₃) (κ s)
  breathe : (A s) (F*G*D)= (A s) F * (A s) G * (A s) D
  pair : (A s) (F*G)= (A s) F * (A s) G
  triple : taking P.run P.large p v (F*G*D)=Journey.compass Y p v s (attire ((A s) F) *
    attire ((A s) G) * attire ((A s) D))
  double : taking P.run P.large p v (F*G)=Journey.compass Y p v s (attire ((A s) F) * attire ((A s) G))
private lemma torn (p': (A s) (F*G*D)= (A s) F * (A s) G * (A s) D)(p₀ : F*G*D∈ boardedDB K s) (v₀ : Pay Y s p v) :
    taking P.run P.large p v (F*G*D)=Journey.compass Y p v s (attire ((A s) F) * attire ((A s) G) * attire ((A s) D)) :=
  let Z₁:= Journey.compass Y p v s
  let Y₁:=(A s) F
  let W₁:=(A s) G
  let T:=(A s) D
  (taking_phys Y H s p v _ v₀ p₀).trans ((congrArg (fun x=> Z₁ (attire x)) p').trans (congrArg Z₁
    ((attire_mul (Y₁*W₁) T).trans (congrArg (fun x=> x*attire T) (attire_mul Y₁ W₁)))))
private lemma at_level (d' : ℝ) (hZ : U₁∪V∪W ⊆ Tapestry.cabin d') (a : F∈ PolAt Y H s U₁)
    (b : G∈PolAt Y H s V)(d : D∈ PolAt Y H s W)(e : Disjoint U₁ V)(q : Disjoint (U₁∪V) W)
    (g : Pay Y s p v)(t : GrowsPast Y p d') : P.Sewn s p v F G D U₁ V W := by
  have hx : U₁∪V⊆ Tapestry.cabin d':= Set.Subset.trans Set.subset_union_left hZ
  have hw : W⊆ Tapestry.cabin d':= Set.Subset.trans Set.subset_union_right hZ
  have hy := Set.Subset.trans (Set.subset_union_left (s:=U₁) (t:=V)) hx
  have hz := Set.Subset.trans (Set.subset_union_right (s:=U₁) (t:=V)) hx
  have hp : F*G∈PolAt Y H s (U₁∪V) := (PolAt Y H s _).mul_mem ((isotone Y H Set.subset_union_left) a)
    ((isotone Y H Set.subset_union_right) b)
  let a₀:= ((well_spec ..).1 a).1
  let b₀:= ((well_spec ..).1 b).1
  let f₀:= ((well_spec ..).1 d).1
  let B₁ : P.Effect →ₗ[ℂ] Tapestry.Ward (κ s) := A s
  have he : B₁ (F*G)= B₁ F* B₁ G:= pair_breathing Y H p v s t hy hz e Set.univ Set.univ a₀ b₀ g
  have hu:B₁ (F*G*D)=B₁ F*B₁ G*B₁ D:=
    (pair_breathing Y H p v s t hx hw q Set.univ Set.univ ((well_spec ..).1 hp).1 f₀ g).trans
      (congrArg (fun r=> r*B₁ D) he)
  let f' := inside_budget Y H hp
  refine ⟨?_,hu,he,P.torn s p v F G D hu ((boardedDB K s).mul_mem f' (inside_budget Y H d)) g,?_⟩
  · obtain ⟨U,h₁⟩:= care_at P s p v F U₁ a g
    obtain ⟨V',h₂⟩:= care_at P s p v G V b g
    obtain ⟨W',h₃⟩:= care_at P s p v D W d g
    refine ⟨U,V',W',h₁,h₂,h₃,unwrap Y p d' t s _ ?_⟩
    intro i k; rcases Finset.mem_union.mp k with y | y
    · rcases Finset.mem_union.mp y with z|z; exact hy (h₁.there.contains z); exact hz (h₂.there.contains z)
    exact hw (h₃.there.contains y)
  exact (taking_phys Y H s p v _ g f').trans
    (congrArg (Journey.compass Y p v s) ((congrArg attire he).trans (attire_mul (B₁ F) (B₁ G))))

/-- For late enough period, at any *paid* cutoff for that depth: verify
support qualifications in the tor Mark prescription, along the course's
successive physical interior heights between the **highest ingredient's height**
and the top level. (The lemma below will also use this from the height of the
measurement just for the pair with no detector relative to any further regulator. `TopBill`
itself is at the top for the presentation by one-U reading.) -/
structure DepthBill : Prop where
  valid : P.PaidPe s p v
  sewn (i : ℕ) (h : i∈ Set.Icc s (P.run.uv v)) : P.Sewn i p v F G D U₁ V W
lemma depthBill_of (X : IsCompact (U₁∪V∪W)) (a : F∈ PolAt Y H s U₁)(b : G∈PolAt Y H s V)
    (d : D∈ PolAt Y H s W)(e : Disjoint U₁ V)(q : Disjoint (U₁∪V) W) :
    ∀ᶠ p in atTop, ∀ v, Pay Y s p v → P.DepthBill s p v F G D U₁ V W := by
  obtain ⟨d',X'⟩:= into_cabin _ X
  filter_upwards [wide_calendar Y d'] with p t v u; exact ⟨P.account_pe u, fun i z ↦
    P.at_level i p v F G D U₁ V W d' X' (polAt_up Y H z.1 a) (polAt_up Y H z.1 b)
      (polAt_up Y H z.1 d) e q ⟨u.1,z.2⟩ t⟩

section
local notation "b'" a:max=> ((P.sixBody s n a).kiss P 3)
local notation "b" a:max=> P.sixBody s n a
local notation "f'" z:max=> P.smearField t f ((P.sixBody s n z).kiss P 3)
local notation "g'" z:max=> P.smearField t g (P.sixBody s n z)
-- include args at use of `Field` when clarity.
local notation "A₁" z:max=> P.slotHole t (f' z)
local notation "A₂" z:max=> P.slotHole t (g' z)
local notation "W₁" z:max=> P.occupiedSpace f ((P.sixBody s n z).kiss P 3)
local notation "W₂" z:max=> P.occupiedSpace g (P.sixBody s n z)
local notation "π" i:max=> P.detectorBudget 3 c i
local notation "δ" i:max=> P.pollTicket 3 c i
local notation "p₀" i:max=> P.period (WedgeStage.vol i)
local notation "v₀" i:max=> P.cutoff (WedgeStage.uv i)
local notation "μ" i:max=> taking P.run P.large (p₀ i) (v₀ i)
local notation "e'" i:max=> P.RatioOn R 3 c i

variable (d : ℕ) (p' : WedgeStage)
/-- Matrix of normalized signed readings at the observing mesh and the period/cutoff
cone evaluator; INDEX order in the volume pickup here is important. May equally use
Journey.compass (all these actual interior heights) or `readingAtTop`, see `Participates`
at any probing frame. And to measure in the selected component: take sector limit here
with the above fixed before it, i.e. first `p'` argument (`WedgeStage`) goes
inner, then detector d. The **main** measurement at increasing resolution t observes
these prices, removing t last. -/
def primitiveObservation (t s n : ℕ) (f g : Vantage→ℝ) (c : P.Poll 3) (d : ℕ) (p' : WedgeStage) :
    Matrix Window.Family Window.Family ℂ := Matrix.of fun z w ↦
      (μ p') (P.slotHole t (P.smearField t f ((P.sixBody s n z).kiss P 3)) *
        P.slotHole t (P.smearField t g (P.sixBody s n w)) * P.pollTicket 3 c d) /
        (μ p') (P.pollTicket 3 c d)

def predictionAt (t s n : ℕ) (f g : Vantage→ℝ) (c : P.Poll 3) (d : ℕ) :
    Matrix Window.Family Window.Family ℂ:= Matrix.of fun z w ↦ P.RatioOn R 3 c d
      (P.slotHole t (P.smearField t f ((P.sixBody s n z).kiss P 3)) *
        P.slotHole t (P.smearField t g (P.sixBody s n w)))

-- both before, and if selecting by the detector, with the detector. Program for every clan in the measurement.
structure Participates : Prop where
  kernelPhase : t≤ (c d).t
  pays : Pay Y (c d).t (p₀ p') (v₀ p')
  compatriots (z w : Window.Family) : P.DepthBill t (p₀ p') (v₀ p') (A₁ z) (A₂ w) 1
    (W₁ z) (W₂ w) ∅
  enrolled (z w : Window.Family) : Disjoint (W₁ z ∪ W₂ w) (π d) ∧
    P.TopBill (p₀ p') (v₀ p') (W₁ z) (W₂ w) (π d) (A₁ z) (A₂ w) (δ d) ∧
    P.DepthBill (c d).t (p₀ p') (v₀ p') (A₁ z) (A₂ w) (δ d) (W₁ z) (W₂ w) (π d)
  factored (z w : Window.Family)(B : Pay Y (c d).t (p₀ p') (v₀ p')) :
    (μ p') (A₁ z * A₂ w * δ d) = Reconstruction.readingAtTop Y H (p₀ p') (v₀ p') (A₁ z * A₂ w * δ d)
  activated : (μ p') (δ d) = Reconstruction.readingAtTop Y H (p₀ p') (v₀ p') (δ d) ∧ (μ p') (δ d) ≠ 0

variable (a : P.Selects R 3 x c) (h : P.Consult R s t n f g x)
local notation "C₀" i:max y:max => P.primitiveObservation t s n f g c i y
local notation "C₁" i:max=> P.predictionAt R t s n f g c i
include a h
lemma Consult.actualObservation :
    Tendsto (fun d ↦ P.predictionAt R t s n f g c d) atTop (𝓝 (P.measureAt s n t f g x)) ∧
    ∀ᶠ d in atTop, (∀ᶠ p in followStage,P.Participates s t n f g c d p) ∧
      Tendsto (fun p ↦ P.primitiveObservation t s n f g c d p) followStage (𝓝 (C₁ d)) := by
  have p (i j:Window.Family):= h.receives c a i j
  obtain ⟨y,m⟩:= h.frame
  refine ⟨entry_tendsto _ _ _ (fun i j ↦ ?_),?_⟩
  · have he := h.seen i j
    rw [he]; exact (p i j).valuation
  filter_upwards [Filter.eventually_all.mpr (fun z:Window.Family ↦ Filter.eventually_all.mpr
    (fun j:Window.Family ↦ (p z j).detector))] with d He
  constructor
  · have hv : Tendsto (fun p : WedgeStage ↦ p₀ p) followStage atTop:= P.law.pick.grow_i.tendsto_atTop.comp overStage
    let Q':Window.Family := (0,false)
    have hk (i j:Window.Family):= (He i j).2.2.2.1
    have t₀ : t≤ (c d).t:= (He Q' Q').1
    let p₁ (i j:Window.Family) := m.pe_gap i j
    let V₁ (i:Window.Family):= (m.left i).1
    let V₂ (i:Window.Family):= (m.right i).1
    let U i:=(h.marks i).2.2.1; let V i:=(h.marks i).2.2.2
    filter_upwards [Filter.eventually_all.mpr (fun i ↦ Filter.eventually_all.mpr (hk i)),
      Filter.eventually_all.mpr (fun i:Window.Family ↦ Filter.eventually_all.mpr (fun j:Window.Family ↦
        (hv.eventually (P.depthBill_of _ _ _ _ _ _ _ ((V₁ i|>.union (V₂ j)).union isCompact_empty)
          (U i) (V j) ((PolAt Y H t ∅).one_mem) (p₁ i j) (by simp))).and
        (hv.eventually (P.depthBill_of _ _ _ _ _ _ _ ((V₁ i|>.union (V₂ j)).union
          (P.detectorGeometry 3 c d).1)
          (polAt_up Y H t₀ (U i)) (polAt_up Y H t₀ (V j)) (He i j).2.1 (p₁ i j) (He i j).2.2.1))))]
      with p e E
    let v:=(e Q' Q').1
    let w:= inside_budget Y H (He Q' Q').2.1
    refine ⟨t₀,v,(fun z j ↦ (E z j).1 (v₀ p) ⟨v.1,t₀.trans v.2⟩),(fun z j ↦ ⟨(He z j).2.2.1,
      (e z j).2.1,(E z j).2 _ v⟩),?_, (identifyRevenue Y H _ _ _ w v).2.2,(e Q' Q').2.2.1⟩
    intro z j _
    exact (identifyRevenue Y H _ _ _ ((boardedDB K (c d).t).mul_mem ((boardedDB K (c d).t).mul_mem
      (inside_budget Y H (polAt_up Y H t₀ (U z))) (inside_budget Y H (polAt_up Y H t₀ (V j)))) w) v).2.2
  exact entry_tendsto _ _ _ (fun i j ↦ (He i j).2.2.2.2)

omit h

/-- Literal estimation order, no mandate to implement selected finite cost on
proofs about the raw marginals. Starting at a realized successful pair, may even
observe successful matrices eventually by taking true **finite** ratios (after the
growing detector, all its cutoff/period thresholds inside), fixed supports. No local
claim when tests are evaluated outside the stated qualifications. Success measurement
has a connected meaning at the limit and is even connected in `P.measureAt`. The actual
ratio of finite costs here already sees the nonvanishing (NOT saying it would
implement a split prediction if separately advecting just its gauge and matter readings
all the way to that top, NOR claiming connected meaning for the ratio at finite `d,p`). -/
lemma Realized.contour (p : P.Realized R s n x f g)(T : Set (Matrix Window.Family Window.Family ℂ))
    (u : IsOpen T)(m : P.measureField s n f g x∈ T) :
    ∀ᶠ t in atTop, ∀ᶠ d in atTop, ∀ᶠ p' in followStage,
      P.Participates s t n f g c d p' ∧ (P.primitiveObservation t s n f g c d p')∈ T ∧
      Success (P.primitiveObservation t s n f g c d p') := by
  let I₀:= T ∩ {u : Matrix Window.Family Window.Family ℂ | Success u}
  have hi : IsOpen I₀:= u.inter (isOpen_iff_mem_nhds.mpr
    (fun i h ↦ eventually_success (𝓝 i) id _ (fun i j ↦ ((continuous_apply _).comp (continuous_apply _)).continuousAt) h))
  filter_upwards [p.limits.eventually (hi.mem_nhds (show P.measureField s n f g x∈ I₀ from ⟨m,p.success⟩)),
    eventually_ge_atTop s] with t h hh
  obtain ⟨h',v⟩:= Consult.actualObservation P R s t n f g c x a (p.consultation t hh)
  filter_upwards [h'.eventually (hi.mem_nhds h),v] with d p q
  filter_upwards [q.1,q.2.eventually (hi.mem_nhds p)] with p v p'; exact ⟨v,p'⟩
end
end Spine

#print axioms Spine.depthBill_of
#print axioms Spine.Consult.actualObservation
#print axioms Spine.Realized.contour
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
