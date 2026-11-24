import YM.SU5.MacroSix.Report
import YM.SU5.MacroSix.Painted
import YM.SU5.MacroSix.Receipt

/-! # The Ward zero comparison on the physical order-phase

Suffices Split-normalized-predictor, with either pure marginal Ward at the
actual height. In fact suffice requesting Ward on every physical smooth gauge
sampling on either one, i.e. `Painted`. This is **exact**, tests all such gauges,
not an approximation allowing Ward bounds/error schedules. Doesn't even need
an ensemble reading to price these opponents. Public a-pair & list receipts
(also arbitrary `t`, not needing large smoothing resolution). Note the points
are of the TRUE SIZE in all such reports with `loft`: centered pose times
the original physical budgets, no restriction to point locus or co-moving
occurrences. Actual opponent built on the common height M by `partner`; normalization &
Ward certified. -/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2800
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
open _root_.YM.MacroSix
namespace Spine
variable (P : Spine) (s t n : ℕ) (j : Axis) (ρ : P.Register)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "Xy" r:max => P.pose t r
local notation "Φ" => Pockets.Prices K
local notation "τ" Y:max => Tapestry.keep Λ P.width t K true Y
variable {M : Pockets.Prices P.calibration} {S T U : Finset Cover} {Z A B V : Set RSpace}
  {f g : P.Test} {b : Bool}
variable (q : PaintedSplit P.par t M)

lemma compare_paint (p : GPhysical) (z : P.RibbonAccount t Z A B S T U b f)
    (v : ∀ x∈ A,p x=SU.central) (w : ∀ x∈B∪V, p x=1) (e : g∈ τ V) (u : Split M)
    (k : GatesPrice M (restrictG Λ t p) ∨ MantlesPrice M (restrictG Λ t p)) : M (f*g)=0 := by
  obtain ⟨N,a,d⟩:= e
  exact pocket_zero _ z.ribbon_ z.t z.u z.color a
    (fun i w ↦ v _ (z.pocketUp i w (treads P.par P.width t i)))
    (fun i h ↦ w _ (Or.inl (z.pocketDown i h (treads P.par P.width t i))))
    (fun i h ↦ w _ (Or.inr (d i h (treads P.par P.width t i)))) u k

include ρ in
/-- The same gauge function on physical space will suffice at **every** later
consultation for the whole promoted family (a charged summand), when using
other bodies priced in `V` (an arbitrary fixed closed region disjoint from its A).
It is already flat on the original endpoint neighborhoods. May pick a different
paint for each pose, summand, query. No uniform or asymptotic Ward weakened into
these hypotheses. -/
theorem recurrentPaint (u : P.RibbonAccount s Z A B S T U b f) (v : Disjoint A V)
    (p : IsClosed V) : ∃ X : GPhysical, Painted X ∧ ∀ (n : ℕ), ∀ M : Pockets.Prices P.calibration,
      Split M → (GatesPrice M (restrictG Λ (s+n) X) ∨ MantlesPrice M (restrictG Λ (s+n) X)) →
        ∀ f'∈keep P.par P.width (s+n) P.calibration true V, M (P.conveying s n f*f')=0 := by
  obtain ⟨X,P',a,b'⟩ := usesPaint A (B∪V) (Set.disjoint_left.mpr fun i e h ↦ h.elim
    (Set.disjoint_left.mp u.noOverlap e) (Set.disjoint_left.mp v e)) u.compactUp (u.compactDown.isClosed.union p)
  exact ⟨X,P', fun n _ k h f t ↦ P.compare_paint (s+n) X (u.persists P s ρ n)
    a.self_of_nhdsSet b'.self_of_nhdsSet t k h⟩

include q in
lemma mSplit_reserve (h : P.RibbonAccount t Z A B S T U b f) (p : g∈ τ V) (v : Disjoint A V) :
    M (f*g)=0 := by
  obtain ⟨N,a,d⟩ := p; let W := P.placard t N
  have he : g∈ τ W := ⟨N,a,P.placard_print t N⟩
  have hp : Disjoint A W := v.mono_right ((P.placard_spec t).1 d)
  obtain ⟨X,P',c,u⟩ := usesPaint A (B∪W) (Set.disjoint_left.mpr fun i e h' ↦ h'.elim
    (Set.disjoint_left.mp h.noOverlap e) (Set.disjoint_left.mp hp e)) h.compactUp (h.compactDown.union
      (P.placard_compact t N)).isClosed
  exact P.compare_paint _ X h c.self_of_nhdsSet u.self_of_nhdsSet he q.1 (q.2 X P')

include q -- in group of such at every t
lemma mSplit (h : f∈ P.Covered t A b) (u : g∈ τ B) (v : Disjoint A B) : M (f*g)=0 := by
  refine Submodule.span_induction (p:=fun f _ ↦ M (f*g)=0) ?_ (by simp)
    (fun _ _ _ _ p q ↦ by rw [add_mul,map_add,p,q,add_zero])
    (fun i _ _ h ↦ by rw [Algebra.smul_mul_assoc,map_smul,h,smul_zero]) h
  rintro x ⟨A',B',S,T,U,p⟩
  exact P.mSplit_reserve t q p u (v.mono_left p.zoneUp)

section lists
variable {I : Type*} (X : I → Set RSpace)(F : I → P.Test) (L : List I)
  (h : ∀ i∈ L, ∃ b, F i∈ P.Covered t (X i) b)
local notation "Q" => (L.map F).prod
omit q in
private lemma tailKeeps {A : Set RSpace} (v : ∀ x∈L, X x ⊆ A)
    (p : ∀ x ∈ L, F x∈ τ (X x)) : Q ∈ τ A := by
  induction L with
  | nil => exact Subalgebra.one_mem _
  | cons i l ih =>
      exact Subalgebra.mul_mem _
        (rooms P.par P.width t P.calibration true _ (v i List.mem_cons_self) (p _ List.mem_cons_self))
        (ih (fun j u ↦ v j (List.mem_cons_of_mem i u)) (fun j u ↦ p _ (List.mem_cons_of_mem i u)))
include h
lemma mSplit_many (c : L ≠ []) (v : L.Pairwise (fun i j ↦ Disjoint (X i) (X j))) : M Q=0 := by
  cases L with
  | nil => contradiction
  | cons i L =>
    obtain ⟨b,w⟩:= h _ (List.mem_cons_self)
    let A : Set RSpace := ⋃ i∈{i|i∈L}, X i
    have hx (j:I) (p : j∈ L) : X j⊆ A := Set.subset_biUnion_of_mem (show j∈{i|i∈L} from p)
    have hy (j : I) (p : j∈ L) : F j∈ τ (X j) := by
      obtain ⟨x,h⟩:= h j (List.mem_cons_of_mem i p); exact (P.coveredPrices t h).1
    have ht : Disjoint (X i) A:= Set.disjoint_left.mpr (fun x h b ↦ by
      obtain ⟨j,u,b⟩ := Set.mem_iUnion₂.mp b
      exact Set.disjoint_left.mp ((List.pairwise_cons.mp v).1 j u) h b)
    exact P.mSplit t q w (tailKeeps _ t X F L hx hy) ht
end lists

include ρ q
/-- Manuscript `eq:msplit`. Nonempty products—including single factor. Includes
bodies placed at different resolutions, asking this purchase at any `t` where
all footprints fit. Use `Apron.reflectCoverage` as often as desired. Covers all
six families (`pay_factor` uses `Covered`, or plug `sixStamp`). -/
theorem mSplit_pose {I : Type*} (D : I → P.Apron) (r : I → Cover) (L : List I)
    (x : L ≠ []) (d : ∀ i∈L, ∃ b,(D i).covered P b) (a : ∀ i∈L,(D i).s≤t)
    (v : L.Pairwise (fun i j ↦ Disjoint ((D i).scenery P (Xy (r i)))
      ((D j).scenery P (Xy (r j))))) : M (P.fullScroll t D r L)=0 := by
  refine P.mSplit_many t q (fun i ↦ (D i).scenery P (Xy (r i)))
    (fun i ↦ P.fieldAt t (D i) (r i)) L ?_ x v
  intro i e; obtain ⟨b,h⟩ := d i e
  exact ⟨b,P.pay_factor ρ (D i) h t (a i e) _⟩

omit q in
lemma mSplit_sumCovered (D : P.Apron) (p : D.covered P b) (f : Vantage → ℝ)
    (a : D.s≤ t)(u : HasCompactSupport f) : P.smearField t f D ∈ P.Covered t (P.doubledBudget f D) b := by
  have hf := P.pose_finite t f u; unfold smearField; rw [finiteTest_sum _ _ _ hf.toFinset (by simp)]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i e ↦ Submodule.smul_mem _ _ ?_)
  have he : D.scenery P (P.pose t i) ⊆ P.doubledBudget f D:= fun x p ↦
    ⟨P.pose t i,subset_tsupport _ ((show i∈Function.support (f∘P.pose t) from (by simpa using e)) : f (P.pose t i)≠0),p⟩
  exact (P.covered_bigger t he) (P.pay_factor ρ D p t a i)

theorem mSplit_smears {I : Type*} (D : I → P.Apron)(r : I → Vantage → ℝ) (L : List I)
    (x : L ≠ []) (d : ∀ i∈L,∃ b,(D i).covered P b) (a : ∀ i∈L,(D i).s≤t)
    (u : ∀ i∈L, HasCompactSupport (r i))
    (v : L.Pairwise (fun i j ↦ Disjoint (P.doubledBudget (r i) (D i))
      (P.doubledBudget (r j) (D j)))) : M (L.map (fun i ↦ P.smearField t (r i) (D i))).prod=0 := by
  refine P.mSplit_many t q (fun i ↦ P.doubledBudget (r i) (D i)) _ L ?_ x v
  intro i h; obtain ⟨b,e⟩ := d i h; exact ⟨b,P.mSplit_sumCovered t ρ _ e _ (a i h) (u i h)⟩

omit ρ q
/-- Same signed normalization and all stencil conventions; switch only the paid
predictor at `t`. -/
def respond (f g : Vantage → ℝ) (M : Pockets.Prices P.calibration) :
    Matrix Window.Family Window.Family ℂ := Matrix.of fun Z Q ↦
  M (P.smearField t f ((P.sixBody s n Z).kiss P 3) * P.smearField t g (P.sixBody s n Q))

local notation "J₁" i:max => ((P.sixBody s n i).kiss P 3)
local notation "J₂" i:max => (P.sixBody s n i)

variable (f g : Vantage → ℝ)
include ρ q
theorem zero_matrix (p : P.StockClear n)(a : s ≤ t)(w : HasCompactSupport f)
    (u : HasCompactSupport g)(v : ∀ i j, Disjoint (P.doubledBudget f (J₁ i))
      (P.doubledBudget g (J₂ j))) : P.respond s t n f g M = 0 := by
  ext i j
  exact P.mSplit t q (P.mSplit_sumCovered t ρ (J₁ i) (Apron.reflectCoverage P 3 _
    (P.sixStamp s n i p)) f a w) ((P.coveredPrices t (P.mSplit_sumCovered t ρ (J₂ j)
      (P.sixStamp s n j p) g a u)).1) (v i j)

theorem frameZero (p : P.StockClear n)(a : s ≤ t)(w : HasCompactSupport f)
    (u : HasCompactSupport g){c : ℝ}(e : P.OnFrame s n f g c) : P.respond s t n f g M = 0 := by
  apply P.zero_matrix s t n ρ q f g p a w u
  intro i j; exact Set.disjoint_left.mpr (fun x h h' ↦ (not_lt_of_gt (show x 3 < 2*c from (e.places i j).1 h))
    (show 2*c < x 3 from (e.places i j).2 h'))
omit ρ q

variable (x : P.Spectrum0 3)
local notation "Γ" => P.singleState 3 t x
lemma trueResponse : P.respond s t n f g (P.singleState 3 t x) = P.measureAt s n t f g x := rfl

/-- Any hypothetical opposed raw prices allowed. Even both the TRUE signed
marginals will price the 0 prediction on mixing them by the factorized bill. -/
def partner : Pockets.Prices P.calibration := splitMap (P.singleState 3 t x) (P.singleState 3 t x)
local notation "Ξ" => P.partner t x

lemma authentic_norm : Γ (1:P.Test)=1 := by rw [P.single_state, P.reading_unit, map_one]
lemma ward_appointment (f : P.Test)(T : GVertex) : Γ (pennant K T f)= Γ f :=
  congrArg (P.chi 3 x) (P.reading_gauge 3 t T f)

lemma actualPrediction : Split (Ξ) ∧ (∀ f∈Gate K,Ξ f=Γ f) ∧ (∀ f∈Mantle K,Ξ f=Γ f) ∧
    (∀ p, GatesPrice (Ξ) p) ∧ (∀ p,MantlesPrice (Ξ) p) :=
  have he := P.authentic_norm t x
  ⟨buildSplit (Γ) (Γ) he he,fun f h ↦ split_gate (Γ) (Γ) he h,fun g h ↦ split_mantle (Γ) (Γ) he h,
    fun p ↦ split_gate_ward he (fun f _ ↦ P.ward_appointment t x f p),
    fun p ↦ split_mantle_ward he (fun f _ ↦ P.ward_appointment t x f p)⟩
lemma partnerPricing : Comparison (Ξ):=
  ⟨(P.actualPrediction t x).1,Or.inl ((P.actualPrediction t x).2.2.2.1)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms recurrentPaint
#print axioms mSplit_pose
#print axioms mSplit_smears
#print axioms zero_matrix
#print axioms frameZero
#print axioms partnerPricing
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
