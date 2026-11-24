import YM.SU5.Reconstruction.Cross.Stretched
import YM.SU5.Reconstruction.Cross.Coherency
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
/-!
# A *single* function on real configuration atlas

A domain theorem (use high-ANY acceptable chart, including if high rung deeply above first probe creation).
Then explicit coherence and continuity. Later: analytic contours in another section.
Note references need not yet belong to the domain for all locations (mark size fixed).
Please use `the construction notes` for discussion.
-/
open _root_.YM.SelectionAnalysis Vacancy.Average
variable {ι:Type*} [Finite ι] (f:ι→ Marks (tent Y H) false) (x: List ι)
local notation "Ωt" t:max x:max => upGrade Y H s Q false (f x) t
local notation "φ" => ι → Axis→ℝ
local notation "Γx" => ι→seeMesh Μ
-- address chosen on Γ to high. inside Lebesgue real inequalities.
structure AcceptFrom where
  stage : ℕ
  large : s ≤ stage
  gate : ∀ x:ι,Gate Y H stage j (upGrade Y H s Q false (f x) stage)
  order : List ι
  schedule : order.Perm x
  low : ℤ
  travel : Leaves Y H stage j (fun i=> (Ωt stage i)) gate low order
local notation "X" t:max=> AcceptFrom Y H Q s t f x
-- enumerate *all* open loci per time axis. Chart width finite. union is the asserted REAL analytic geometry of Γ continuation.
namespace AcceptFrom
variable {Y H V Q Qt s j C c f x}
def domain (A:X j) : Set (ι→Axis→ℝ):= {v|∀ i∈A.order,(A.gate i).within_ (v i)}
lemma isOpen (A:X j): IsOpen A.domain:= open_window Y H A.stage j _ A.gate A.order
end AcceptFrom
noncomputable def arenaRegion (x:List ι) : Set (ι→Axis→ℝ) :=⋃ (j:Axis) (A: AcceptFrom Y H Q s j f x), A.domain
local notation "S" => arenaRegion Y H Q s f x
noncomputable def axisRegion (x:List ι)(i:Axis) : Set (ι→Axis→ℝ) := ⋃ A: AcceptFrom Y H Q s i f x,A.domain
lemma axis_isOpen (i:Axis) : IsOpen (axisRegion Y H Q s f x i) := isOpen_iUnion (fun A=> A.isOpen)
lemma arena_open : IsOpen (arenaRegion Y H Q s f x) := isOpen_iUnion (fun j => axis_isOpen Y H Q s f x j)

local notation "Ξ" => electedAtlas Y H V Q Qt
variable (Z : ∀ j, Arena Y H Q.circuit j 0 false)
local notation "H₀" k:max => displacement Y H V Q Qt j false C c k (Z k)
noncomputable def commonR (v:ι→Axis→ℝ) : ℂ:=if h:v∈S then
    let k:=(Set.mem_iUnion.mp h).choose; let W:= (Set.mem_iUnion.mp (Set.mem_iUnion.mp h).choose_spec).choose
    electedAtlas Y H V Q Qt W.stage k (Z k) (H₀ k) _ W.gate W.order v else 0
local notation "Φc" => commonR Y H V Q Qt s j C c f x Z
lemma in_chart (W : AcceptFrom Y H Q s j f x) : W.domain ⊆ S:= Set.subset_iUnion_of_subset j (Set.subset_iUnion _ W)
private lemma same_values (u v:Axis)(s:ℕ)(p:Marks (tent Y H) false) : response Y H V s Q Qt u false (Z u) (H₀ u) p = response Y H V s Q Qt v false (Z v) (H₀ v) p := by rw [across_response,across_response]
lemma enters_common (p:x.Nodup) {k:Axis}(W:AcceptFrom Y H Q s k f x)(v:ι→Axis→ℝ)(e:v∈W.domain) : Φc v= electedAtlas Y H V Q Qt W.stage k (Z k) (H₀ k) _ W.gate W.order v :=by
 let h:= in_chart Y H Q s k f x W e
 rw [commonR,dif_pos h]; dsimp only;
 let i:=(Set.mem_iUnion.mp h).choose; let P:AcceptFrom Y H Q s i f x:=(Set.mem_iUnion.mp (Set.mem_iUnion.mp h).choose_spec).choose
 have he:v∈P.domain:= (Set.mem_iUnion.mp (Set.mem_iUnion.mp h).choose_spec).choose_spec
 exact differentRungs Y H V Q Qt s i (Z i) (H₀ i) f (Z k) (H₀ k) P.gate W.gate (P.schedule.trans W.schedule.symm) (P.schedule.nodup_iff.mpr p) (same_values Y H V Q Qt j C c Z i k) P.large W.large P.travel W.travel he e -- tune order args
lemma common_continuous (p:x.Nodup) : ContinuousOn (commonR Y H V Q Qt s j C c f x Z) (arenaRegion Y H Q s f x) := by
  intro v h; obtain ⟨i,W⟩:= Set.mem_iUnion.mp h; obtain ⟨g,e⟩:= Set.mem_iUnion.mp W
  apply ContinuousAt.continuousWithinAt
  refine (electedAtlas_continuous Y H V Q Qt g.stage i (Z i) (H₀ i) _ g.gate g.order).continuousAt.congr ?_
  exact Eventually.mono (show ∀ᶠ w in 𝓝 v, w∈g.domain from g.isOpen.mem_nhds e) (fun i h=> (enters_common Y H V Q Qt s j C c f x Z p g i h).symm)
-- path assertion through outside occupancy. eventually stage heights unbounded for timetable.
variable (U : ι→ Finset Cover)
lemma payment_geometry {i:Axis} (y:List ι)(e:y.Perm x) {r w:ι→ℝ} {v:ι→Axis→ℝ} (p:∀ k,InTest (tent Y H) true (U k) false (f k).val)
    (h0:∀ k, r k<w k ∧ ∀ x∈ silhouette Λ l s (U k), r k< v k i+x i ∧ v k i+x i < w k) (m:ℝ) (h:books r w m y) :
  ∀ᶠ t in atTop,∃ g:AcceptFrom Y H Q s i f x, g.stage=t ∧ g.order=y ∧ v∈g.domain := by
 filter_upwards [stretching Y H Q s i f U y h0 h p,eventually_ge_atTop s] with t g ht
 obtain ⟨g0,e0,h'⟩:=g; exact ⟨⟨t,ht,g0,y,e,_,e0⟩,rfl,rfl, fun x _=> (h' x).1⟩

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.common_continuous
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.payment_geometry
