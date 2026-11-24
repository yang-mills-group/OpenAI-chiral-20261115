import YM.SU5.Reconstruction.Cross.Cased
import YM.SU5.Reconstruction.Cross.AllReal
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
/- # Fixed physical regions for aperture and all the charts

The chart at observation height doesn't have to fit if checking at its original
stencil grid. Can accept on any high enough refinement. All such charts cohere as
kernels even on different chart heights (Coherency). Use e.g. for comparing
reorderings at arbitrary aperture openings. -/
open _root_.YM.SelectionAnalysis Vacancy.Average
variable {ι:Type*} [Finite ι] (f:ι→ Marks (tent Y H) false) (X:ι→ Finset Cover)
section
local notation "P" => Timetable
local notation "ΦS" t:max a:max => silhouette Λ l t a
local notation "MS" x:max=> silhouette Λ l s (X x)
-- contiguous using real travel. sufficient chart criterion in physical coords.
inductive books {ι : Type*} (start endP:ι→ℝ): ℝ→ List ι → Prop
| blank (r : ℝ) : books start endP r []
| next {i r x} : start i=r→ books start endP (endP i) x→ books start endP r (i::x)

local notation "F" t:max x:max=> upGrade Y H s Q false (f x) t
lemma stretching {v:ι → Axis → ℝ} (x: List ι) {r₀:ℝ} {ia ib:ι→ℝ}
    (hp:∀ i, ia i< ib i ∧ ∀ x∈ silhouette Λ l s (X i), ia i < v i j+x j ∧ v i j+x j < ib i) (h:books ia ib r₀ x)
    (p:∀ i,InTest K true (X i) false (f i).val) :
    ∀ᶠ t in atTop, ∃ (g:∀ i,Gate Y H t j (upGrade Y H s Q false (f i) t)), Leaves Y H t j (fun i=> F t i) g (meshPy Μ r₀ t) x ∧
      ∀ i,(g i).within_ (v i) ∧ ∀ u∈ silhouette Λ l s (X i),u j∈ Icc (bell Μ t (g i).base) (bell Μ t ((g i).base+ (g i).width)):=by
 let D'(i:ι):= Timetable.mk (σ:=MS i) (v:=v i) (j:=j) (ia i) (ib i) (hp i).1 (hp i).2
 filter_upwards [eventually_all.mpr (fun i=> ticket_has Y H Q s j (p i) (D' i))] with t q
 choose g A B C H' using q
 refine ⟨g,?_,fun i=> ⟨A i,H' i⟩⟩
 induction h with
 | blank t=> exact Leaves.blank _
 | @next i r' x h p ih=>
    rw [←h]; refine Leaves.append (B i) ?_
    rw [← show (g i).start=meshPy Μ (ia i) t from B i, C i]; exact ih
-- all axes occupancy corollary later.

-- shifting a mark f on translated boxes doesn't increase the physical size. Include
-- Volume-collar after refinement. 
local notation "Λ₁" => seeMesh (timeMesh Λ)
lemma physical_shift (X : Finset Cover)(S: Cover) : ∀ x∈ silhouette Λ l s (streetBox (tent Y H) S X),∃ v∈ silhouette Λ l s X,x= v+ toR (M:=timeMesh Λ) (grid (timeMesh Λ) s S):=by
 intro x hx; obtain ⟨y,h,t⟩:=silhouette_iff.mp hx
 obtain ⟨v,u,w⟩:= drives_shifted Y H S ordinate ordinate_one y h
 let Y₀:= toR (M:=timeMesh Λ) (grid (timeMesh Λ) s S); refine ⟨x-Y₀,silhouette_iff.mpr ⟨v,u,?_⟩,(sub_add_cancel ..).symm⟩
 apply stamp_abs.mpr; intro i
 have he:gaugePosition Λ s y i= gaugePosition Λ s v i+Y₀ i:=by
   specialize w i; rw [if_pos (ordinates i)] at w; unfold gaugePosition; rw [w]; unfold Y₀ toR; rw [grid_eval,bell_norm]; push_cast; ring
 rw [Pi.sub_apply,show x i-_ -_ = x i-gaugePosition Λ s y i by rw [he]; ring]
 exact stamp_abs.mp t i

variable {Z:Marks (tent Y H) false}
lemma high_aperture_test {X: Finset Cover} (h:InTest (tent Y H) true X false Z.val) (q:Cover) (t:ℕ) (p:s≤t) :
    let y:= toR (M:=timeMesh Λ) (grid Μ t q); let S:= Selected.streetBox (tent Y H) q (volumeAround Λ l (t-s) X)
    InTest K true S false (relocateWorld Y H false q (upGrade Y H s Q false Z t)).val ∧
     ∀ v∈ silhouette Λ l t S, v-y∈ silhouette Λ l s X:=by
 intro y S
 obtain ⟨x,h⟩:= nearby_power Y H Q s h t p; rw [world_val]; refine ⟨cad_test q _ x,?_⟩
 intro i hi; obtain ⟨w,u,rfl⟩:= physical_shift Y H t _ q i hi; unfold y; rw [add_sub_cancel_right]; exact h u

end

-- gate support away from contact, mover with y in Γ still located within continuous slot. instant.
lemma aligned {f:Marks (tent Y H) false} (G : Gate Y H s j f) :
    ∃ S:Finset Cover, InTest K true S false f.val ∧ silhouette Λ l s S ⊆ {u:RSpace| u j∈ Set.Icc (bell Μ s G.base) (bell Μ s (G.base+G.width))}:=by
 obtain ⟨S,x,v⟩:= G.entry.property
 have ht:= v.relocate K j G.base; rw [show (K).B=Λ.block from rfl,add_zero, show ruler Λ.block*G.base + ruler Λ.block*G.width= ruler Λ.block*(G.base+G.width) from by ring] at ht -- defeq?
 rw [G.price]; exact ⟨_,flow_port K j _ x, (stamp_span Y H j _).2 ht⟩
theorem physical_gate {f:Marks (tent Y H) false} (G : Gate Y H s j f) :
    ∃ U : Set RSpace, IsCompact U ∧ 
    (∃ S:Finset Cover, InTest (tent Y H) true S false f.val ∧ silhouette Λ l s S⊆ U) ∧
    (∀ x: Axis→ℝ,G.within_ x → ∀ p∈U,bell Μ s G.start < x j+p j ∧ x j+p j < bell Μ s (G.start+ G.full)) ∧
    ∀ (t:ℕ), s≤t → ∀ q:Cover,
      ∃ W:Finset Cover, InTest K true W false (relocateWorld Y H false q (upGrade Y H s Q false f t)).val ∧
         silhouette Λ l t W ⊆ {p | p-toR (M:=timeMesh Λ) (grid Μ t q)∈ U}:=by
 obtain ⟨S,h,w⟩:= aligned Y H s j G
 refine ⟨silhouette Λ l s S,silhouette_compact .., ⟨S,h,Set.Subset.rfl⟩,fun x hx u q=>?_,fun t e p=>?_⟩
 · have p:= (w q).1; have v':=(w q).2
   obtain ⟨hp,hK⟩:=hx
   unfold Gate.left at hp; unfold Gate.right Gate.left at hK; rw [bell_add] at v'; unfold Gate.full; push_cast; rw [bell_add,bell_add Μ s G.width]; constructor <;> linarith
 exact ⟨_,high_aperture_test Y H Q s h p t e⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.physical_gate
