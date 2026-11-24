import YM.SU5.Reconstruction.Cross.Agreement
import YM.SU5.Reconstruction.Cross.EachTime
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
open _root_.YM.SelectionAnalysis Vacancy.Average
section variation
variable {ι : Type*} {W:Type*} [TopologicalSpace W] (x : ι→Axis→W)
private def blendW (t:Finset Axis)(f:ι→Axis→W) (i:ι)(j:Axis) := if j∈t then f i j else x i j
private lemma blend_still (t:Finset Axis):blendW x t x=x:=by funext i j; simp [blendW]
private lemma blend_full (f:ι→Axis→W): blendW x Finset.univ f=f:=by funext i j; simp [blendW]
private lemma blend_void (f:ι→Axis→W): blendW x ∅ f=x:=by funext i j; simp [blendW]
private lemma blend_cont (t:Finset Axis) : Continuous (blendW x t) :=by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold blendW; by_cases h:j∈t; simp_rw [if_pos h]; exact (continuous_apply j).comp (continuous_apply i); simp_rw [if_neg h]; exact continuous_const
private lemma onAxisCont {T : Type*} [PseudoMetricSpace T] (F:(ι→Axis→W)→T)
    (h : ∀ (j:Axis) (u u': (ι→Axis→W) → ι→Axis→W), (∀ f i l,l≠j→u f i l=u' f i l) →
      Tendsto u (𝓝 x) (𝓝 x) → Tendsto u' (𝓝 x) (𝓝 x) → Tendsto (fun y => dist (F (u y)) (F (u' y))) (𝓝 x) (𝓝 0)) : ContinuousAt F x := by
  have ht(S:Finset Axis):Tendsto (F ∘ blendW x S) (𝓝 x) (𝓝 (F x)):=by
    induction S using Finset.induction_on with
    | empty=> change Tendsto (fun f=> F (blendW x ∅ f)) _ _; simp_rw [blend_void]; exact tendsto_const_nhds
    | insert i S p ih=>
       have g(S:Finset Axis):Tendsto (blendW x S) (𝓝 x) (𝓝 x):=by have h':=(blend_cont x S).tendsto x; rwa [blend_still] at h'
       refine tendsto_of_tendsto_of_dist ih (h i (blendW x S) (blendW x (insert i S)) ?_ (g _) (g _))
       intro u x l q; simp [blendW,q]
  specialize ht Finset.univ; rw [show F ∘ blendW x Finset.univ= F from funext (fun i=> by unfold Function.comp; rw [blend_full])] at ht; exact ht
end variation
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
variable {ι:Type*} [Finite ι] (f:ι→ Marks (tent Y H) false) (g : ∀ x, Gate Y H s j (f x))
local notation "G" => peninsula Y H V Q Qt j false C c
local notation "Θ" => rawProduct Y H V Q Qt s j C c f g
local notation "θ" => rawTrace Y H V Q Qt s j C c f g
local notation "Μw" => ι→ Axis→ Marks (tent Y H) false -- not used
local notation "Μk" => seeMesh Μ
local notation "φ" => ι→Axis→ℝ
local notation "X" => plannedProduct Y H V Q Qt s j C c f g
local notation "Xi" => electedAtlas Y H V Q Qt s j C c f g
local notation "Tv" => gridChart (ι:=ι) (timeMesh Λ)
local notation "Tq" q:max=> toR (M:=Μ) q

def everywhere_axis (t:List ι) (x:ι→Axis→ℝ):Prop:= ∀ i:Axis,∃ (t': List ι) (z:ℤ) (g:∀ x,Gate Y H s i (f x)), Leaves Y H s i f g z t' ∧ t.Perm t' ∧ ∀ i∈t',(g i).within_ (x i)
local notation "C'" => everywhere_axis Y H s f
lemma aperture_open (t:List ι) : IsOpen {x| everywhere_axis Y H s f t x}:=by
    rw [show {x|C' t x}=⋂ i:Axis,⋃ (t':List ι) (z:ℤ) (g:∀ x,Gate Y H s i (f x)) (e:Leaves Y H s i f g z t') (p:t.Perm t'), {x|∀ i∈t',(g i).within_ (x i)} by
       ext x; unfold everywhere_axis; simp only [mem_iInter,mem_iUnion,mem_setOf_eq]; constructor <;> intro h i <;> obtain ⟨t',z,g,r⟩:=h i
       · exact ⟨t',z,g,r.1,r.2.1,r.2.2⟩ -- tune And vs exists
       · obtain ⟨e,f,r⟩:=r; exact ⟨t',z,g,e,f,r⟩]
    exact isOpen_iInter_of_finite (fun i=> isOpen_iUnion fun t'=> isOpen_iUnion fun z=>isOpen_iUnion fun g=> isOpen_iUnion fun e=> isOpen_iUnion fun v=> open_window Y H s i f g t')

-- order irrelevant. This stronger certificate not just two-point passage. Accept γ when all dimensions ordered.
lemma rawContinuousAt {lo:ℤ} {t:List ι} (p : Leaves Y H s j f g lo t) {x : ι → seeMesh (timeMesh Λ)} (e:∀ i∈t,(g i).within_ (toR (M:=Μ) (x i))) (h : everywhere_axis Y H s f t (gridChart Μ x)) (C₁ : ∀ i: Axis, Arena Y H Q.circuit i 0 false) :
    ContinuousAt (rawTrace Y H V Q Qt s j C c f g t) x := by
  refine onAxisCont x _ ?_; intro d u u' ht l1 l2
  obtain ⟨t',z,g',L,Hs,t'n⟩ := h d
  let c₀:= displacement Y H V Q Qt j false C c d (C₁ d)
  let r(w):=rawTrace Y H V Q Qt s d (C₁ d) c₀ f g' t' w
  have τ : θ t =ᶠ[𝓝 x] r:=by
    filter_upwards [((open_window Y H s j f g t).preimage (grid_continuity Μ)).mem_nhds e, ((open_window Y H s d f g' t').preimage (grid_continuity Μ)).mem_nhds t'n] with x y v
    -- y v implicit membership terms
    exact raw_agree Y H V Q Qt s j C c f g (C₁ d) c₀ g' Hs p L (fun s i=> (across_response Y H V s Q Qt j false C c i d (C₁ d)).symm) x (fun i e=> (g i).allows (y i e)) (fun i e=> (g' i).allows (v i e))
  suffices H : Tendsto (fun x=> dist (r (u x)) (r (u' x))) (𝓝 x) (𝓝 0) from H.congr' (by filter_upwards [τ.comp_tendsto l1,τ.comp_tendsto l2] with u a b using congrArg₂ dist a.symm b.symm)
  exact vary_city Y H V Q Qt s d (C₁ d) c₀ f g' t' t'n ht l1 l2

lemma recovers {lo:ℤ} {t:List ι} (p : Leaves Y H s j f g lo t) (ht:t.Nodup)
    (x : ι → seeMesh (timeMesh Λ)) (C₁ : ∀ i: Axis, Arena Y H Q.circuit i 0 false) (e:∀ i∈t,(g i).within_ (toR (M:=Μ) (x i))) (h : everywhere_axis Y H s f t (gridChart Μ x)) :
    rawTrace Y H V Q Qt s j C c f g t x=electedAtlas Y H V Q Qt s j C c f g t (gridChart (timeMesh Λ) x) :=by
  classical
  letI:=Fintype.ofFinite ι
  exact tendsto_nhds_unique (smooth_fit (timeMesh Λ) (rawTrace Y H V Q Qt s j C c f g t) x (rawContinuousAt Y H V Q Qt s j C c f g p e h C₁)) (handles Y H V Q Qt s j C c f g t x ht)
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.recovers
