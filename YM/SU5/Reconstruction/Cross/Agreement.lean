import YM.SU5.Reconstruction.Cross.Train
import YM.SU5.Reconstruction.Cross.Acceptance
import YM.SU5.Reconstruction.Cross.Traced
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
# Real-spacetime Euclidean kernel on selected absolute aperture words

Unconditional. Precisely purchases projection without identifying it with Id. Eχ preserved
on Γ with the indicated smoothing; raw equal even on common windows without smoothing.
Single analytic (in time widths; below and later files) object; see the construction notes for definition.
Still not at contact regions. Nor one single space with Poincaré and all axes yet (obstructions there).
-/
open _root_.YM.SelectionAnalysis Vacancy.Average
variable {ι : Type*} (f:ι→ Marks (tent Y H) false) (g : ∀ x, Gate Y H s j (f x)) (t : List ι)
local notation "Β" f:max x:max => entrance Y H V s Q Qt j false C f x
local notation "B" x:max => Ρ x
local notation "O₀" q:max => indoorOp Y H V Q Qt s j C c q
local notation "Γ" => saunters Y H V Q Qt j false C c
local notation "G" => peninsula Y H V Q Qt j false C c
local notation "L" => fort Y H V Q Qt j false C c
local notation "Ψ" => vocation Y H V Q Qt j false C c
local notation "Θ" => rawProduct Y H V Q Qt s j C c f g
local notation "θ" => rawTrace Y H V Q Qt s j C c f g
local notation "A" q:max => paidOp Y H V Q Qt s j C c q
local notation "Ρx" => ι→seeMesh Μ
local notation "φ" => ι→Axis→ℝ
noncomputable def plannedProduct (u:ι→ Axis→ℝ) : (L).Op := (t.map (fun i=> (A (g i)) (u i))).prod
noncomputable def electedAtlas (u:ι→ Axis→ℝ) := inner ℂ (vocation Y H V Q Qt j false C c) ((plannedProduct Y H V Q Qt s j C c f g t u) Ψ)
local notation "X" => plannedProduct Y H V Q Qt s j C c f g
local notation "Xi" => electedAtlas Y H V Q Qt s j C c f g
-- uniform boundedness consumed on all axes. Strong-on-ALL-continuous vectors.
lemma curtain_continuous (w:L) : Continuous (fun u=> (X t u) w) := by
  induction t with
  | nil=> exact continuous_const
  | cons i t ih=>
    change Continuous (fun u : ι → Axis → ℝ=> (A (g i)) (u i) (X t u w))
    exact paid_cont Y H V Q Qt s j C c (g i) _ (fun u:ι → Axis→ℝ=> u i) ih (continuous_apply i)
lemma electedAtlas_continuous : Continuous (electedAtlas Y H V Q Qt s j C c f g t) := continuous_const.inner (curtain_continuous Y H V Q Qt s j C c f g t Ψ)
noncomputable def gridChart (M:Mesh)(y:ι→seeMesh M) : ι→Axis→ℝ := toR ∘ y
local notation "φ₀" => gridChart (ι:=ι) Μ
lemma grid_continuity (M:Mesh) : Continuous (gridChart (ι:=ι) M):= continuous_pi fun i=> (toR_cont M).comp (continuous_apply i)
lemma gridChart_dense (M:Mesh) : DenseRange (gridChart (ι:=ι) M):= DenseRange.piMap (f:=fun (_:ι) (x:seeMesh M)=>toR (M:=M) x) (fun _=>real_grid_dense M)

local notation "Γy" => ι→seeMesh Μ
-- smoothing is still absolutely placed. strong on compressed inputs only.
noncomputable def smearTrain (q:ℕ×ℕ) (u:Γy) : (ρ).Op := (t.map (fun i=> smear (timeMesh Λ) (O₀ (g i)) (u i) q)).prod
local notation "S" => smearTrain Y H V Q Qt s j C c f g
variable (u : ι→seeMesh (timeMesh Λ))
lemma strong_words (x:L): Tendsto (fun q=> smearTrain Y H V Q Qt s j C c f g t q u (x.val:ρ)) nested (𝓝 (((plannedProduct Y H V Q Qt s j C c f g t (gridChart (timeMesh Λ) u) x:Γ).val):ρ)):=by
  induction t with
  | nil=> exact tendsto_const_nhds
  | cons i t ih=>
     let w : L := X t (φ₀ u) x; let g':=g i
     apply keeping_times (fun q=> smear (timeMesh Λ) (O₀ (g i)) (u i) q) (fun q=> S t q u (x.val:ρ)) (w.val:ρ) (((A g') (toR (M:=Μ) (u i)) w:Γ).val:ρ) _ (fun t=> smear_budget Y H V Q Qt s j C c (g i) (u i) t) ih (strong_projection Y H V Q Qt s j C c (g i) (u i) w)

section
variable [Fintype ι] [DecidableEq ι]
lemma finances_absolute (p:t.Nodup) (q:ℕ×ℕ) : smoothPositions (timeMesh Λ) (rawProduct Y H V Q Qt s j C c f g t) u q= smearTrain Y H V Q Qt s j C c f g t q u:= averaging_op (fun i v=> (O₀ (g i)) (u i + offsets Μ q.1 q.2 v)) t p
lemma handles (p:t.Nodup) : Tendsto (smoothPositions (timeMesh Λ) (rawTrace Y H V Q Qt s j C c f g t) u) nested (𝓝 (electedAtlas Y H V Q Qt s j C c f g t (gridChart (timeMesh Λ) u))):= by
 let ω':L:=Ψ; let Ω':ρ:=ω'.val
 have h:Ω=Ω':=(vocate ..).symm
 rw [show Xi t (φ₀ u)=inner ℂ Ω' ((X t (φ₀ u) ω':Γ).val:ρ) from rfl]
 have p0(v):smoothPositions Μ (θ t) u v=inner ℂ Ω' (S t v u Ω'):=by
    rw [← finances_absolute Y H V Q Qt s j C c f g t u p v]
    unfold smoothPositions rawTrace; rw [h]; exact Average.natural _ ((innerSL ℂ Ω').comp (ContinuousLinearMap.apply ℂ (ρ).space Ω'))
 rw [show smoothPositions Μ (θ t) u=(fun v=>inner ℂ Ω' (S t v u Ω')) from funext p0]
 exact tendsto_const_nhds.inner (strong_words Y H V Q Qt s j C c f g t u ω')
end
section
variable [Finite ι]
variable {j':Axis} (C' : Arena Y H Q.circuit j' 0 false) (c' : (displayAlgebra Y H V Q Qt j' false C') →⋆ₐ[ℂ] ℂ)
variable (g' : ∀ x, Gate Y H s j' (f x))
local notation "Xi'" => electedAtlas Y H V Q Qt s j' C' c' f g'
local notation "θ'" => rawTrace Y H V Q Qt s j' C' c' f g'
local notation "Mx" i:max => Selected.response Y H V i Q Qt j' false C' c'
-- arbitrary change of chart, incl permutation in ANY order. support real continuum (open price supplied).
lemma comparesProjected {lo lz:ℤ} {x y:List ι} (p:x.Perm y) (u':x.Nodup) (h : Leaves Y H s j f g lo x) (q : Leaves Y H s j' f g' lz y)
    (he : ∀ t (f : Marks (tent Y H) false), (Eχ t) f=(Mx t) f) (v : ι→Axis→ℝ)
    (p' : ∀ i∈x,(g i).within_ (v i)) (q' : ∀ i∈y,(g' i).within_ (v i)) :
    electedAtlas Y H V Q Qt s j C c f g x v = electedAtlas Y H V Q Qt s j' C' c' f g' y v:=by
  classical
  letI:= Fintype.ofFinite ι
  let E: Set (φ):= {v|∀ i∈x,(g i).within_ (v i)} ∩ {v|∀ i∈y,(g' i).within_ (v i)}
  have ht:IsOpen E:=(open_window Y H s j f g x).inter (open_window Y H s j' f g' y)
  let D: Set (φ):= Set.range (φ₀) ∩ E
  have hd:v∈closure D:=by
     refine Metric.mem_closure_iff.mpr ?_
     intro ε h; obtain ⟨u,p,r'⟩ := (gridChart_dense (ι:=ι) Μ).exists_mem_open (ht.inter Metric.isOpen_ball) ((show (E ∩ Metric.ball v ε).Nonempty from ⟨v,⟨p',q'⟩, Metric.mem_ball_self h⟩))
     exact ⟨φ₀ u,⟨⟨u,rfl⟩,p⟩,(dist_comm _ _).trans_lt (show _ from r')⟩
  refine EqOn.closure (s:=D) ?_ (electedAtlas_continuous Y H V Q Qt s j C c f g x) (electedAtlas_continuous Y H V Q Qt s j' C' c' f g' y) hd
  intro z hz; obtain ⟨⟨w,rfl⟩,hz⟩:=hz
  refine tendsto_nhds_unique_of_eventuallyEq (handles Y H V Q Qt s j C c f g x w u') (handles Y H V Q Qt s j' C' c' f g' y w (p.nodup_iff.mp u')) ?_
  refine (besidePositions Μ ((φ₀) ⁻¹' E) w ((ht.preimage (grid_continuity Μ)).mem_nhds hz)).mono ?_
  intro n pn
  exact Average.eq_of _ _ (fun i=> raw_agree Y H V Q Qt s j C c f g C' c' g' p h q he (disclose Μ w n i) (fun z f=> (g z).allows ((pn i).1 z f)) (fun z f=> (g' z).allows ((pn i).2 z f))) -- expected exact might not
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.comparesProjected
