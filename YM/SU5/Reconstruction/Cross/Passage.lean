import YM.SU5.Reconstruction.Cross.Contours
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
-- *Contoured* t does NOT shift axis, orient t real edge unitaries. Region price in each true time slot.
variable {ι : Type*}[Fintype ι] (f : ι→ Marks (tent Y H) false) (g : ∀ i, Gate Y H s j (f i)) (t:List ι)
local notation "Γ" => saunters Y H V Q Qt j false C c
local notation "G" => peninsula Y H V Q Qt j false C c
local notation "L" => fort Y H V Q Qt j false C c
local notation "γ" => vocation Y H V Q Qt j false C c
local notation "ξ" v:max=> contourOp Y H V Q Qt s j C c v
local notation "π" v:max=> minkOp Y H V Q Qt s j C c v
local notation "φp" t:max=> electedAtlas Y H V Q Qt s j C c f g t
local notation "V₀" a:max=> visual Y H s j a
local notation "Ρt" => ι → Axis→ℝ
local notation "Ρ0" => ι → ℝ
local notation "Ρz" => ι → ℂ
variable (v:ι→Axis→ℝ)
noncomputable abbrev realContour (z: ι→ℝ) : ι→Axis→ℝ := fun i=> stepDrift j (v i) (z i)
def viewing (z : ι→ℂ) : Prop := ∀ i∈t,visual Y H s j (g i) (v i) (z i)
local notation "Vt"=> viewing Y H s j f g t v
def opPass (z : ι→ℂ) : (L).Op:= (t.map (fun i=> contourOp Y H V Q Qt s j C c (g i) (v i) (z i))).prod
def minkPass (z : ι→ℝ) : (L).Op:= (t.map (fun i=> minkOp Y H V Q Qt s j C c (g i) (v i) (z i))).prod
noncomputable def requested (z:ι→ℂ): ℂ := inner ℂ γ (opPass Y H V Q Qt s j C c f g t v z γ)
noncomputable def arrived (r:ι→ℝ): ℂ := inner ℂ γ (minkPass Y H V Q Qt s j C c f g t v r γ)
local notation "Ξ" t:max => requested Y H V Q Qt s j C c f g t
local notation "Ψ" t:max => arrived Y H V Q Qt s j C c f g t
local notation "B" t:max=> opPass Y H V Q Qt s j C c f g t
local notation "μ" t:max=> minkPass Y H V Q Qt s j C c f g t

lemma passage (z:ι→ℂ)(p:viewing Y H s j f g t v z) : (Ξ t) v z=(Ψ t) (realContour j v (fun i=> (z i).re)) (fun i=> -(z i).im) := by
 unfold requested arrived opPass minkPass; congr 2
 apply congrArg; apply List.map_congr_left; intro i h; exact continued_contour Y H V Q Qt s j C c (g i) _ _ (p _ h)
lemma Mink_full (r:ι→ℝ)(p: ∀ i∈t,(g i).within_ (v i)) : (Ψ t) v r = (Ξ t) v (fun i=> sideways (r i)) := by
 unfold arrived requested opPass minkPass; congr 2
 apply congrArg; apply List.map_congr_left; intro i h; exact (mink_contour Y H V Q Qt s j C c (g i) _ (r i) (p _ h)).symm
lemma Mink_empty : (Ψ t) v 0=(φp t) v:=by
 unfold arrived electedAtlas minkPass plannedProduct; simp_rw [Pi.zero_apply, mink_zero]
lemma euclidean_time (r:ι→ℝ)(p:∀ i∈t,(g i).within_ (realContour j v r i)) :
   (Ξ t) v (fun i=> (r i : ℂ))=(φp t) (realContour j v r):=by rw [passage]; simp only [Complex.ofReal_re,Complex.ofReal_im,neg_zero]; exact Mink_empty ..; exact fun i h=> (within_step _ _ s j (g i) _ _).2 (p i h)
lemma contour_ready (z:ι→ℂ): Vt z ↔ ∀ i∈t,(g i).within_ (realContour j v (fun i=> (z i).re) i):=by simp only [viewing,realContour,within_step]
lemma window_complex (z:ι→ℂ)(h : Vt z) : AnalyticAt ℂ (requested Y H V Q Qt s j C c f g t v) z:=by
 let h0 : AnalyticAt ℂ (opPass Y H V Q Qt s j C c f g t v) z:=by
    induction t with
    | nil=> exact (analyticAt_const (v:=(1:(L).Op))) -- tune
    | cons i t ih=>
       change AnalyticAt ℂ (fun z=> (ξ (g i)) (v i) (z i)* (B t) v z) z
       exact AnalyticAt.mul (((contour_analytic Y H V Q Qt s j C c (g i) (v i)) _ (h i (List.Mem.head ..))).comp (f:=fun a: Ρz => a i) ((ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : ι=>ℂ) i).analyticAt _)) (ih fun i t=>h i (List.Mem.tail _ t))
 exact (((innerSL ℂ γ).comp (ContinuousLinearMap.apply ℂ (L) γ)).analyticAt _).comp h0
-- continuous BOTH true offsets *within* Euclidean slot and real Mink translations.
noncomputable def edgeArrival (x:(ι→Axis→ℝ)×(ι→ℝ)):ℂ := arrived Y H V Q Qt s j C c f g t x.1 x.2
lemma edge_cont : Continuous (edgeArrival Y H V Q Qt s j C c f g t) := by
  suffices h: ∀ (w:L), Continuous (fun i:(ι→Axis→ℝ)×(ι→ℝ) => minkPass Y H V Q Qt s j C c f g t i.1 i.2 w) by exact continuous_const.inner (h γ)
  intro w; induction t with
  | nil=> exact continuous_const
  | cons i t ih=>
     change Continuous (fun x : (Ρt) × (Ρ0) => (π (g i)) (x.1 i) (x.2 i) ((μ t) x.1 x.2 w))
     apply mink_cont Y H V Q Qt s j C c (g i) (fun x:(Ρt) × (Ρ0)=>x.1 i) (fun x:(Ρt) × (Ρ0)=>x.2 i) _ ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd) ih
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.edge_cont
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.window_complex
