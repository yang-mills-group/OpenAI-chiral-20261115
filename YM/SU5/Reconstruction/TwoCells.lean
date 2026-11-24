import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.TestInteraction
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H

open _root_.YM.CF.Pannier.Chancel
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  (D : Exhibition Y H i k I E L B)
variable (j d : Axis) (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
local notation "χ₀" => Dome (tent Y H)
local notation "Ĉ" => euclideanHalf Λ l (tent Y H) j
variable (c : (displayAlgebra Y H V G.history G.clipped d false (T d)) →⋆ₐ[ℂ] ℂ)
local notation "χ" => Selected.displacement Y H V G.history G.clipped d false (T d) c j (T j)
local notation "rχ" => resident Y H V G d false (T d) c
local notation "ρ" => indoor Y H V G.history G.clipped j false (T j) χ
local notation "P" => procession Y H V G.history G.clipped j false (T j) χ
local notation "Ω" => doorstep Y H V G.history G.clipped j false (T j) χ
local notation "Ψ" => matchGNS Y H V G j false (T j) d (T d) c
local notation "𝒱" s:max x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x
local notation "Θ" => onDrawing Y H V G D d T rχ
local notation "Mx" => evaluate Y H V G d T rχ
local notation "Ex" s:max => Selected.response Y H V s G.history G.clipped j false (T j) χ
variable (S : Finset Cover)
variable (s q t : ℕ) (o : Cover) (z : SU.Slot) (f : Selected.Marks (tent Y H) true)
local notation "C₀" s:max => insertAt Y H s
local notation "σ" n:max => silhouette Λ l n
variable (p a : Cover) (δ : ℝ)
local notation "U" => leftCell j K p S
local notation "U'" => rightCell K a S
local notation "f₊" => relocateWorld Y H true a f
local notation "fₘ" => Selected.mirrorInMarks Y H j true (relocateWorld Y H true p f)
local notation "u₊" => insertAt Y H s f₊
local notation "uₘ" => insertAt Y H s fₘ
local notation "u" => uₘ*u₊
local notation "μ" n:max => vistaFinish Y H (s+n) D
local notation "χₙ" n:max F:max => stream Y H G.refine s n F
open SelectionAnalysis OS.Semigroup
local notation "Γ" => saunters Y H V G.history G.clipped j false (T j) χ
local notation "S₀" => peninsula Y H V G.history G.clipped j false (T j) χ
local notation "W" F:max => land Y H V s G.history G.clipped j false (T j) χ F
local notation "inH" x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x

-- render as Dome extension with whole resolution product.
noncomputable def useAt {J : Calibration} {S : Finset Cover} (s : ℕ) {F : Family J}
    (t : InTest J false S false F) : Cloud (Dome J) :=
  pinhole _ s (⟨F,aux_test t.widen⟩ : Dome J)

lemma useAt_qualified {J : Calibration} {wideU : Set RSpace} {S : Finset Cover} {F : Family J} (t : InTest J false S false F) (e : printedHere Λ l s S (handstamp wideU)) :
    useAt s t∈jetty Λ l J false (handstamp wideU) (Set.Iic s) :=
  pokes _ _ (Set.mem_Iic.mpr (le_refl s)) (show (⟨F, aux_test t.widen⟩ : Dome J)∈ keep Λ l s J false (handstamp wideU) from ⟨S,t,e⟩)
lemma useAt_value {S : Finset Cover} {F : Family (tent Y H)} (t : InTest K false S false F) : Θ (useAt s t)=Mx s F:= plugged Y H V G D d T rχ s _

section product
-- assay at the gauge-covariant extension, so factors separately need not be singlets.
local notation "μp" => Selected.remotePair j K p a
lemma extended_assay
    (h : ThresholdInteraction Y H V s G.history G.clipped j (T j) S χ f z o q t)
    (w : Exceeds Y H V s G.history G.clipped j (T j) χ δ f z S o q t p a) :
    ∃ (x y : Family (tent Y H)) (F F' : PairsC → ℂ) (M : x∈ Lode (tent Y H) (Window.family z) (booty o t q) S)
        (N : y∈ Lode (tent Y H) (Window.family z) (booty o t q) S) (A : Coeff false S F) (A' : Coeff false S F'),
        let m₁ := (useAt s (tested_narrow j p a (Lode_test M) (Lode_test N)))
        let m₂ := (useAt (J:=tent Y H) s (tested_narrow j p a (InTest.seed A) (InTest.seed A')))
        let r := jetty Λ l K false (handstamp (silhouette Λ l s (U∪U'))) (Set.Iic s)
        m₁∈r ∧ m₂∈r ∧ Θ m₁=0 ∧ Θ (m₂*m₁)≠0 := by
  have hx:= w.shelf.paid
  rw [← total_extension Y H V G j d T c s] at hx
  unfold Selected.RemoteSplit at hx; push Not at hx
  obtain ⟨x,hx,y,hy,F,F',A,A',e⟩ := hx
  have zeroPrice : Mx s (μp x y)=0 := by
    rw [total_extension Y H V G j d T c s]
    exact remote_cold Y H V s G.history G.clipped j (T j) χ a U (detached_disjoint w.shelf.structured)
      _ (axial _ j 0 (cad_test p ordinate (Lode_test hx).widen)) _ h.witness.link.anchor_inj _ y hy
  rw [zeroPrice,mul_zero, Selected.remotePair_factors j (tent Y H) p a (aux_test (Lode_test hx).widen)
    (aux_test (InTest.seed («K»:=tent Y H) A').widen)] at e
  let t₁:= tested_narrow (J:=tent Y H) j p a (InTest.seed A) (InTest.seed A')
  let t₂:= tested_narrow j p a (Lode_test hx) (Lode_test hy)
  have hm₁ : Θ (useAt s t₂)=0:= (useAt_value Y H V G D d T c s t₂).trans zeroPrice
  refine ⟨x,y,F,F',hx,hy,A,A',useAt_qualified s t₂ (supported_iff.mpr Set.Subset.rfl), useAt_qualified s t₁ (supported_iff.mpr Set.Subset.rfl), hm₁,?_⟩
  intro hz
  have hg : Θ ((useAt s t₁)*(useAt s t₂))=Θ (useAt s (t₁.mul t₂)) := congrArg Θ ((map_mul (pinhole χ₀ s) _ _).symm)
  rw [useAt_value] at hg
  exact e (hg.symm.trans hz)
end product

section visible
lemma footprint_pair
    (h : f.val∈ _root_.YM.CF.Pannier.Chancel.Filigree K (Window.family z) (booty o t q) S) :
    InTest K false U false (fₘ).val ∧ InTest K false U' false (f₊).val := by
  have he (r : Cover) : InTest K false (rightCell K r S) false (relocateWorld Y H true r f).val := by
    rw [world_val]; exact chart_narrow ordinate r (FilTest h)
  exact ⟨axial K j 0 (he p), he a⟩

lemma partner_cost
    (h : ThresholdInteraction Y H V s G.history G.clipped j (T j) S χ f z o q t)
    (w : Exceeds Y H V s G.history G.clipped j (T j) χ δ f z S o q t p a) :
    ----- one actual gauge–matter interaction test in the stated RemoteSplit sense
    Disjoint (silhouette Λ l s U) (silhouette Λ l s U') ∧
    (∀ i:Axis,∀ x∈ silhouette Λ l s U, ∀ y∈ silhouette Λ l s U', x i+δ≤ y i) ∧
    (¬ Selected.RemoteSplit j K p a S (booty o t q) (Window.family z) (Mx s)) ∧
    uₘ∈ circum Λ l K false (silhouette Λ l s U) (Set.Iic s) ∧
    u₊∈ circum Λ l K false (silhouette Λ l s U') (Set.Iic s) ∧
    u∈ circum Λ l K false (silhouette Λ l s (U∪ U')) (Set.Iic s) ∧
    1/32 ≤ ‖Θ (u)‖ := by
  obtain ⟨x,y⟩ := footprint_pair Y H j S q t o z f p a h.witness.link.mark_mem
  have hx:= insert_visible (s:=s) Y H fₘ x; have hy:= insert_visible (s:=s) Y H f₊ y
  rw [total_extension Y H V G j d T c s,←map_mul]
  refine ⟨stamp_disjoint (w.shelf.span_positions j),fun i x z y v=>stamp_range (w.shelf.span_positions i) z v,
      w.shelf.paid,hx,hy,insert_visible Y H _ (x.mono Finset.subset_union_left |>.mul (y.mono Finset.subset_union_right)),?_⟩
  rw [draw_read Y H V G D j]; exact w.shelf.consumption

lemma further_partners
    (h : ThresholdInteraction Y H V s G.history G.clipped j (T j) S χ f z o q t)
    (w : Exceeds Y H V s G.history G.clipped j (T j) χ δ f z S o q t p a) (n : ℕ) :
    (((μ n) u).val=(χₙ n (fₘ).val)*(χₙ n (f₊).val) ∧ Θ u=Mx (s+n) ((μ n) u).val) ∧
      InTest K true (volumeAround Λ l n U) false (χₙ n (fₘ).val) ∧
      InTest K true (volumeAround Λ l n U') false (χₙ n (f₊).val) := by
  obtain ⟨x,y⟩ := footprint_pair Y H j S q t o z f p a h.witness.link.mark_mem
  have ht:u=(C₀ s) (fₘ*f₊):= (map_mul ..).symm
  rw [ht]
  refine ⟨⟨(further_finish Y H V G D s n (fₘ*f₊)).trans (w.persisting n).1,
    drawAt Y H V G D d T rχ ?_⟩, (proceeds Y H G.history.circuit s n x.widen).1,
    (proceeds Y H G.history.circuit s n y.widen).1⟩
  exact Tapestry.Altitude.climbs (Dome K) (Nat.le_add_right s n) (short_pinhole s (resolutionProbe Y H (fₘ*f₊)))

-- carry to same representation (interior equality extends even to real time, by later crossing proof; here at zero)
lemma interaction_vectors
    (w : Exceeds Y H V s G.history G.clipped j (T j) χ δ f z S o q t p a) :
    ∃ x y : Tower.Field Y H s j 0 true,
      let g := Selected.admit Y H s j x; let m := Selected.admit Y H s j y
      x.val=(relocateWorld Y H true p f).val ∧ y.val=(f₊).val ∧
      Θ u = inner ℂ (inH g) (inH m) ∧
      Θ u = inner ℂ (W g) (W m) ∧
      (∀ᶠ v : RSpace in 𝓝 0, 1/33 ≤ ‖inner ℂ (W g) ((S₀).E (v j).toNNReal ((S₀).U (diameter v) (W m)))‖) := by
  obtain ⟨x,y,h,t,e,hx,z,R⟩ := w.extendsTo
  have hp (x : Tower.Field Y H s j 0 false) (F : Marks (tent Y H) true) (e : x.val=F.val) : x.val∈ purpose (tent Y H) (meshface (Λ:=Λ) 0 s) j true :=
    (purpose_ok ..).2 ⟨((purpose_ok ..).1 x.property).1, fun _ => e.symm ▸ (marksSpec true F).2 rfl⟩
  have hz : Θ u=(Ex s) (bosonLabel K (fₘ*f₊)) := by rw [←map_mul, draw_read Y H V G D j]
  refine ⟨⟨_,hp x _ h⟩,⟨_,hp y _ t⟩,h,t,hz.trans ?_,(hz.trans z.symm).trans ?_,hx.mono fun v p=> ?_⟩
  · have ht := congrArg₂ (fun a b=>mirror (tent Y H) j 0 a*b) h t
    exact ((congrArg (Ex s) (Subtype.ext ht.symm : bosonLabel K (fₘ*f₊) =
      (Selected.mirrorInMarks Y H j false (Selected.futureMark Y H s j false x))* (Selected.futureMark Y H s j false y))).trans (Selected.earns Y H V s G.history G.clipped j false (T j) χ x y).symm)
  · change scene Y H V s G.history G.clipped j false (T j) χ x y 0=_
    rw [peninsula_window]; rw [show SelectionAnalysis.diameter (a:=j) 0=0 from (show (OS.Semigroup.SEP j) 0=0 from map_zero _), (S₀).uZero]; simp only [Pi.zero_apply,Real.toNNReal_zero,(S₀).eZero]; rfl
  exact p.trans_eq (congrArg norm (peninsula_window Y H V s G.history G.clipped j false (T j) χ x y v))
end visible
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.extended_assay
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.further_partners
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.interaction_vectors
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.partner_cost
