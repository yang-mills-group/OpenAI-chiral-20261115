import YM.SU5.Selected.Debut
import YM.SU5.Selected.ThresholdInteraction
/-! # Reconstruct threshold with all three tens and all three fivesBar, on
one gauge field and in a single selected component on this very law.
`Slot` here includes components within each family! no claim recipes will
be LINEAR in their slot (in particular averaging can identify colors).
Relativistic completion still SCOPE separate. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 400000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (C : Arena Y H Q.circuit 0 0 false)
open Tapestry _root_.YM.SelectionAnalysis CF.Pannier.Chancel
variable (S : Finset Cover)
local notation "𝔄" => Ark.Ht Y H Q.circuit 0 0 false C
local notation "ℛ" => Aurora Y H V Q 0 false C
local notation "R₀" => groundRoom Y H V Q 0 false C
local notation "𝔅" => driveAlgebra Y H V Q Qt 0 false C
local notation "A" => displayAlgebra Y H V Q Qt 0 false C
local notation "ω₀" => floorV Y H Q.circuit 0 0 false C
local notation "π" => (ℛ).orthogonalProjectionOnto
local notation "Ω₀" => seat0 Y H V Q 0 false C
local notation "qv" s:max i:max x:max => entrance Y H V s Q Qt 0 false C i x
local notation "P₁" t:max => actor Y H t Q.circuit 0 0 false C
local notation "σ" => ruler Λ.block
local notation "Ρ" x:max => indoor Y H V Q Qt 0 false C x
local notation "κ₀" f:max t:max x:max => bud Y H V t Q Qt 0 false C f x

variable {q d w : ℕ} {R A' : ℝ} (z : SU.Slot)
local notation "B" => payout d q w
local notation "φ" x:max => located Y H V s Q Qt 0 false C x
open OS.Ground
lemma all_wines (P : Panel Y H V Q Qt 0 false C) (h : Issued Y H V Q Qt 0 false C P)
    (F : SU.Slot → observable (tent Y H) true) (x : ∀ z, Worthy Y H V s Q Qt C z q d w (F z)) :
    ∃ᶠ i in ae P.μ, ∀ z:SU.Slot, 3/4 ≤ ‖response Y H V s Q Qt 0 false C (P.character i) (bosonLabel (tent Y H) (F z))‖:=by
  let f (z:SU.Slot) := (show Marks K false from bosonLabel K (F z)); let W(i:P.X)(z:SU.Slot):=response Y H V s Q Qt 0 false C (P.character i) (1+f z); let c (i:P.X) (z:SU.Slot) := ‖W i z‖^2
  let T i := ∑ z:SU.Slot,c i z
  letI := h.normalized
  have h1 (z) : Integrable (fun i=> c i z) P.μ:= Continuous.integrable_of_hasCompactSupport (((h.weak (φ (1+f z))).norm).pow _) (HasCompactSupport.of_compactSpace _)
  have hT : Integrable T P.μ:= integrable_finsetSum _ fun i _=> h1 i
  have he : ∀ z:SU.Slot,(∫ i,c i z∂P.μ) ≤ (1:ℝ)/2048:= fun z => (Panes.Shines.energyMatch («A»:= (displayAlgebra Y H V Q Qt 0 false C)) h (φ (1+f z))).trans_le (x z).price
  have hh : ∃ᶠ i in ae P.μ,T i < (1:ℝ)/16:=by
    intro k; have hz : ∀ᵐ i ∂P.μ,T i ≥ (1:ℝ)/16:=k.mono fun i => le_of_not_gt
    have hi : (∫ i,T i∂P.μ) ≥ 1/16:=by simpa using integral_mono_ae (integrable_const _) hT hz
    have hi0:(∫ i,T i∂P.μ) ≤ (45:ℝ)/2048:=by unfold T; rw [integral_finsetSum _ (fun i _=> h1 i)]; refine (Finset.sum_le_sum (fun i _=> he i)).trans ?_; rw [Finset.sum_const,Finset.card_univ,SU.slots]; norm_num
    linarith
  apply hh.mono; intro i hi z
  let r := response Y H V s Q Qt 0 false C (P.character i) (f z)
  have hv0:c i z<1/16:= lt_of_le_of_lt (Finset.single_le_sum (fun x _=> show 0≤ c i x from sq_nonneg _) (Finset.mem_univ z)) hi
  have hv: ‖W i z‖≤1/4:=by unfold c at hv0; nlinarith
  have hW: W i z-r=1:=by unfold W r response; rw [map_add,map_add,located_one,map_one]; ring
  change _≤ ‖r‖
  linarith only [hv,norm_sub_le (W i z) r, show (1:ℝ)=‖W i z-r‖ from by rw [hW,norm_one]]

lemma vintage_chosen (g : Papal.Korn Y H q d w R A') (P : Panel Y H V Q Qt 0 false C)
    (h : Issued Y H V Q Qt 0 false C P) (c : ∀ j, Arena Y H Q.circuit j 0 false) :
    ∀ᶠ s in atTop, ∃ F : SU.Slot → observable (tent Y H) true, ∃ᶠ x in ae P.μ, ∀ z:SU.Slot,
      ThresholdInteraction Y H V s Q Qt 0 C (Sen (grain B) B) (P.character x) (F z) z (grain B) q d ∧
      3/4 ≤ ‖response Y H V s Q Qt 0 false C (P.character x) (bosonLabel (tent Y H) (F z))‖ ∧
      ∀ k : Axis, ThresholdInteraction Y H V s Q Qt k (c k) (Sen (grain B) B) (displacement Y H V Q Qt 0 false C (P.character x) k (c k)) (F z) z (grain B) q d:=by
  filter_upwards [covalues Y H V Q Qt C g] with s t
  choose F p using t; refine ⟨F,?_⟩
  apply ((all_wines Y H V s Q Qt C P h F p).and_eventually (full_house Y H V Q Qt 0 false C P h c)).mono
  intro i t z; have ht:= (t.1 z).trans' (show (1:ℝ)/4≤3/4 by norm_num)
  refine ⟨threshold_interaction Y H V s Q Qt 0 C _ _ _ (survive Y H V s Q Qt 0 C (p z).indeed t.2.1 ht), t.1 z, fun k=> threshold_interaction Y H V s Q Qt k _ _ _ _ (survive Y H V s Q Qt k (c k) (p z).indeed (t.2.2 k) ?_)⟩
  rw [across_response]; exact ht

theorem single_winemaker (ε η : ℝ) (h : 0 < η) (U : Supplier) :
    ∃ (P : Preparation) (l : ℕ) (Z₁ : ℝ), ε < P.x ∧ P.d ≤ η ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧ decorate U P l Z₁ ≤ P.h ∧
    ∃ (H : Real.exp 1 ≤ P.x) (Y : Course P (VolumeCape.Dream.Nimbus l))
      (a b : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ)
      (E : ℕ → Family (tent Y H) → ℂ) (V : Universal Y H a b I E)
      (R : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H)
      (q d w s : ℕ) (C : ℝ) (c : ∀ j:Axis, Arena Y H R.history.circuit j 0 false)
      (A' : Panel Y H V R.history R.clipped 0 false (c 0)),
      let o := grain (payout d q w); let S:=Sen o (payout d q w)
      Papal.Korn Y H q d w C Z₁ ∧ Issued Y H V R.history R.clipped 0 false (c 0) A' ∧
      (∀ F j, ∫ i, response Y H V j R.history R.clipped 0 false (c 0) (A'.character i) F ∂A'.μ = E j F.val) ∧
      ∃ (F : SU.Slot → observable (tent Y H) true) (x:A'.X), ∀ z:SU.Slot,
        ThresholdInteraction Y H V s R.history R.clipped 0 (c 0) S (A'.character x) (F z) z o q d ∧
        ∀ k:Axis, ThresholdInteraction Y H V s R.history R.clipped k (c k) S (displacement Y H V R.history R.clipped 0 false (c 0) (A'.character x) k (c k)) (F z) z o q d:=by
  obtain ⟨P,l,R,u,k,g,G,H,Y,_,_,_,q,d,w,C,g',a,b,I,E,u0,_,_,_,A',_⟩ := Papal.elevation ε η h U
  let V := A'.univ_; obtain ⟨Q⟩ := SatinVerification.extend_ground Y H V
  let c (i:Axis) := Classical.choice (voyage_H Y H V Q.history.circuit i 0 false)
  obtain ⟨P',t⟩ := display_receives Y H V Q.history Q.clipped 0 false (c 0)
  letI := t.normalized
  obtain ⟨s,F,f⟩ := (vintage_chosen Y H V Q.history Q.clipped (c 0) g' P' t c).exists
  obtain ⟨x,e⟩ := f.exists
  exact ⟨P,l,R,u,k,G,g,H,Y,a,b,I,E,V,Q,q,d,w,s,C,c,P',g',t,fun F j=> survives_check Y H V j Q.history Q.clipped 0 false (c 0) P' t F,F,x,fun i=> ⟨(e i).1,(e i).2.2⟩⟩
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.single_winemaker
#check @YM.CF.Buffered.Afterglow.Tower.Selected.single_winemaker
