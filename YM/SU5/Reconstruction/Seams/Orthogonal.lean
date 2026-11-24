import YM.SU5.Reconstruction.Seams.Outcomes
import YM.SU5.Reconstruction.Seams.Far
/-!
# Perpendicular chart prices ONLY on this slab replica arrangement; now in full seam
with ∀ space k-axis imaginary-j displacements along one gap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
variable {J : Calibration}
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
set_option quotPrecheck false
local notation "P"=> (C₀).orthogonalProjectionOnto
local notation "θ"=> flipMark j K
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "κ" p:max=> move K p
local notation "Jj"=> Domain Y H G false (flank j 0)
variable (k₁ : Axis)(C' : Arena Y H G.history.circuit k₁ 0 false)
  (χ' : displayAlgebra Y H V G.history G.clipped k₁ false C' →⋆ₐ[ℂ] ℂ)
variable (u' : j≠k₁)
local notation "S'"=> peninsula Y H V G.history G.clipped k₁ false C' χ'
local notation "G'₀"=> fort Y H V G.history G.clipped k₁ false C' χ'
local notation "J'₀"=> indoor Y H V G.history G.clipped k₁ false C' χ'
local notation "φ"=> eject j
local notation "φ'"=> eject k₁
local notation "θ'"=> flipMark k₁ K
local notation "T'"=> flank k₁ 0
local notation "N'"=> Domain Y H G false (flank k₁ 0)
local notation "Vo'"=> coreOs Y H V G k₁ C' χ'
local notation "ψ₁"=> osValue Y H V G k₁ C' χ'
local notation "Ot'"=> opCarries Y H V G k₁ C' χ'
open Sail
local notation "U'"=> transversal k₁ j u'
variable (U Vt : marks (timeMesh Λ)) (p w : Domain Y H G false (flank j 0)) (d f b t : marks (timeMesh Λ))
include V u'
-- L and R convert to k-time faces through v, w positions. no time price in k for p cutoff.
lemma leftGate (p' : p.val∈ D (lowland k₁ d)
 ): ∃ x : Domain Y H G false (flank k₁ 0), move K (φ (-t)) (flipMark j K p.val)=move K (φ' d) (flipMark k₁ K x.val) := by
  -- L support entirely ≤d along k. choose θ' move(-d) L
  let L' := move K (eject j (-t)) (flipMark j K p.val); let R' := move K (φ' (-d)) L'; let l':= flipMark k₁ K R'
  have h : L'∈ Domain Y H G false (lowland k₁ (d:ℝ)):= by
    apply domain_mono Y H G _ (moving Y H V G (φ (-t)) _ (mirror_support Y H G j p.val p'))
    rintro _ ⟨x,⟨y,b,rfl⟩,rfl⟩; change mirrorE j 0 y k₁ + coordinates Λ _ _ ≤_
    simpa [coordinates_eject,mirrorE,u'.symm] using (show y k₁ ≤ _ from (show y k₁ ≤ d from b))
  have hb : R'∈ Domain Y H G false (lowland k₁ 0):= by
    apply domain_mono Y H G _ (moving Y H V G _ _ h)
    rintro _ ⟨x,e,rfl⟩; change x k₁ + coordinates Λ (φ' (-d)) k₁ ≤0; simp only [coordinates_eject,eject_at, AddSubgroup.coe_neg]; linarith [show x k₁ ≤ d from e]
  have hv : l'∈Domain Y H G false (flank k₁ 0):= domain_mono Y H G (by
    rintro _ ⟨x,h,rfl⟩; change 0≤ mirrorE _ _ x k₁; simpa [mirrorE] using (show x k₁ ≤ 0 from h)) (mirror_support Y H G k₁ _ hb)
  refine ⟨⟨l',hv⟩, ?_⟩; change L'= move K _ (θ' l'); unfold l' R'; rw [mirror_twice, move_sum,selectRay,add_neg_cancel,eject_zero,move_by_zero]

lemma rightGate (p': w.val∈ D (flank k₁ (d:ℝ))) : ∃ x: Domain Y H G false (flank k₁ 0), move K (φ t) w.val= move K (φ' d) x.val := by
  let R':= move K (φ t) w.val; let x:= move K (φ' (-d)) R'
  have hv : x ∈ Domain Y H G false (flank k₁ 0) := domain_mono Y H G (by
    rintro _ ⟨q,⟨y,h,rfl⟩,rfl⟩; change 0≤ (y k₁ + coordinates Λ (φ t) k₁)+coordinates Λ (φ' (-d)) k₁; simp only [coordinates_eject,eject_at, eject_away j _ k₁ u'.symm, add_zero,AddSubgroup.coe_neg]; linarith [show (d:ℝ) ≤ y k₁ from h]) (moving Y H V G (φ' (-d)) _ (moving Y H V G (φ t) _ p'))
  exact ⟨⟨x,hv⟩, (by change R'= move K (φ' d) x; unfold x; rw [move_sum,selectRay,add_neg_cancel,eject_zero,move_by_zero])⟩
omit V u'
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
  (tC' : saunters Y H V G.history G.clipped k₁ false C' χ' = ⊤)
  (eT : osValue Y H V G k₁ C' χ'= osValue Y H V G j C χ)
  (cC' : ConePrice.Forward (peninsula Y H V G.history G.clipped k₁ false C' χ'))
local notation "T₂"=> (f + Vt + (f-(d+U))) -- layout PA `[d,d+U]` PB `[f,f+Vt]`, R at T₂

private lemma hdist (h : d+U<f): 0< ((f-(d+U)): Gt) := sub_pos.mpr h
local notation "δ₁"=> (f-(d+U))
-- local notation for motion δ positivity not embed data

include V u' tC' eT cC'
lemma cross_chart (h : d+U<f) {x y:Sky (tent Y H)} {A B:(J'₀).Op}
    (a:Follows Y H V G k₁ C' χ' (move K (φ' (-d)) x) U A) (b':Follows Y H V G k₁ C' χ' (move K (φ' (-f)) y) Vt B)
    (X Y' : Domain Y H G false (flank k₁ 0))
    (c:move K (φ (-t)) (θ p.val)=move K (φ' d) (θ' X.val))(z': move K (φ t) w.val=move K (φ' T₂) Y'.val) (i:Gt) :
    let r:= Real.toNNReal ((f-(d+U) : marks (timeMesh Λ)):ℝ)
    let pr : 0 < r:= Real.toNNReal_pos.mpr (show 0 < ((δ₁:Gt):ℝ) from sub_pos.mpr h) -- fais
    let Sail₀ := Sail.transverse (S') cC' U' (le_of_eq (transversal_norm ..)) r pr
    ∃ k: chron0 j t i p.val x y w.val∈ D univ,
      osValue Y H V G j C χ ⟨chron0 j t i p.val x y w.val,k⟩= inner ℂ (Vo' X) (Ot' A (Sail₀ (i:ℝ) (Ot' B (Sail₀ (-(i:ℝ)) (Vo' Y'))))) := by
  intro r hu M
  let V₀:=φ' d; let V₁:=φ i+φ' f; let W:=φ' T₂
  have a₀: V₁-(V₀+φ' U)=φ' δ₁ +φ i:= by unfold V₀ V₁; simp only [sub_eq_add_neg, eject_neg, ← selectRay]; abel
  have a₁: W-(V₁+φ' Vt)=φ' δ₁+φ (-i):=by unfold W V₁; simp only [sub_eq_add_neg, eject_neg, ← selectRay]; abel
  have hx: 0 ≤ (δ₁:Gt):=(sub_pos.mpr h).le
  obtain ⟨k₀,k⟩:= purchases Y H V G k₁ C' χ' tC' (move K (φ' (-d)) x) (move K (φ' (-f)) y) U Vt A B V₀ W V₀ V₁ X Y' a b' (by simp) (by rw [a₀]; simp only [Pi.add_apply,eject_at,eject_away j _ k₁ u'.symm,add_zero]; exact hx) (by rw [a₁]; simp only [Pi.add_apply,eject_at,eject_away j _ k₁ u'.symm,add_zero]; exact hx)
  have hb : tab K V₀ V₀ V₁ W (θ' X.val) (move K (φ' (-d)) x) (move K (φ' (-f)) y) Y'.val=chron0 j t i p.val x y w.val := by
    unfold V₀ V₁ W tab chron0; dsimp only [tab]; rw [←c,← z', move_sum,selectRay,add_neg_cancel,eject_zero,move_sum]; rw [show φ i+φ' f+φ' (-f)=φ i from by rw [add_assoc,selectRay,add_neg_cancel,eject_zero,add_zero]]
  rw [sub_self,a₀,a₁,across_time Y H V G k₁ C' χ' j δ₁ i u',across_time Y H V G k₁ C' χ' j δ₁ (-i) u'] at k
  rw [show bridgeEstate Y H V G k₁ C' χ' 0 = ContinuousLinearMap.id ℂ _ from (by rw [show (bridgeEstate Y H V G k₁ C' χ') 0=bridgeEstate Y H V G k₁ C' χ' (eject k₁ (0:Gt)) from by rw [eject_zero], bridge_time]; simp only [AddSubgroup.coe_zero,Real.toNNReal_zero,OS.Semigroup.eZero])] at k
  refine ⟨hb ▸ k₀,(by
    rw [←eT,show (⟨chron0 ..,_⟩ : D univ)=(⟨tab ..,k₀⟩ : D univ) from Subtype.ext hb.symm,k]; unfold M Sail.transverse; erw [on_strip (S') cC' U' (le_of_eq (transversal_norm k₁ u')) r hu, ← Complex.ofReal_neg,on_strip (S') cC' U' (le_of_eq (transversal_norm k₁ u')) r hu]; rfl)⟩
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
