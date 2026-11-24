import YM.SU5.Reconstruction.Seams.Orthogonal
import YM.SU5.Reconstruction.Seams.Bills
/-!
# Bound speed in Limit. Perpendicular chart prices ONLY on this slab replica arrangement; now in full seam
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
local notation "𝔉"=> osValue Y H V G j C χ
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
-- Have $A_n$ and $B_n$ purchases, complete hinge prices along k. Also explicit conditions on δ-time window. Strong closure of operators thus can be sought; these are *physical* prices on same state.
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
  (tC' : saunters Y H V G.history G.clipped k₁ false C' χ' = ⊤)
  (eT : osValue Y H V G k₁ C' χ'= osValue Y H V G j C χ)
  (cC : ConePrice.Forward (peninsula Y H V G.history G.clipped j false C χ))
  (cC' : ConePrice.Forward (peninsula Y H V G.history G.clipped k₁ false C' χ'))
local notation "T₂"=> (f + Vt + (f-(d+U)))
local notation "δ₁"=> (f-(d+U))
local notation "Vo"=> coreOs Y H V G j C χ
local notation "Ot"=> opCarries Y H V G j C χ
open Sail

structure Slice (x : ℕ→Sky (tent Y H)) (h:ℕ→marks (timeMesh Λ)) (T:ℕ→ (indoor Y H V G.history G.clipped j false C χ).Op)
    (A : (fort Y H V G.history G.clipped j false C χ).Op) : Prop where
  forever (n:ℕ): Follows Y H V G j C χ (x n) (h n) (T n)
  cloudy (n:ℕ) : 0< ((h n:marks (timeMesh Λ)):ℝ)
  timing : Tendsto (fun n => ((h n:marks (timeMesh Λ)):ℝ)) atTop (𝓝 0)
  carriage : Anchors (H:=fort Y H V G.history G.clipped j false C χ) (fun n=> opCarries Y H V G j C χ (T n)) A

structure Perpendicular (x:ℕ → Sky (tent Y H)) (T:ℕ→(indoor Y H V G.history G.clipped k₁ false C' χ').Op) : Prop where
  beyond (n:ℕ): Follows Y H V G k₁ C' χ' (move K (φ' (-d)) (x n)) U (T n)
  bounded : ∃ c:ℝ,∀ n, ‖opCarries Y H V G k₁ C' χ' (T n)‖ ≤ c

section localizing
variable {U Vt d f} {x y : ℕ → Sky (tent Y H)} {u v:ℕ → marks (timeMesh Λ)}
  {X W:ℕ → (indoor Y H V G.history G.clipped j false C χ).Op} {D₀ D₁: ℕ→(indoor Y H V G.history G.clipped k₁ false C' χ').Op}
  {A B : (fort Y H V G.history G.clipped j false C χ).Op}
  (X₀:Slice Y H V G j C χ x u X A) (X₁:Slice Y H V G j C χ y v W B)
  (b₀:Perpendicular Y H V G k₁ C' χ' U d x D₀) (b₁:Perpendicular Y H V G k₁ C' χ' Vt f y D₁)

-- `Perpendicular` parameters order check
include u' tC tC' eT cC' X₀ X₁ b₀ b₁
set_option maxHeartbeats 850000 in
lemma crosses (r:ℝ) (t' : 0<(t:ℝ)) (δ : d+U<f) (q: |r|< (δ₁:ℝ))
    (lp : p.val∈ Domain Y H G false (lowland k₁ (d:ℝ))) (rp : w.val∈ Domain Y H G false (flank k₁ (T₂:ℝ))) :
    let E₁:= (S).E (Real.toNNReal (t:ℝ))
    inner ℂ (E₁ (Vo p)) (A (LorTime (S) r B (E₁ (Vo w))))=
      inner ℂ (E₁ (Vo p)) (LorTime (S) r B (A (E₁ (Vo w)))):=by
  obtain ⟨Z₀,h₀⟩:= leftGate Y H V G j k₁ u' p d t lp -- order
  obtain ⟨Z₁,h₁⟩:= rightGate Y H V G j k₁ u' w T₂ t rp
  let hu:=X₀.timing; let hv:=X₁.timing
  have hQ : 0< (δ₁:ℝ):= (show 0 < δ₁ from sub_pos.mpr δ)
  let ρ:= Real.toNNReal (δ₁:ℝ); let e:= Real.toNNReal_pos.mpr hQ
  have h:=le_of_eq (transversal_norm k₁ u'); let F(i:ℕ):= screen (S') cC' (transversal k₁ j u') h ρ e (Ot' (D₀ i)) (Ot' (D₁ i)) (Vo' Z₀) (Vo' Z₁)
  let b : ∀ n:ℕ,∀ a:Gt, ∃ k: chron0 j t a p.val (x n) (y n) w.val∈ D univ,
    osValue Y H V G j C χ ⟨chron0 j t a p.val (x n) (y n) w.val,k⟩ = F n (a:ℝ):= fun n i=> cross_chart Y H V G j C χ k₁ C' χ' u' U Vt p w d f t tC' eT cC' δ (b₀.beyond n) (b₁.beyond n) Z₀ Z₁ h₀ h₁ i -- RHS defeq neg cast complex? ima of -(i:ℝ) vs -(↑..:ℂ), not defeq.
  have e₀ : (ρ:ℝ)=(δ₁:ℝ):= Real.coe_toNNReal _ hQ.le
  obtain ⟨a₁,u₁⟩:= b₀.bounded; obtain ⟨a₂,u₂⟩:= b₁.bounded
  refine seam_bill (S) (Real.toNNReal (t:ℝ)) A B (Vo p) (Vo w) X₀.carriage X₁.carriage hu hv (Real.toNNReal_pos.mpr t') e (daylight (timeMesh Λ)) (F:=F) (fun i=> slit_opens (S') cC' _ h ρ e _ _ _ _) ⟨_,fun i _ hh=> anchored_cost (S') cC' _ h ρ e _ _ _ _ (u₁ i) (u₂ i) hh⟩ ?_ ?_ r (show |r| < (ρ:ℝ) from by rw [e₀]; exact q)
  · intro i u₀ q₀; rw [Real.coe_toNNReal _ t'.le] at u₀; let q : Gt:=⟨i,q₀⟩
    have hm : ∀ᶠ i' in atTop, (u i':ℝ) < i ∧ (v i':ℝ)< (t:ℝ)-i:= (hu.eventually (Iio_mem_nhds u₀.1)).and (hv.eventually (Iio_mem_nhds (sub_pos.mpr u₀.2)))
    filter_upwards [hm] with n ⟨p₀,p₁⟩
    have hw: q+v n≤t:=show (i:ℝ)+(v n:ℝ)≤t from (by linarith)
    obtain ⟨t₁,e⟩:= opens_right Y H V G j C χ p w tC (X₀.forever n) (X₁.forever n) t q t'.le p₀.le hw
    exact e.symm.trans (b n q).choose_spec
  intro i u₀ q₀; rw [Real.coe_toNNReal _ t'.le] at u₀; let q : Gt:=⟨i,q₀⟩
  have hm : ∀ᶠ i' in atTop, (v i':ℝ)< -i ∧ (u i':ℝ)< t:= (hv.eventually (Iio_mem_nhds (neg_pos.mpr u₀.2))).and (hu.eventually (Iio_mem_nhds t'))
  filter_upwards [hm] with n ⟨p₀,p₁⟩
  have hw: q+v n≤0 := show (i:ℝ)+(v n:ℝ)≤0 from (by linarith)
  obtain ⟨t₁,e⟩:= opens_left Y H V G j C χ p w tC (X₀.forever n) (X₁.forever n) t q t'.le hw u₀.1.le p₁.le
  exact e.symm.trans (b n q).choose_spec
include cC
lemma real_locality (r:ℝ) (δ : d+U<f) (q: |r|< (δ₁:ℝ)) : Commute A (LorTime (S) r B) := by
  let t: marks (timeMesh Λ):= notch (timeMesh Λ) 0 1; have e : 0 < (t:ℝ):= by change 0< bell (timeMesh Λ) 0 1; unfold bell; simpa using mill_pos (timeMesh Λ) 0
  let E₁:=(S).E (Real.toNNReal (t:ℝ)); let W' := far Y H V G j C χ k₁
  let Z i q := E₁ '' (W' i q : Set G₀)
  have he i p : Dense (Z i p):= ((S).whole (Real.toNNReal (t:ℝ))).dense_image E₁.continuous (far_dense Y H V G j C χ k₁ u'.symm tC cC i p)
  change A*(LorTime (S) r B)=LorTime (S) r B * A
  ext1 z; refine closure_minimal ?_ (isClosed_eq (ContinuousLinearMap.continuous (A * (LorTime (S) r B))) (ContinuousLinearMap.continuous (LorTime (S) r B*A))) (he (T₂:ℝ) true z)
  rintro _ ⟨v0,hv,rfl⟩
  apply Dense.eq_of_inner_right ℂ (he d false); rintro _ ⟨p0,hu,rfl⟩
  obtain ⟨v0,rfl⟩:=LinearMap.mem_range.mp hv; obtain ⟨p0,rfl⟩:=LinearMap.mem_range.mp hu
  let p00 : Domain Y H G false (flank j 0) := ⟨p0.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left p0.property)⟩; let v00 : Domain Y H G false (flank j 0):=⟨v0.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left v0.property)⟩
  exact (crosses Y H V G j C χ k₁ C' χ' u' p00 v00 t tC tC' eT cC' X₀ X₁ b₀ b₁ r e δ q (domain_loose Y H G _ (domain_mono Y H G inter_subset_right p0.property)) (domain_loose Y H G _ (domain_mono Y H G inter_subset_right v0.property)))
end localizing
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
