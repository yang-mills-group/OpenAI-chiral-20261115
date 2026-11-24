import YM.SU5.Reconstruction.PilotLight.Prefix
/-! In THIS epoch, solvability and response of the plugged-in density. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 370000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Lat Fock
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "Ω₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "Θ"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "Os"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Ps"=> Follows Y H V G j (c j) χ
local notation "Sₚ"=> splice Y H V G j (c j) χ
variable (s t w n:ℕ) (u : marks (timeMesh Λ)) (S:Finset Cover) (r δ:ℝ)(p:placement Λ)
local notation "B₁" => alcove (hAll Λ t w n)
local notation "Σ" => bufferedHull Λ l s S
local notation "O" => slides (coordinates Λ p) (alcove (hAll Λ t w n))
variable {x:Dome (tent Y H)}
local notation "Z"=> salute Y H G s
-- authorized prolongations along ANY ONE cost path.Times.Stop.
local notation "A₀"=> flank j r
variable {d q vm:ℕ} {x0:ℕ → SU.Slot → Dome (tent Y H)} {l0 N:ℕ→ℕ} {R:ℝ}
variable (W:Trail Y H V G c w q d vm R N l0 x0)
variable (z:SU.Slot)(h:ReadySet (l:=l) j s u S r δ p)(σ:0<δ)
include W h
local notation "P" i:max=> lantern (tent Y H) (x0 i z) w (N i)
local notation "Sₐ"=> district q d vm
local notation "L₀"=> tileA q d vm
local notation "θ" i:max=> bAll Λ (l0 i) w (N i)
local notation "hw"=> powered Y H V G c W
local notation "Kₚ" i:max=> motor Y H V G j c χ W z i
local notation "Rₚ"=>startLens Y H V G j (c j) χ s u h.buys.high
local notation "Gk" i:max=> witnessedKet Y H V G j c χ s (l0 i) w (N i) u p h.buys.high (powered Y H V G c W) (W.blocks i)
local notation "X" i:max x:max=> salute Y H G s (l0 i) p x (P i)
-- norm approximation to ANY purchased operational budget Follows f in a POSITIVE width with finite margin. Use covariance at crew, no extras.
include σ
lemma clamped (v:InTest K true S false x.val)(k:Gt)(e:(p j:ℝ)+R≤(k:ℝ))(i:ℕ) : ∃ A: (Ω₀).Op, Follows Y H V G j (c j) χ (X i x) k A∧ ‖A+ (Rₚ x)*(L).E (Real.toNNReal ((k:ℝ)-(u:ℝ)))‖≤ ‖Rₚ x‖* amber (N i) := by
 let T:= p-eject j u; have he: 0≤ ((θ i):ℝ):=(aTime (l0 i) w (N i)).ge.trans' (by positivity)
 have q:(p j:ℝ)+ ((θ i):ℝ) ≤ k := le_trans (add_le_add (le_refl _) ((aTime (l0 i) w (N i)).le.trans (W.aperture i))) e
 have Gm:=ChargeFrame.fills Y H V G j c χ W z i
 refine ⟨_, boxAfter Y H V G j (c j) χ p k h.buys.high.le he (right_gap j s u S r δ p h σ) q (onset Y H V G j (c j) χ S s u r h.buys v) Gm.funded, ?_⟩
 exact earnInterest Y H V G j (c j) χ u (θ i) k _ _ p (right_gap j s u S r δ p h σ|>.le) he q _ (by rw [aTime,Real.toNNReal_coe]; exact Gm.detail)
omit σ
lemma home_fields (k:Domain Y H G false (flank j 0))(t:k.val=ticket Y H G s x)(v:InTest K true S false x.val): Tendsto (fun i=> (Gk i) x (P i)) atTop (𝓝 (-(Os k))) := by
 have ht:= (maintains Y H V G j c χ W z (fun _=>p) (fun _=>0) Θ).1
 let A:=Rₚ x; let E':=Pr (p-eject j u);
 have hy:= A.continuous.continuousAt.tendsto.comp (E'.continuous.continuousAt.tendsto.comp ht)
 rw [answer_oper Y H V G j (c j) χ (onset Y H V G j (c j) χ S s u r h.buys v) t]
 have he:A (E' (-Θ))= -(A Θ):=by rw [map_neg,staysVacuum,map_neg]
 rw [he] at hy; exact hy
include χ
lemma right_doom (i:ℕ) : P i∈ insideAt Λ l K true (alcove (hAll Λ (l0 i) w (N i))) (l0 i) := (ChargeFrame.fills Y H V G j c χ W z i).age
include σ in
lemma halo_region {q': Bool} (h' : InTest (tent Y H) true S false x.val)(q:q'=true → CovCover K x.val)(i:ℕ) :
   X i x∈Domain Y H G q' (bufferedHull Λ l s S ∪ slides (coordinates Λ p) (alcove R)):=by
 refine domain_mono Y H G (Set.union_subset_union (Set.Subset.refl _) (Set.image_mono (alcove_mono (W.aperture i)))) (coherent_product Y H V G j s (l0 i) w (N i) u S r δ p h σ h' q ?_); cases q'; exact insideAt_loose _ (right_doom Y H V G j c χ s w u S r δ p W z h i); exact right_doom Y H V G j c χ s w u S r δ p W z h i
-- includes PRESERVATIVE analytic restoration: role f may be anything Intro.B.No need contour.Op.
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.clamped
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.home_fields
