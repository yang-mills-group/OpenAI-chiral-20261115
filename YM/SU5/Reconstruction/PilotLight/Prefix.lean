import YM.SU5.Reconstruction.PilotLight.Prior
import YM.SU5.Reconstruction.PilotLight.Witness
import YM.SU5.Reconstruction.PilotLight.Conserve
/-! The other spectator always online. For illumination, interest also genuine.
Consider these as physical *position* claims, no time-step costs across different Spin frames. -/
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
/- explicit distances seed permit including UTC Eu thresholds. Core Region.S.Turn. -/
structure ReadySet :Prop where
    buys : Passport (Λ:=Λ) (l:=l) j S s u r
    schedule : ∀ i:Axis,∀ x∈bufferedHull Λ l s S,x i+δ ≤ (p i:ℝ)
    timing : (u:ℝ)+δ ≤ p j
    begins : r ≤ (p j:ℝ)
lemma Set_behind (h:0<δ) : ∃ p:placement Λ,∀ x:Passport (Λ:=Λ) (l:=l) j S s u r, ReadySet (l:=l) j s u S r δ p := by
 obtain ⟨p,e⟩ := signed_extent (Λ:=Λ) (max r u) δ _ (compact_hull Λ l s S); exact ⟨p,fun x=> ⟨x,fun i=>(e i).2,(add_le_add_left (le_max_right ..) _).trans (e j).1,by linarith only [h,(e j).1,le_max_left r (u:ℝ)]⟩⟩
variable (a:ReadySet (l:=l) j s u S r δ p)(σ:0<δ)
include a
lemma spends_plan : ∀ i:Axis,∀ x∈ bufferedHull Λ l s S,∀ y∈ slides (coordinates Λ p) (alcove (hAll Λ t w n)), x i+δ ≤ y i:=by
 rintro i x q _ ⟨v,p',rfl⟩; exact (a.schedule i x q).trans (le_add_of_nonneg_left (p' i).1)
lemma earns_plan : ∀ d:ℝ, Σ∪slides (coordinates Λ p) (alcove d) ⊆ flank j r := by
 rintro d x (q|⟨u,t,rfl⟩); exact (a.buys.cost q).1; exact a.begins.trans (le_add_of_nonneg_left (t j).1)
variable {x y:Dome (tent Y H)}
def salute (x y:Dome (tent Y H)): Sky (tent Y H):= ticket Y H G s x * move K p (ticket Y H G t y)
local notation "Z"=> salute Y H G s t p
include a σ V
omit V in
lemma right_gap : (u:ℝ) < (p j:ℝ):= (lt_add_of_pos_right _ σ).trans_le a.timing
omit V in
lemma ditto (d:ℝ): Disjoint Σ (slides (coordinates Λ p) (alcove d)) := by
 apply Set.disjoint_left.mpr; rintro _ h ⟨x,e,rfl⟩; have hK : (x j+(p j:ℝ))+δ ≤ (p j:ℝ):= a.schedule j _ h; linarith [(e j).1]
lemma coherent_product {q₀:Bool} (v:InTest K true S false x.val)(u': q₀=true → CovCover (tent Y H) x.val)(hy:y∈insideAt Λ l (tent Y H) q₀ B₁ t) : Z x y∈ D q₀ (Σ∪O):=
 domain_mult Y H G (ticket_mem Y H G ((mem_insideAt ..).2 ⟨⟨S,v,hull_support Λ l s S⟩,u'⟩)) (moving Y H V G p _ (ticket_mem Y H G hy)) (ditto j s u S r δ p a σ _)
lemma highEnoughₚ {q₀:Bool} (v:InTest K true S false x.val)(u': q₀=true → CovCover (tent Y H) x.val)(hy:y∈insideAt Λ l (tent Y H) q₀ B₁ t) : Z x y ∈ D q₀ (flank j r):= domain_mono Y H G (earns_plan j s u S r δ p a _) (coherent_product Y H V G j s t w n u S r δ p a σ v u' hy)
variable (t1:0<w)(t2:0<n)
-- primal ANY q error. Always exact operator/χ relationship.
omit a σ
def witnessedKet (k:0<(u:ℝ))(p1:0<w)(p2:0<n)(x y:Dome (tent Y H)) : indoor Y H V G.history G.clipped j false (c j) χ := startLens Y H V G j (c j) χ s u k x (Pr (p-eject j u) (valuePort Y H V G j c χ t w n p1 p2 y Θ))
local notation "Gb"=> witnessedKet Y H V G j c χ s t w n u p a.buys.high t1 t2
include a σ
lemma resources (v:InTest K true S false x.val)(hy:y∈insideAt Λ l (tent Y H) false (alcove (hAll Λ t w n)) t)
 (d:Domain Y H G false (flank j 0))(p':d.val = Z x y) : OSvector Y H V G j (c j) χ d= Gb x y:=
 sparePrice Y H V G j (c j) χ p ((lt_add_of_pos_right (u:ℝ) σ).trans_le a.timing) (show 0≤(bAll Λ t w n : ℝ) from (by rw [aTime]; positivity)) a.buys.high.le (onset Y H V G j (c j) χ S s u r a.buys v) (portent Y H V G j c χ t w n t1 t2 hy) p' -- hole non calc coercion

-- Tactics may not see left notation; shrink.T.Need use hp casts. Gram pricing structure. This is at *this* chi.
omit a σ
def historyGram (k:0<(u:ℝ))(p1:0<w)(p2:0<n)(x y:Dome (tent Y H)):ℂ:= let X:= witnessedKet Y H V G j c χ s t w n u p k p1 p2 x y; inner ℂ X X
local notation "GN"=> historyGram Y H V G j c χ s t w n u p a.buys.high t1 t2
include a σ
lemma authority (v:InTest K true S false x.val)(hy:y∈insideAt Λ l (tent Y H) false (alcove (hAll Λ t w n)) t) : ∃ h:LightBudget.gram j (tent Y H) (Z x y)∈ D false Set.univ,
   osValue Y H V G j (c j) χ ⟨LightBudget.gram j (tent Y H) (Z x y),h⟩ = GN x y:=by
 let hx:= domain_mono Y H G (TimeMesh.flank_mono j a.buys.base) (highEnoughₚ (q₀:=false) Y H V G j s t w n u S r δ p a σ v nofun hy)
 let d:= (⟨_,hx⟩ :Domain Y H G false (flank j 0)); have h:= (registered_pair Y H V G j (c j) χ d d); refine ⟨paired_forever Y H G j _ _ hx hx, h.symm.trans ?_⟩
 rw [resources Y H V G j c χ s t w n u S r δ p a σ t1 t2 v hy d rfl]; rfl
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.authority
