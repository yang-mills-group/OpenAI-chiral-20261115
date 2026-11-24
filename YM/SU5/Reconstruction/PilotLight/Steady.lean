import YM.SU5.Reconstruction.PilotLight.LanternRoom
/-! Mint Station. Actually funded at this field. No spectral price. Covers all limits of these exact purchases. -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5700
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted
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
local notation "J₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "T₀"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Lp'"=> Follows Y H V G j (c j) χ
variable {A B : (indoor Y H V G.history G.clipped j false (c j) χ).Op}
variable (s w:ℕ)
variable {x y:Dome (tent Y H)}
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
local notation "bP" n:max=> bAll Λ s w n
local notation "K₁"=> ticket Y H G s
variable (z:SU.Slot){r:ℕ}{S:Finset Cover}{a:Fin r → Cover}
open SlabMark.Bankroll Tapestry Tapestry.Altitude PhaseChoice
open _root_.YM.Analysis
variable (Kσ₀ t:ℝ)
def amber (k:ℕ):ℝ:= (1/64:ℝ)^k
lemma amber_nonneg (k:ℕ): 0≤ amber k:=by unfold amber; positivity
lemma amber_limit : Tendsto amber atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma amber_control (k:ℕ)(e:0<k): amber k ≤1/64:=by
 cases k with
 | zero=> omega
 | succ k=>
   unfold amber
   rw [pow_succ']; apply mul_le_of_le_one_right (by norm_num); exact pow_le_one₀ (by norm_num) (by norm_num)
structure Traveler (S:Finset Cover){r:ℕ}(a:Fin r → Cover)(x:Dome (tent Y H)) : Prop where
  worth : x∈ insideAt Λ l (tent Y H) true (alcove (hOne Λ s w)) s
  carnet (j:Axis) : Between (tent Y H) j 0 (ruler Λ.block*w) S
  hearth (j:Axis): StampFoot Y H V s G j (c j) w S x.val (1/64)
  basis : x.val∈ Filigree (tent Y H) (Window.family z) a S
  flat : Silence x.val
  real_ : Injective a
variable {w}
lemma onward (p:Traveler Y H V G c s w z S a x) : 0<w:= ((p.hearth 0).2.2).choose
-- Mask ticket. includes coherence, level, f and appointment. q≥1 even if ignored Slot occupant.Token
variable (q d u:ℕ)
def tileA (q d u:ℕ) := booty (grain (payout d q u)) d q
def district (q d u:ℕ) := grindscape (tileA q d u) (Sen (grain (payout d q u)) (payout d q u))
local notation "Ta"=> tileA q d u
local notation "Sₐ"=> district q d u
variable {J Q:ℝ} (P:Papal.Cellarer Y H J Q q d u w) {v v':SU.Slot→ observable (tent Y H) true}
variable {i' :ℕ} {κ :ℝ}
-- warmth of all characters. Captures SAME prescription.
include P in
lemma felt_one (h:Deliver Y H V s G w c d q u v v' κ i')(ht':Silence (v' z).val): Traveler Y H V G c s w z Sₐ (tileA q d u) (PhaseChoice.resolutionProbe Y H (v' z)):= by
 obtain ⟨u',Yt⟩:=h.after z
 have ht:∀ j, Between (tent Y H) j 0 (ruler Λ.block*w) Sₐ:=fun i=>(Yt i).2.1
 let B:= PhaseChoice.resolutionProbe Y H (v' z)
 have hb:InTest K true (district q d u) false B.val:= (Yt 0).1; have hv:CovCover K B.val:=(v' z).property.2 rfl
 have he:Injective (booty (grain (payout d q u)) d q):= P.cents _
 refine ⟨roomKit Y H s w ht hb (fun _=>hv), ht, Yt, u', ht', he⟩

section beam
variable (p:Traveler Y H V G c s w z S a x) (n:ℕ)
local notation "B₁"=> bAll Λ s w n
local notation "D₀"=> alcove (hAll Λ s w n)
local notation "Xk"=>lantern (tent Y H) x w n
local notation "Pₚ"=> valuePort Y H V G j c χ s w n
structure Mantle (a:Fin r → Cover)(n:ℕ)(p:0<w)(d:0<n)(x:Dome (tent Y H)) :Prop where
  age : x∈insideAt Λ l (tent Y H) true (alcove (hAll Λ s w n)) s
  flow : x∈fieldBook z S a (tent Y H) w n
  charge : Silence x.val
  funded : Follows Y H V G j (c j) χ (K₁ x) (bAll Λ s w n) (valuePort Y H V G j c χ s w n p d x)
  detail : ‖valuePort Y H V G j c χ s w n p d x+(L).E (hAll Λ s w n)‖ ≤ amber n
  inquiry : pinhole (Dome K) s x∈ PhaseChoice.circum Λ l K false (alcove (hAll Λ s w n)) ((Set.univ:Set ℕ)∩ Set.Iic s)
-- S is implicit? structure fields auto variable.S.tune.
variable (e:0<n)
include p
lemma collects (t:0<w): Mantle Y H V G j c χ s (w:=w) z (S:=S) a n t e Xk := by
 have ht:= permit_lantern Y H s w t p.worth n; let A:= Pₚ t e Xk
 have he: Follows Y H V G j (c j) χ (K₁ Xk) B₁ A:= portent Y H V G j c χ s w n t e (insideAt_loose s ht)
 refine ⟨ht, allIlluminated w z S a n p.basis, luminous_silence w p.flat n,he, ?_, ?_⟩
 · obtain ⟨G',Ha,u,Gq⟩:=operator_relation (x:=asLoose K x) Y H V s G j (c j) w S χ x (p.hearth j) rfl
   obtain ⟨B',q,r⟩:=stack_precision Y H V G j c χ s w p.worth (show Follows _ _ _ _ _ _ _ _ (bOne Λ s w) G' from Ha) _ u.le n t
   change ‖A+_‖ ≤ _; rw [unique_op Y H V G j (c j) χ _ he q]; exact r
 obtain ⟨S,u,v,p⟩:=receiptStencil Y H s w t p.carnet (FilTest p.basis) n z a; exact narrow_price Y H s v u ht
end beam
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.collects
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.felt_one
