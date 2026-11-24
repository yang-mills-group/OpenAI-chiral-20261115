import YM.SU5.Reconstruction.Sleet.Mitt
import YM.SU5.Reconstruction.Sleet.Hoist
/-! # Sleet proof budget on the pulse -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5200
set_option synthInstance.maxSize 33000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers LightBudget Storm
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
local notation "W" => placement Λ
local notation "L" j:max=> lowland j 0
local notation "N" j:max=> flank j 0
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier Fock Lat Lifted Peaks Spire Tenant Vale
  SlabMark MeshClock Tapestry.Exhibition Tapestry.Altitude Metric
attribute [local instance] opCStarAlgebra
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker

/-- Issued on the actual selected character. No unspoken interpolation assumptions.
Sleet Real Appointment criterion is on REAL consultations. Sufficient for CP5 genuine Boost & Four Frame translation/positive light.If concerns about funding all real axis rotations or floor locality/Weyl physics, those have more prices as in CP1..15.
Read other statements such as separation_price, ConePrice.Storm.Snowball declarations, fronts etc for the full semantics in CP this thesis. -/
structure Rainbow:Prop where
  stencils (r:ℝ)(p:0≤r): Consult Y H V G C a χ r → BoostBacking Y H V G C a χ
  wings (j b:Axis)(v:b≠j) (x:Sky (tent Y H))(t:x∈Domain Y H G true (flank j 0)):
    let w:= displacement Y H V G.history G.clipped a false (C a) χ j (C j)
    ∃ D' Q:ℝ,Blizzard (ride Y H V G.history G.clipped j false (C j) w) ((mainsea Y H V G.history G.clipped j false (C j) w).track.crew ⟨b,v⟩) (physicalKet Y H V G j (C j) w ⟨x,t⟩) D' Q
  credits(j b:Axis)(p:b≠j)(ℓ:ℝ)(w:0≤ℓ)(x:Sky (tent Y H))(t:x∈Domain Y H G true (flank j ℓ))(u:marks (timeMesh Λ))(e:0≤(u:ℝ))(t₁ t₂:Shard (marks (timeMesh Λ))) :
    let v:= u+t₁.val+t₂.val
    let A:= lowland j (-ℓ)
    let B:= flank j (ℓ+(v:ℝ))
    let y:= move (tent Y H) (terrainK j b v (t₁.val-t₂.val)) x
    ((flipMark j (tent Y H) x∈ Domain Y H G true A)∧ y∈Domain Y H G true B) ∧ Disjoint A B ∧ (∀x∈A,∀ z∈B,(v:ℝ)≤ z j-x j) ∧ 0<(v:ℝ)∧ inspect Y H j b x u t₁ t₂∈ Domain Y H G true (A∪B)
  grantArray (j b:Axis)(p:b≠j)(x y:Sky (tent Y H))(v:Thermal Y H G j x y)(u: Thermal Y H G b x y):
      let B:= max (maxFare Y H V G C a χ j v) (maxFare Y H V G C a χ b u)
      ∃ (F:ℝ→ℂ→ℂ)(G':ℂ→ℝ→ℂ),Squall B F G' ∧ ∀ s t:Shard (marks (timeMesh Λ)), let z:= whiff Y H V G C a χ (ridgeLine Y H j b x y s.val t.val); F (thermal s) (thermal t)= z ∧ G' (thermal s) (thermal t)=z
  boarding (j b:Axis)(h:b≠j)(U R:Set RSpace)(a':IsCompact U)(b':IsCompact R)(δ:ℝ)(v:allLift U R δ) (x y:Sky (tent Y H)) (h1:x∈ Domain Y H G false U)(h2:y∈ Domain Y H G false R) (s:Shard (marks (timeMesh Λ)))(A:thermal s<δ):∃ F:ℂ→ℂ, Soaring Y H V G C a χ j b x y s F
  agency (j b:Axis)(h:b≠j)(U R:Set RSpace)(δ:ℝ)(v:allLift U R δ)(c:Bool)(x y:Sky (tent Y H))(h1:x∈ Domain Y H G c U)(h2:y∈ Domain Y H G c R)(s:Shard (marks (timeMesh Λ)))(A:thermal s<δ)(z:marks (timeMesh Λ))(t:|(z:ℝ)|≤ thermal s):
      let R':= slides (coordinates Λ (terrainK j b z (-z))) R
      allLift U R' (δ-thermal s) ∧ ridgeLine Y H j b x y z (-z)∈Domain Y H G c (U∪R')
  route (i j b:Axis)(p:b≠j)(S:Finset Cover)(o B J:Cover)(t d u:ℕ)(δ:ℝ)(z:SU.Slot)
    (f:Marks (tent Y H) true)
    (g:LinkCheck Y H V G i (C i) (displacement Y H V G.history G.clipped a false (C a) χ i (C i)) t B J S z o u d f δ)
    (s: Shard (marks (timeMesh Λ)))(q:thermal s<δ):TraceSignal Y H V G C a χ i j b z t u d S o B J s f

set_option maxHeartbeats 500000 in
lemma fully_shored: Rainbow Y H V G C a χ where
 stencils r p q:= Consult.funded Y H V G C a χ p q
 wings j b v x t:= available_wings Y H V G C a χ j b v t
 credits j b p ℓ w x t u e t₁ t₂:= separation_price Y H V G j b p w t u t₁ t₂ e
 grantArray j b p x y v u:= by intro B; apply weather_tag Y H V G C a χ j b p v u B (le_max_left ..) (le_max_right ..)
 boarding j b h _ _ u v δ w x y h1 h2 s q:= full_power Y H V G C a χ j b h w u v s q h1 h2
 agency j b h _ _ δ k_pp c x y h1 h2 s A z t:= ⟨lessSnow j b h k_pp s A z t,fronts Y H V G j b h k_pp s A z t h1 h2⟩
 route i j b p _ o B J t d u δ z f g s q:= ReceiptLift Y H V G C a χ i j b p t q B J g
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
