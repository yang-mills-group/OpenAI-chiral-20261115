import YM.SU5.Reconstruction.PilotLight.Piece
import YM.SU5.Reconstruction.PilotLight.Loss
import YM.SU5.Reconstruction.Trap.Castle
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
variable {d q vm:ℕ}{l0 N:ℕ→ℕ}{x:ℕ→ SU.Slot → Dome (tent Y H)} {R:ℝ}
variable (W:Trail Y H V G c w q d vm R N l0 x) (z:SU.Slot)
local notation "θ" i:max=> lantern (tent Y H) (x i z) w (N i)
local notation "tq" i:max=> l0 i
local notation "hw" => powered Y H V G c W
noncomputable def launch (l0 N:ℕ→ℕ)(x:ℕ→ SU.Slot → Dome (tent Y H))(n:ℕ)(f:Dome (tent Y H)): Sky (tent Y H):=salute Y H G s (l0 n) p f (lantern (tent Y H) (x n z) w (N n))
-- Query for this net, same normalization etc. ONLY use actual occurrences with BILL: self gram ≥1.
-- License also to require further checks explicitly that comparison genuinely fails for those. Thus
-- already a genuinely surviving NONFACTOR detector investigation each time `_slot(z)`. Import
-- } hLeg.R{ from Sig.Flag.FirstFrame to get every test (incl comparisons) paid in THIS χ.
open Lens Spectral Analysis OS Semigroup ConePrice SelectionAnalysis
local notation "M" y:max=>LightBudget.gram j (tent Y H) y
local notation "K₁"=> D true
local notation "U"=> mainsea Y H V G.history G.clipped j false (c j) χ
variable (ε:ℝ)(hr:0≤r)(D':0<δ)
local notation "Pp"=> powered Y H V G c W
noncomputable def Annual (
  W:Trail Y H V G c w q d vm R N l0 x):Prop:=
 ∀ i:Axis, i≠j→∀ b:marks (timeMesh Λ),0<(b:ℝ)→(b:ℝ)< ε→
   ∀ (s:ℕ)(u: marks (timeMesh Λ))(S:Finset Cover)(p:placement Λ)(a:ReadySet (l:=l) j s u S r δ p)
     (y:Dome (tent Y H)), InTest K true S false y.val → CovCover K y.val → ∃ᶠ n in atTop,
    1 ≤ (historyGram Y H V G j c χ s (l0 n) w (N n) u p a.buys.high (powered Y H V G c W) (W.blocks n) y (lantern (tent Y H) (x n z) w (N n))).re →
    ¬ lostCause Y H V G j c χ s (l0 n) w (N n) u S p (district q d vm) (tileA q d vm) z a.buys.high (powered Y H V G c W) (W.blocks n) →
     let X:= launch Y H G s w p z l0 N x n y; let A:=Picket.byStamp j i b
     let S1:= gram j (tent Y H) (shop j (tent Y H) A X); let S2:= LightBudget.gram j (tent Y H) (LightBudget.floor j (tent Y H) A X)
     ∀ (k1: S1∈Domain Y H G false Set.univ) (k2:S2∈Domain Y H G false Set.univ), (osValue Y H V G j (c j) χ ⟨S1,k1⟩).re ≤ (osValue Y H V G j (c j) χ ⟨S2,k2⟩).re
local notation "Ac"=> Annual Y H V G j c χ w r δ z ε W -- order check
variable {y:Dome (tent Y H)}
variable (a:ReadySet (l:=l) j s u S r δ p)
local notation "L0" i:max=> launch Y H G s w p z l0 N x i y
local notation "fₚ"=>physicalKet Y H V G j (c j) χ
local notation "Ta"=>Passport (Λ:=Λ) (l:=l)
include W D' χ a
lemma governor (v:InTest K true S false y.val)(s₀:CovCover K y.val)(n:ℕ): (L0 n)∈D true (flank j r):=by
 let X:=ChargeFrame.fills Y H V G j c χ W z n
 exact highEnoughₚ Y H V G j s (l0 n) w (N n) u S r δ p a D' v (fun _=>s₀) X.age
omit D'
local notation "Wv" i:max=> witnessedKet Y H V G j c χ s (l0 i) w (N i) u p a.buys.high Pp (W.blocks i) y (θ i)
local notation "Gz" n:max=> historyGram Y H V G j c χ s (l0 n) w (N n) u p a.buys.high Pp (W.blocks n) y (θ n)
include a
lemma norms_read (n:ℕ): (historyGram Y H V G j c χ s (l0 n) w (N n) u p a.buys.high Pp (W.blocks n) y (lantern K (x n z) w (N n))).re= ‖Wv n‖ ^ 2:= inner_self_eq_norm_sq (𝕜:=ℂ) (Wv n)
lemma account_author (v:InTest K true S false y.val)(n:ℕ)(A:D true (flank j 0))(k:A.val = L0 n)(u':0<δ): physicalKet Y H V G j (c j) χ A=Wv n := resources Y H V G j c χ s (l0 n) w (N n) u S r δ p a u' Pp (W.blocks n) v (insideAt_loose _ (ChargeFrame.fills Y H V G j c χ W z n).age) (Submodule.inclusion (domain_loose Y H G _) A) k
lemma fertile (k:D true (flank j 0))(f : k.val=ticket Y H G s y)(p0:1<‖fₚ k‖)(h': InTest K true S false y.val): ∀ᶠ i in atTop,1 < (Gz i).re:=by
 simp_rw [show ∀ i:ℕ,(Gz i).re = ‖Wv i‖^2 from norms_read Y H V G j c χ s w u S r δ p W z a]
 let v:=home_fields Y H V G j c χ s w u S r δ p W z a (Submodule.inclusion (domain_loose Y H G _) k) f h';
 have ht:Tendsto (fun i=> ‖Wv i‖) atTop (𝓝 ‖fₚ k‖):= by have ht:= v.norm; rwa [norm_neg] at ht
 filter_upwards [ht.eventually (lt_mem_nhds p0)] with n hn; exact (show 1< _^2 from by nlinarith only [(show 1< ‖Wv n‖ from hn)])

local notation "poles" x:max d:max => shop j (tent Y H) x d
local notation "bonds" x:max d:max => LightBudget.floor j (tent Y H) x d
variable {k:Axis}(v:k≠j)(b: marks (timeMesh Λ))(p₀:0<(b:ℝ))(f'':(b:ℝ)<ε)
local notation "z'"=> Picket.byStamp j k b
local notation "t₀"=> (face (z') j).toNNReal
local notation "Tₚ"=>transverse_play (U) z'
-- Linearity extension and closure now via True spec Particle.
include D' v p₀ f''
lemma illuminated_price (a': Ac)(hr: InTest K true S false y.val)(q₁:CovCover K y.val)
 (d0:D true (flank j 0))(f : d0.val=ticket Y H G s y)(p1:1<‖fₚ d0‖):
   let v:= physicalKet Y H V G j (c j) χ d0
   ‖((L).E t₀) (Tₚ v) - (L).E t₀ v‖ ≤ ‖v-(L).E t₀ v‖:=by
 intro v'0; let H0:=a.buys.base
 have m₀ : coordinates Λ z'∈ CostDomain j ε:= Picket.starch (U) ⟨k,v⟩ b p₀ f''
 have he:=a' k v b p₀ f'' s u S p a y hr q₁; let a1:= fertile Y H V G j c χ s w u S r δ p W z a d0 f p1 hr
 let y₁(i:ℕ):=Wv i; let u0:= ((L).E t₀).comp Tₚ - ((L).E t₀); let H1:=1- (L).E t₀; let Q:=(fun v:Ω₀=> ‖u0 v‖); let H2:=(fun v:Ω₀=> ‖H1 v‖)
 have P0: ∃ᶠ n in atTop,Q (y₁ n) ≤ H2 (y₁ n) := (he.and_eventually a1).mono (fun i ⟨h,k⟩=> by
    let i0:=governor Y H V G j c χ s w u S r δ p W z D' a hr q₁ i
    -- pressure inequality on EXACT movement with Φ >...
    obtain ⟨e0,e1⟩:=pressure_coverage Y H V G j (z') (L0 i) i0 H0 m₀
    let x'0:=(L0 i); let r0:=domain_loose Y H G Set.univ e0; let r1:= domain_loose Y H G Set.univ e1
    let p1':= glistens Y H V G j c χ s (l0 i) w (N i) u S r δ p Pp (W.blocks i) (district _ _ _) (tileA _ _ _) z a D' hr ((W.posts i).room z) k.le
    let B:=domain_mono Y H G (TimeMesh.flank_mono j H0) i0
    let y':=(⟨x'0,B⟩: D true (flank j 0)); have v1:= (pressure_test Y H V G j (c j) χ (L0 i) z' m₀.1.le B r0 r1).1 (h k.le p1' r0 r1)
    rw [show y₁ i=fₚ y' from (account_author Y H V G j c χ s w u S r δ p W z a hr i y' rfl D').symm]; exact v1)
 have P₂: Tendsto y₁ atTop (𝓝 (-v'0)) := home_fields Y H V G j c χ s w u S r δ p W z a (Submodule.inclusion (domain_loose Y H G _) d0) f hr
 have hm: Q (-v'0) ≤ H2 (-v'0) := (isClosed_le (u0.continuous.norm) (H1.continuous.norm)).mem_of_frequently_of_tendsto P0 P₂
 unfold Q H2 at hm; rw [map_neg,map_neg,norm_neg,norm_neg] at hm; exact hm
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.illuminated_price
