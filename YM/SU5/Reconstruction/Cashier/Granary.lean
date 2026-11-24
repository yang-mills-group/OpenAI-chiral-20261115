import YM.SU5.Reconstruction.Cashier.Foyer
/-!
# Localization of Harvest grain-eyepiece operators

Realization weak-limit subsequence of live frames at ALL heights eventually (!!), shrinking
aperture (here meaning temporal stencil footprint via BUDGET, not necessarily the ζ field!). Restricts support in time (REAL intervals)
at origin but at ANY k truly. No assertion that OPERATOR LIMIT is nonscalar.
Rotation & PVM criterion not required to obtain these; commuting benefits priced later.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry ConePrice Germ
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Anvil
open SelectionAnalysis
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open FirstWindows.Chambers
variable (a:Axis)(c:∀ i:Axis,Arena Y H G.history.circuit i 0 false)
variable (x:displayAlgebra Y H V G.history G.clipped a false (c a) →⋆ₐ[ℂ] ℂ)
local notation "χ₁" i:max=> displacement Y H V G.history G.clipped a false (c a) x i (c i)
local notation "R" i:max=> indoor Y H V G.history G.clipped i false (c i) (χ₁ i)
local notation "S" i:max=> fort Y H V G.history G.clipped i false (c i) (χ₁ i)
local notation "χU" i:max=> opCarries Y H V G i (c i) (χ₁ i)
local notation "L" i:max=>ride Y H V G.history G.clipped i false (c i) (χ₁ i)
open CF.Pannier.Chancel Bankroll
variable {u w q d:ℕ} (J J':ℝ)
local notation "o"=>grain (payout d q u)
local notation "Ξ"=> booty (grain (payout d q u)) d q
local notation "Ψ"=>Sen (grain (payout d q u)) (payout d q u)
local notation "Tt"=> grindscape (booty (grain (payout d q u)) d q) Ψ
local notation "Θ" s:max=>whenly (timeMesh Λ) s w
local notation "E'"=> driveAlgebra Y H V G.history G.clipped a false (c a)
variable (j:Axis)(z:SU.Slot)
-- For given ruler $i,s,u$ stage and both W & W' purchases. No rescaling of origin required.
-- Recognition: these tickets + mask are those delivered by Cashiering Kraft actually,
-- and once a proof point selected all are already available there.
-- Use arbitrary simultaneous live sequence as the prescription.
noncomputable def toSkybox (s:ℕ)(f: observable (tent Y H) true):Sky (tent Y H):= ticket Y H G s (PhaseChoice.resolutionProbe Y H f)
local notation "ρ'" s:max=> toSkybox Y H G s
variable {Y₀: (indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))).Op}

/-- A Cashed probe. One limiting operator preceded by its Euclidean cost permits
on ALL frames. Using visible $0^{+}$ slit, widths w of the original authority;
poses for the Masked probes actually in `paints_for` of ALL frames once specializing.`
This name doesn't claim the limiting operator is non-scalar. -/
structure Embers (u w q d:ℕ)(Y₀: (R j).Op) : Prop where
   price : ∃ (ψ e:ℕ→ℕ)(f f':ℕ→ SU.Slot → observable (tent Y H) true)(ζ:ℕ→ℝ)
       (X: ℕ→(indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))).Op),
       StrictMono ψ ∧ (∀ i,0<ζ i) ∧ (∀ i, Deliver Y H V (ψ i) G w c d q u (f i) (f' i) (ζ i) (e i)) ∧
       (∀ n, Follows Y H V G j (c j) (χ₁ j) ((ρ' (ψ n)) (f' n z)) (notch (timeMesh Λ) (ψ n) w) (X n) ∧ ‖X n+(L j).E (whenly (timeMesh Λ) (ψ n) w)‖ <1/64) ∧ Limited atTop X Y₀
-- act at each level c mask; yields near norm price regardless whether heading altar, reflection, projection.
lemma chooseLive {f f': SU.Slot → observable (tent Y H) true} {Z:ℝ} {e s:ℕ} (t:Deliver Y H V s G w c d q u f f' Z e) :
   ∃ B:(R j).Op, Follows Y H V G j (c j) (χ₁ j) ((ρ' s) (f' z)) (notch (timeMesh Λ) s w) B∧ ‖B+(L j).E (Θ s)‖<1/64 :=by
 let y:= (f' z); obtain ⟨B,k0,u,k⟩:= operator_relation Y H V s G j (c j) w Tt (χ₁ j) (x:= bosonLabel K y) (PhaseChoice.resolutionProbe Y H y) ((t.after z).2 j) rfl
 exact ⟨B,k0,u⟩

lemma harvest_price {M:(R j).Op}(k:ℝ≥0)(p:‖M+(L j).E k‖ <1/64):‖M‖ ≤ 2:=by
 have he:‖M‖ ≤ ‖M+(L j).E k‖+‖(L j).E k‖:= by simpa only [add_sub_cancel_right] using norm_sub_le (M+(L j).E k) ((L j).E k)
 linarith only [he,p,(L j).shrinks k]

lemma build (A:∀ᶠ s in atTop, ∀ᶠ e in atTop,∃ ζ>0,∃ f f':SU.Slot → observable (tent Y H) true, Deliver Y H V s G w c d q u f f' ζ e) : ∃ M:(R j).Op, Embers Y H V G a c x j z u w q d M:= by
 obtain ⟨a1,h⟩:= eventually_atTop.mp A
 let θ(n):=n+a1; choose e ζ g₁ f f' hf using fun n=> (h (θ n) (Nat.le_add_left ..)).exists -- choose extracts h and witness
 choose B v ux using fun i=> chooseLive Y H V G a c x j z (hf i)
 have hv(i): ‖B i‖ ≤ 2:= harvest_price Y H V G a c x j _ (ux i)
 letI : TopologicalSpace.SeparableSpace (R j).space:= separable Y H V G j (c j) (χ₁ j)
 obtain ⟨ψ,p,M,b,g⟩:= Limited.extract B (by norm_num : (0:ℝ)≤2) hv
 refine ⟨M,⟨θ∘ψ,e∘ψ,f∘ψ,f'∘ψ,ζ∘ψ,B∘ψ,(strictMono_id.add_const a1 |>.comp p),fun n=>g₁ (ψ n),fun n=>hf (ψ n),fun n=>⟨v (ψ n),ux (ψ n)⟩,g⟩⟩

lemma Embers.coin (p:Embers Y H V G a c x j z u w q d Y₀) : ‖Y₀+1‖ ≤ 1/64 ∧ ‖(χU j) Y₀+1‖ ≤1/64:=by
 obtain ⟨ψ,e,f,g,ζ,B,h,a',v,b,w0⟩:= p.price
 have he:= momentShrink Y H V G j (c j) (χ₁ j) w h.tendsto_atTop (fun n=>(b n).2.le) w0
 exact ⟨he,projected_units Y H V G j (c j) (χ₁ j) he⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank.build
