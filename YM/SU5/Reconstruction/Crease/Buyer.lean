import YM.SU5.Reconstruction.Cashier.Alerts
import YM.SU5.Reconstruction.Crease.Screen
/-! Everywhere affordability in the Sense of a joint Screen frame label. Keeps all costs even without Rank. -/
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
local notation "ρ'" s:max=> toSkybox Y H G s
variable {Y₀: (indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))).Op}
local notation "Gt"=>marks (timeMesh Λ)
local notation "Φ" i:max=> peninsula Y H V G.history G.clipped i false (c i) (χ₁ i)
-- true coverage in Common RSpace; compact cube shrink on ALL frames without analytic economy.
section ticket
variable {f:observable (tent Y H) true}{s:ℕ}
local notation "T"=>Tapestry.cabin (whenly (timeMesh Λ) s w)
lemma joint_tarps {S₀:Finset Cover} (v:∀ j,StampFoot Y H V s G j (c j) w S₀ f.val (1/64)) :
 (ρ' s) f∈Domain Y H G true (BridgeClub.Tarp j (fun _=>0) (fun _=>(Θ s:ℝ)) (Θ s:ℝ)):=by
 apply ticket_mem; refine (mem_insideAt ..).2 ⟨⟨S₀,(v 0).1,(supported_iff ..).2 ?_⟩,fun _=>f.property.2 rfl⟩
 intro x p; have Ht(i:Axis): x i∈ Set.Icc (0:ℝ) (Θ s:ℝ):= (show x∈Chambers.strip i 0 (Θ s) from (supported_iff ..).1 ((strip_seats Y H i s w).2 (v i).2.1) p)
 exact ⟨Ht j,fun i _=>(by simpa only [zero_add] using Ht i)⟩

end ticket
variable (p:Embers Y H V G a c x j z u w q d Y₀)
include p
private lemma vision_that {X: ℕ→ (R j).Op} {ψ:ℕ→ℕ} (h:Tendsto ψ atTop atTop)(v:Limited atTop X Y₀):
   Limited atTop (fun i=> (χU j) ((X∘ψ) i)) ((χU j) Y₀):= by
 obtain ⟨⟨M,g,k⟩,u⟩:=v; exact projected Y H V G j (c j) (χ₁ j) ⟨⟨M,g,h.eventually k⟩,fun x y=> (u x y).comp h⟩
lemma inSight (h:0<w)(v:Gt)(c':0<(v:ℝ)) : Crease.Sight Y H V G c a x j (fun _=>0) (fun _=>v) ((χU j) Y₀):=by
 obtain ⟨ψ,e,f,g,ζ,B,hF,hP,u',b,w'⟩:= p.price
 let k(i:ℕ):=(ρ' (ψ i)) (g i z); let A(i:ℕ):=notch (timeMesh Λ) (ψ i) w
 have hp(i):((A i):ℝ)=(Θ (ψ i):ℝ):=natural_time ..
 have ht:Tendsto (fun i=>(A i:ℝ)) atTop (𝓝 0):=by simp_rw [hp]; exact NNReal.tendsto_coe.mpr ((skinny (Λ:=Λ) w).comp hF.tendsto_atTop) -- direction?
 obtain ⟨N,u₁⟩:= eventually_atTop.mp (ht.eventually (ge_mem_nhds c')) -- Iic
 let σ(n:ℕ):= n+N; have hσ:Tendsto σ atTop atTop:=(strictMono_id.add_const N).tendsto_atTop
 refine ⟨fun i _=>c',A∘σ,k∘σ,B∘σ,⟨(fun n=> (b (σ n)).1),fun i=>?_,ht.comp hσ,vision_that Y H V G a c x j z p hσ w'⟩,fun n=>?_,fun d _=>?_⟩
 · change 0< (A (σ i):ℝ); rw [hp]; exact when_pos _ _ _ h
 · let l:= ψ (σ n); let U':= (A (σ n):ℝ)
   have hu: (Θ l:ℝ)≤(v:ℝ):= by rw [← hp (σ n)]; exact u₁ _ (Nat.le_add_left ..)
   apply domain_mono Y H G _ (joint_tarps Y H V G c j (((u' (σ n)).after z).2)) -- arg tune
   rintro x ⟨a,b⟩; refine ⟨⟨a.1,(hp (σ n)).symm ▸ a.2⟩,fun i h=> ⟨(b i h).1,(b i h).2.trans (add_le_add_right hu _)⟩ ⟩
 choose D t hz using fun i=> chooseLive Y H V G a c x (d:Axis) z (u' (σ i))
 choose M t' hf using fun i=> padding Y H V G (d:Axis) (c (d:Axis)) (χ₁ (d:Axis)) (show A (σ i) ≤ v from u₁ _ (Nat.le_add_left ..)) (t i)
 exact ⟨M,fun i=> by change Follows Y H V G (d:Axis) (c (d:Axis)) (χ₁ (d:Axis)) (FirstWindows.move (tent Y H) (eject (d:Axis) (-(0:Gt))) _) _ _; rw [neg_zero,eject_zero,move_by_zero]; exact t' i,2,fun i=> (weak_contour Y H V G (d:Axis) (c (d:Axis)) (χ₁ (d:Axis)) _).trans ((hf i).trans (harvest_price _ _ _ _ _ _ _ _ _ (hz i)))⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget.Hearthbank
