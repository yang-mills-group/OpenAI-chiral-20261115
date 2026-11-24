import YM.SU5.Reconstruction.Vermont.Emulate
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
/- Gauge reduction unconditionally. Need for when buying proofs.
Support EXACT for proposed price. No claim `F=x` in Domain---only equality registered B. -/
lemma northC (T:Set RSpace)(s: Gt)(p:0<(s:ℝ))(x:Sky (tent Y H))(u : x∈ D T)(e:T⊆ Chambers.strip j 0 (s:ℝ)) (A:(J₀ j).Op) (v:(Q j) x s A): ∃ F∈ Ds T, (Q j) F s A:= by
 obtain ⟨r,⟨f,h,rfl⟩,w₁,v0,t0⟩:=(((domain_eventually Y H G).1 u).and (notch_nat_event s p)).exists
 let j0:= (C j)
 obtain ⟨⟨V₀,t,b⟩,-⟩:= (mem_insideAt ..).1 h
 have he : (s:ℝ)= (whenly (timeMesh Λ) r w₁:ℝ):=by rw [← t0]; exact natural_time ..
 let Hp : f∈ insideAt Λ l K false (Chambers.strip j 0 (whenly (timeMesh Λ) r w₁ : ℝ)) r:= (he ▸ (insideAt_mono e h))
 let Z:= startOp Y H j r w₁ f Hp; let VZ := (Chambers.arrangement Y H V G j (C j) (w j) r w₁ Z v0)
 change (Q j) (ticket Y H G r f) _ _ at VZ -- might need dsimp let; undo
 let p0:Between K j 0 (SlabMark.ruler Λ.block*w₁) V₀:= (strip_seats Y H j r w₁).1 ((supported_iff ..).2 (Subset.trans ((supported_iff ..).1 b) (he ▸ e)))
 obtain ⟨y,r0,q⟩:= nearest_bud Y H V r G.history G.clipped j (C j) Z v0 t p0
 let a₁:= Λ.R.L.val^(r+1-r)*w₁; have hv:0<a₁:= Nat.mul_pos (pow_pos Λ.R.L.property _) v0
 let f':= (base Y H j (r+1) a₁ (composer Y H (r+1) j y))
 have h':f'.val∈ insideAt Λ l K true T (r+1):= (mem_insideAt ..).2 ⟨⟨_,((obs_in ..).1 r0).1,b.step⟩, fun _=> ((obs_in ..).1 r0).2⟩
 have hz:notch (timeMesh Λ) (r+1) (a₁:ℤ)= notch (timeMesh Λ) r (w₁:ℤ):= by rw [show (a₁:ℤ)= castor Tx r (r+1) (w₁:ℤ) from (by unfold a₁ castor; push_cast; rfl),notch_up _ _ _ (by omega)]
 refine ⟨ticket Y H G (r+1) f'.val,ticket_mem Y H G h',?_⟩
 obtain hV:= arrangement Y H V G j (C j) (w j) (r+1) a₁ (composer Y H (r+1) j y) hv
 rw [q,hz,t0] at hV; rw [t0] at VZ; rw [unique_op Y H V G j (C j) (w j) _ v VZ]; exact hV

-- Horizon extended W projection onto CP11 region t=0 at identical spatial corners.
noncomputable def panelFace (U:Set RSpace) : Set E4:= (fun x:RSpace=> WithLp.toLp 2 x-x j • basis j) '' U
omit F b
lemma panel_bound {U:Set RSpace} (c:IsCompact U): ∃ A:ℝ,∀ x∈ panelFace j U, ∀ i≠j,|x j|+ x i≤A:=by
 let f(x:RSpace):= WithLp.toLp 2 x-x j • basis j
 have ht: Continuous (f:RSpace→ E4):= by unfold f; fun_prop
 have hc:= c.image ht; obtain ⟨r,hs⟩:= Metric.isBounded_iff_subset_closedBall (0:E4) |>.mp hc.isBounded
 refine ⟨r,?_⟩; rintro _ ⟨t,e,rfl⟩ i p; have hp:‖f t‖≤r:= by simpa using (show dist (f t) 0 ≤r from hs (mem_image_of_mem _ e))
 change |f t j|+f t i ≤ r; rw [show f t j=0 from (by unfold f; simp), abs_zero,zero_add]; exact ((le_abs_self _).trans_eq (Real.norm_eq_abs (f t i)).symm).trans ((PiLp.norm_apply_le (f t) i).trans hp) -- tune
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
