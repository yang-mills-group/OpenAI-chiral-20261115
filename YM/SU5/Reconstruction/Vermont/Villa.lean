import YM.SU5.Reconstruction.Vermont.Windward
import YM.SU5.Reconstruction.Vermont.Periods
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
local notation "ζ"=> floor Y H V G C a χ j
local notation "S"=> (S₀ j)
local notation "Ω"=> (Ω₀ j)
variable {U W:Set RSpace}
variable (B:SpaceFor Λ U W)
namespace Shutters
local notation "Φ" i:max a:max=>B.registerQ.low i a
local notation "μ" i:max a:max=> B.registerQ.width i a
local notation "σ" a:max=> (Φ false a+μ false a)
local notation "g" a:max=> (Φ true a - σ a)
local notation "T" r:max u:max i:max=> (B.registerQ.start j r i) u
-- prepare real position budgets.Lens.
lemma gap : Φ false j + μ false j < Φ true j:= by
 have he := (B.zero_fits j); change _ ∧ (if true=true then _ else _) ∧ True at he
 obtain ⟨_,hz,_⟩:= he; rw [if_pos rfl] at hz; change 0 < B.registerQ.start j 0 true j - B.registerQ.stop j 0 false j at hz
 simp only [Pi.add_apply,Pi.zero_apply, Pi.single_eq_same,zero_add,Schedule.Fixture.start,Schedule.Fixture.stop] at hz; exact (show (Φ false j:ℝ)+(μ false j:ℝ) < (Φ true j:ℝ) from (sub_pos.mp hz))
lemma shutter_c (x:Bool)(θq:Axis): 0 < (μ x θq:ℝ):= B.registerQ.positive x θq
-- geometry for REAL times sufficiently near 0, van Hove.В.
noncomputable def turf (t:ℝ)(q0:Bool): Set E4:= period j (panelFace j (duet U W q0)) t (B.registerQ.low q0 j) (Real.toNNReal (μ q0 j:ℝ)) -- q0 token conflicts
local notation "τ"=> turf j B
local notation "Ht" i:max=> (Φ i j:ℝ)+(μ i j:ℝ)
include b
lemma on_field (t:ℝ)(i:Bool)(x:E4)(p:x∈ τ t i): ∃ s:RSpace,s∈ duet U W i ∧ ((x z) = s z) ∧ ∃ u:ℝ,u∈Icc (Φ i j : ℝ) (Ht i) ∧ x j=t*u:= by
 obtain ⟨u,k0⟩:=mem_iUnion.mp p; obtain ⟨qh,x⟩:=mem_iUnion.mp k0; rw [Real.coe_toNNReal _ (shutter_c B _ _).le] at qh; obtain ⟨_,⟨y,h,rfl⟩,rfl⟩:= x
 refine ⟨y,h,?_,u,qh,?_⟩; all_goals simp [b.symm]
lemma space_budget (t :ℝ)(h:0≤ t)(D0: t*((Ht true)-(Φ false j:ℝ)) < (Φ true z:ℝ) - ((Φ false z:ℝ)+(μ false z:ℝ))) : TicketSeparation j (τ t false) (τ t true) :=by
 intro p L q R; let i:= q-p; unfold Clearance
 obtain ⟨x,hx,x₁,u,u0,h₁⟩:=on_field j z b B t false p L; obtain ⟨y,hy,y₁,v,v0,h₂⟩:=on_field j z b B t true q R
 have z0:z≠ j:=b.symm
 have w1:= B.printed z false hx; have w2:=B.printed z true hy
 have hr : (0:ℝ)≤ t*(v-u):= mul_nonneg h (sub_nonneg.mpr (u0.2.trans ( (show (Φ false j:ℝ)+(μ false j:ℝ)≤ (Φ true j:ℝ) from (gap j B).le).trans v0.1)))
 have e : t*(v-u)≤ t*((Ht true)-(Φ false j:ℝ)):= mul_le_mul_of_nonneg_left (sub_le_sub v0.2 u0.1) h
 have he:i j=t*(v-u):=by change q j - p j=_; rw [h₁,h₂,mul_sub]; -- tune
 have hp : i j < i z:= lt_of_le_of_lt (he ▸ e) (by unfold i; rw [PiLp.sub_apply]; linarith [w2.1,w1.2])
 exact (pow_lt_pow_left₀ hp (he ▸ hr) (by decide)).trans_le (Finset.single_le_sum (f:=fun k:Axis=> (i k)^2) (fun k _=> sq_nonneg _) (a:=z) (s:=Finset.univ.erase j) (by simp [z0]))
lemma purchase_window : ∃ c>0,∀ t:ℝ,t∈ Icc 0 c → TicketSeparation j (τ t false) (τ t true):= by
 let A:= (Ht true)-(Φ false j:ℝ); let B':= (Φ true z:ℝ)-((Φ false z:ℝ)+(μ false z:ℝ))
 have hp:0<B':= sub_pos.mpr (gap z B); have g0:0<A:=by unfold A; linarith [shutter_c B true j,shutter_c B false j, (show (Φ false j:ℝ)+(μ false j:ℝ) < (Φ true j:ℝ) from (gap j B))]
 refine ⟨B'/(2*A),by positivity, fun t p=> space_budget j z b B t p.1 ?_⟩
 nlinarith [(le_div_iff₀ (show 0<2*A by positivity)).mp p.2] -- might need change
omit b
end Shutters
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
