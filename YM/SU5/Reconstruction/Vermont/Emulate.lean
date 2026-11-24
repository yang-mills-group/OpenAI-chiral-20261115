import YM.SU5.Reconstruction.Crease.Rounds
import YM.SU5.Reconstruction.Vermont.Prom
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
variable {x: Sky (tent Y H)} (d v0 : marks (timeMesh Λ))
variable (A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (A':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (s t:marks (timeMesh Λ)) (v u:Axis→marks (timeMesh Λ))
  (f0: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x s A)
  (f1: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-d)) x) v0 A')

local notation "Φ₀" => far Y H V G j (C j) (w j) z d false
include F f0 f1 b
lemma see_edges (L:(G₀ j).Op)(U:Sight Y H V G C a χ j u v L) (g:d+v0 < u z) (r:s<t) (h:0≤ (s:ℝ))(p:G₀ j)(hp:p∈ Φ₀): ∃ c>0, ∃ f,Lens.Plan (S₀ j) ((Π₀ j) A) L (Real.toNNReal (t:ℝ)) (Real.toNNReal (s:ℝ)) c p (Ω₀ j) f:= by
 obtain ⟨u₁,kk,y,T₁,hT,k0,a0⟩:=U; obtain ⟨W,D₁⟩:= a0 z b.symm
 obtain ⟨p,rfl⟩:= LinearMap.mem_range.mp hp; let p':D' j := ⟨p.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left p.property)⟩
 let R:(D' j):= ⟨1,domain_one ..⟩
 have H₁ :(Vo j) R=(Ω₀ j):= (comesHome Y H V G C a χ j)
 change ∃ c>0, ∃ f,Lens.Plan _ _ _ _ _ c ((Vo j) p') _ f
 rw [← H₁]; let u₀:=u z; let v₁:= v z; let δ':=u₀-(d+v0)
 obtain ⟨l0,ϕL⟩:= leftGate Y H V G j z b p' d t (domain_loose Y H G _ (domain_mono Y H G inter_subset_right p.property))
 obtain ⟨w0,ϕW⟩:= rightGate Y H V G j z b R (u₀+ v₁+δ') t (domain_one ..)
 let ρ:= Real.toNNReal (δ':ℝ); have hρ: 0<(δ':ℝ):= (show (0:Gt)< δ' from sub_pos.mpr g); have Hρ:0<ρ:= Real.toNNReal_pos.mpr hρ
 let ω:=transversal z j b; let e:=le_of_eq (transversal_norm z b); let cC':= F.forward z
 let F'(n:ℕ):=screen (S₀ z) cC' ω e ρ Hρ ((Π₀ z) A') ((Π₀ z) (W n)) (Fz l0) (Fz w0)
 have eT : osValue Y H V G z (C z) (w z)= osValue Y H V G j (C j) (w j):= (by rw [os_across Y H V G,os_across Y H V G])
 let Fx (n:ℕ):= cross_chart Y H V G j (C j) (w j) z (C z) (w z) b v0 v₁ p' R d u₀ t (F.present z) eT cC' g f1 (D₁.beyond n) l0 w0 ϕL ϕW
 obtain ⟨ζ,bζ⟩:= D₁.bounded
 let h0:0<(t:ℝ):= lt_of_le_of_lt h r
 refine ⟨(ρ:ℝ), (show 0<(ρ:ℝ) from Hρ), promotion (f:=F') (S₀ j) _ _ _ _ (ρ:ℝ) _ _ (fun i=>slit_opens (S₀ z) cC' _ e ρ Hρ _ _ _ _) Hρ ⟨_,fun n ζ' h=> anchored_cost (S₀ z) cC' _ e ρ Hρ _ _ _ _ (le_refl _) (bζ n) h⟩ Gt (daylight (timeMesh Λ)) hT.short hT.propitious ?_ ?_⟩ -- `_` hol
 · -- tactic anticipate pending Hol inserted synth_hole? used _ not ?_, fix
   intro k p₁ hp; let k₁:Gt:= ⟨k,p₁⟩; rw [Real.coe_toNNReal (t:ℝ) h0.le, Real.coe_toNNReal (s:ℝ) h] at hp; have hv: ∀ᶠ i in atTop,k+(kk i:ℝ) < (t:ℝ):= (tendsto_const_nhds (x:=k) |>.add hT.short).eventually (gt_mem_nhds (by simpa using hp.2)); filter_upwards [hv] with i e'; have he := opens_right Y H V G j (C j) (w j) p' R (F.present j) f0 (hT.stays i) t k₁ h0.le (show (s:ℝ)≤ k from hp.1.le) (show k+(kk i:ℝ)≤ (t:ℝ) from e'.le)
   rw [Real.coe_toNNReal (s:ℝ) h]; exact he.choose_spec.symm.trans ((Fx i k₁).choose_spec)
 intro k p₁ hp; let k₁:Gt:=⟨k,p₁⟩; rw [Real.coe_toNNReal (t:ℝ) h0.le] at hp; have hv: ∀ᶠ i in atTop,k+(kk i:ℝ) < 0:= (tendsto_const_nhds (x:=k) |>.add hT.short).eventually (gt_mem_nhds (by simpa using hp.2)); filter_upwards [hv] with i e'; have he:= opens_left Y H V G j (C j) (w j) p' R (F.present j) f0 (hT.stays i) t k₁ h0.le (show k+(kk i:ℝ)≤ (0:ℝ) from e'.le) (show -(t:ℝ)≤ k from hp.1.le) r.le
 rw [Real.coe_toNNReal (s:ℝ) h]; exact he.choose_spec.symm.trans ((Fx i k₁).choose_spec)
omit F f0 f1 b
lemma seat_cools (r:ℝ≥0) : (S₀ j).E r (Ω₀ j)=(Ω₀ j):= (OS.Semigroup.fixed ..).1 (_root_.YM.Boundary.offiero (S₀ j) (Ω₀ j) (fun _=> compass_origin ..)) r
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
