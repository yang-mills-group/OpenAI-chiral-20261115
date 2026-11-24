import YM.SU5.Reconstruction.Vermont.Spirebook
import YM.SU5.Reconstruction.GiftWrap.Transistor
import YM.SU5.Reconstruction.GiftWrap.Sales
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
open Quartz Quartz.Ship Boots
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
local notation "ζ"=> floor Y H V G C a χ j
local notation "S"=> (S₀ j)
local notation "Ω"=> (Ω₀ j)
local notation "R"=> panelFace j
local notation "Ξ"=>fun p:marks (timeMesh Λ)=> FirstWindows.move (tent Y H) (eject j p)
local notation "μ"=> osValue Y H V G a (C a) χ
include F b
lemma settled (k: owns_it (floor Y H V G C a χ j univ) (Ω₀ j))(r:Registered Y H V G C a χ j) : Enclosure Y H V G C a χ j:= by
 constructor
 · intro f W q;
   obtain ⟨U,p,u0,h⟩:= (compact_domain Y H G).1 q; obtain ⟨t,t',e,t0⟩:= Schedule.shutters (daylight (timeMesh Λ)) j p; let d:= t'-t; have d0:0 < (d:ℝ):= sub_pos.mpr e
   have H0 : U⊆ Chambers.strip j (t:ℝ) ((t:ℝ)+d):= by
     intro x p; obtain ⟨a1,h⟩:= t0 x p; change (t:ℝ)≤ x j ∧ x j≤_; unfold d; simp only [AddSubgroup.coe_sub]; constructor<;> linarith
   let s:=((Ξ) (-t) f); obtain ⟨e,qh,V0⟩:= slide_pin Y H V G j U t f h d H0; obtain ⟨A,T0⟩:= fits Y H V G j (C j) (w j) d d0 s (domain_mono Y H G V0 e)
   refine ⟨U,t,d,A,p,u0,d0,h,H0,T0,?_, shout Y H V G C a χ j r U p A f d t d0 h H0 T0, fun M wq=> ⟨liftedReads Y H V G C a χ F j z b k U p _ M s _ d0.le T0 wq, fun i e'=> from_price Y H V G C a χ F j U a _ _ M wq e' _ i⟩⟩
   rw [← owns_stamp Y H V G C a χ F j d s A _ T0 e]; exact (moving_value Y H V G a (C a) χ (eject j (-t)) _ _).symm -- generates auto?_ 
 exact fun k0 X t v p b' u A he=>⟨answers Y H V G C a χ j r X t b' p v k0 _ u he, fun M m=> liftedReads Y H V G C a χ F j z b k X p _ M k0 t v.le he m⟩
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
