import NeedleW.Coh
import NeedleW.Touch
import Aloft.Resolve
import NeedleW.Line
import Aloft.Spoon
import Aloft.BudgetA
import Aloft.Ride
import Aloft.Conceit
import Aloft.ZL
import Aloft.Canon
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 820000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) 
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
namespace Anchovy
open _root_.NeedleW
variable (J:P.Ellis 3 x)
variable (v0:Enviro P x)(q:Fever P F C D x)(G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))
local notation "τ" j:max=> (tidal P F j).toNNReal
local notation "z" j:max=>A₀ (G j)
private lemma forward_tail {K:Hilbert}(x:ℕ→K)(k:ℕ)(r:ℝ)(t:∀i:ℕ,∃ a, i ≤ a ∧ ‖x a‖ < r):∃ᶠ i:ℕ in atTop,‖x (k+i)‖ ≤ r:=by
    rw [frequently_atTop]; intro i
    obtain ⟨a,u,g⟩:= t (k+i)
    obtain ⟨j,rfl⟩:= Nat.exists_eq_add_of_le u
    exact ⟨i+j,Nat.le_add_right .., (by rw [←Nat.add_assoc]; exact g.le)⟩
include g v0 J v p q
lemma tendency: Tendsto (fun i=>‖z i‖) atTop atTop:=by
 simp_rw [Filter.tendsto_atTop_atTop] -- unknown form use Filter.tendsto_atTop.2
 intro c
 by_contra he
 push Not at he -- tune
 let h(n):=F+n
 let V(n):=z (h n); let f(n): ℝ≥0:= τ (h n)
 have hτ(j:ℕ): ((τ j):ℝ)=tidal P F j:=Real.coe_toNNReal _ (tide_price P F j).le
 have hV := fun i j (h0:f i ≤ f j)=> parcelH P F C D x G g (Nat.le_add_right F _) (Nat.le_add_right F _) h0
 have HE(n):0<f n:= Real.toNNReal_pos.mpr (tide_price P F _)
 have HF:Tendsto f atTop (𝓝 0):= by
    apply NNReal.tendsto_coe.mp; change Tendsto (fun i=>_) atTop (𝓝 (0:ℝ))
    change Tendsto ((fun x:ℝ≥0=>(x:ℝ)) ∘ f) atTop _; change Tendsto (fun n=>((f n):ℝ)) atTop (𝓝 0); simp_rw [f,hτ]; exact (recessVanish P F).comp ((tendsto_add_atTop_nat F).congr (fun i=>Nat.add_comm i F))
 have Hc:∃ᶠ i:ℕ in atTop,‖V i‖ ≤ c:=forward_tail (K:=H) (fun i:ℕ=>z i) F c he
 obtain ⟨y,k⟩:= NeedleW.forwardLimit (Ψ) f V hV HE HF c Hc
 have hz:F ≤ h 0:=Nat.le_add_right ..; have hn:= unlocked P F C D x G g q (j:=h 0) hz
 have hp:∀ᶠ i:ℕ in atTop,‖V 0‖ ≤ ‖V i‖:= (HF.eventually (ge_mem_nhds (HE 0))).mono fun i e=> NeedleW.norm_post (Ψ) f V hV e
 have hy:y≠0:= norm_pos_iff.mp ((norm_pos_iff.mpr hn).trans_le (ge_of_tendsto k.norm hp))
 have hm:Tendsto (fun i=>z i) atTop (𝓝 y):= (tendsto_add_atTop_iff_nat F).mp ((show Tendsto (fun n:ℕ=> z (h n)) atTop (𝓝 y) from k).congr (fun i=> congrArg (fun j:ℕ=>z j) (Nat.add_comm F i))) -- check
 exact avoid P M α F C D x p v J G g v0 (show Tendsto (fun i:ℕ=>i) atTop atTop from tendsto_id) (hm.comp (_root_.YM.Preen.goes_town)) hy
#check tendsto_add_atTop_iff_nat
#check tendsto_atTop_atTop
#check frequently_atTop
#check @avoid
#print axioms tendency
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
