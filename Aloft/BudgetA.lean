import Aloft.SailG
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Ridgetop
open _root_.YM.Preen Py.Rate.Pitching.Focus Py.Dyad Keeping
local notation "γ"=> ((pollN P:ℕ):ℝ)
local notation "Ω"=>‖Ridgetop.visible‖
local notation "Z" n:max=> scaleY (hat P.par.R.L P.par.x (stackW n))
local notation "ℵ" n:max=> P.payday (stackW n)
local notation "r" d:max=> ((girder P d):ℝ)
variable (M:Morn P.par.K)(α:ℝ)(x:P.Spectrum0 3)
noncomputable abbrev ingress(d:ℕ):ℝ:=sponsor P d*(r d)^4
lemma thresholdScale : Tendsto (fun d:ℕ=> ‖ingress P d‖ * thresholdU P M α d (stairW d)) atTop (𝓝 0):=by
 have hv:Tendsto (fun d=> (shoreH d)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp shore_up
 have h(k d:ℕ):0≤ thresholdU P M α d k:=by
    have h2:0 ≤ ranch P M α (hikeV d):=by unfold ranch priceQ payday; change 0 ≤ _^2 * _ * Real.exp 1; positivity
    unfold thresholdU; have h1:= boostP P.par.R.L; positivity
 -- positivity second after nested probably no
 refine squeeze_zero' (Eventually.of_forall fun i=> mul_nonneg (norm_nonneg _) (h _ _)) ?_ hv
 filter_upwards [keyV P M α,feeRatio P,aboard P] with d f hp t
 obtain ⟨_,t⟩:=t; unfold Preen.breeze at t; rw [← coin_scale] at t
 let x:= Z d; let k:= ℵ d; let j:=shoreH d; let a:=thresholdU P M α d (stairW d); have hj:0< j:=zero_lt_one.trans_le (shore_paid _)
 have hk:0<k:=hp.1; have hx:0≤x:=zero_le_one.trans (summitT _)
 have he:0 ≤ (r d):=Nat.cast_nonneg _
 change a*_*(shoreH d)^9≤ k at f
 rw [Real.norm_of_nonneg (show 0≤ ingress P d from mul_nonneg (div_nonneg (sq_nonneg _) hk.le) (pow_nonneg he _))]
 change x^2/k*(r d)^4*a ≤ j⁻¹; apply (mul_le_mul_iff_left₀ (mul_pos hk hj)).mp
 have hr : x^2 ≤ j^8:= (pow_le_pow_left₀ hx t 2).trans_eq (by ring)
 have hq:x^2/k*(r d)^4*a*(k*j)=x^2*((r d)^4*a*j):=by field_simp
 rw [hq,show j⁻¹*(k*j)=k from (by field_simp)]; refine (mul_le_mul_of_nonneg_right hr (show 0 ≤ (r d)^4*a*j from (mul_nonneg (mul_nonneg (by positivity) (h _ _)) hj.le))).trans (?_)
 change a*(r d)^4*j^9 ≤ k at f; linarith only [f]
-- choose m high such that 
local notation "λ*"=>γ*4
noncomputable abbrev traceF :ℝ:= Ω/(256*(λ*+2)^8)
lemma trace_pos:0<traceF P:=by
 have hv:0 < Ω:=norm_pos_iff.mpr Ridgetop.visibility
 unfold traceF; positivity
lemma opening :∃ m:ℕ,1 ≤ m ∧ storm*Ω/(γ*4*m)^8 ≤ traceF P/2:= by
 have hx:Tendsto (fun m:ℕ=> ((γ*4:ℝ)*m)^8) atTop atTop:=by
    have he:Tendsto (fun m:ℕ=> (γ*4:ℝ)*m) atTop atTop:=tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos (show (0:ℝ)<γ from by exact_mod_cast (pollN_pos P)) (by norm_num))
    exact tendsto_pow_atTop (by decide :8≠0)|>.comp he
 have ht:Tendsto (fun m:ℕ=> storm*Ω/(γ*4*m)^8) atTop (𝓝 0):=by simpa only [Function.comp_def,← div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp hx).const_mul (storm*Ω)
 exact ((eventually_ge_atTop 1).and (ht.eventually (ge_mem_nhds (show 0<traceF P/2 from half_pos (trace_pos P))))).exists
noncomputable abbrev bose :=(opening P).choose
variable (V:Enviro P x)
include V
lemma sledge(m:ℕ)(u:1 ≤ m) : ∀ᶠ d:ℕ in atTop, ∀w: Cover, Enrolled P d (stairW d) w→ Ω/(256*(γ*4*m+2)^8) ≤ (ingress P d)^2*‖gem P d m x w‖ ∧ (ingress P d)^2*‖gem P d m x w‖≤ storm*Ω/(γ*4*m)^8:=by
 filter_upwards [dollar P m x u V] with d f w p; specialize f w p
 let κ:=γ*4*m; have hk: (1:ℝ) ≤ κ:=by
    have h1:(1:ℝ) ≤ γ:=by exact_mod_cast (pollN_pos P)
    unfold κ; refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 (by norm_num)) ?_; exact_mod_cast u
 have he:0<κ:=zero_lt_one.trans_le hk
 constructor
 · apply (div_le_iff₀ (show 0<256*(κ+2)^8 from (by positivity))).mpr
   have ht:=pow_le_pow_left₀ ((Nat.cast_nonneg _).trans (ledG P m d w p u)) (mandate P m d w p u|>.2) 8; change _ ≤ ((κ+2)*(r d))^8 at ht; unfold ingress
   have hb:=mul_le_mul_of_nonneg_left ht (show 0 ≤ ‖gem P d m x w‖*(sponsor P d)^2 by positivity); change Ω ≤ _* (256*(κ+2)^ (8:ℕ)); -- reorder via ring rather linarith
   let z:=sponsor P d; let E:= ‖gem P d m x w‖; let A:= led P m d w; change Ω/256 ≤ E*z^2*A^8 ∧ _ at f; change Ω≤(z*(r d)^4)^2*E*(256*(κ+2)^8)
   have hw:= f.1.trans (show E*z^2*A^8 ≤ _ from hb); rw [show (z*(r d)^4)^2*E*(256*(κ+2)^8)=256*(E*z^2*((κ+2)*(r d))^8) from by ring]; linarith only [hw]
 apply (le_div_iff₀ (show 0<κ^8 from pow_pos he _)).mpr; unfold ingress
 let z:=sponsor P d; let E:= ‖gem P d m x w‖; let A:= led P m d w; change (z*(r d)^4)^2*E*κ^8 ≤ _; rw [show (z*(r d)^4)^2*E*κ^8=E*z^2*(κ*(r d))^8 from (by ring)]
 exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg he.le (Nat.cast_nonneg _)) (mandate P m d w p u|>.1) 8) (by unfold E; positivity)).trans f.2
#print axioms thresholdScale
#print axioms sledge
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
