import CellQ.Linger
import GlazeS.Tremble
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
open Py.Rate.Pitching.Focus
variable (P:Spine) {U:P.Roster}(M:Morn P.par.K)
open Py.Dyad Keeping
local notation "fL"=>P.par.R.L
local notation "Q"=>ThinGauge.boost (Xη fL)
abbrev sparrow (P:Spine) (F:ℕ)(x:P.Spectrum0 3)(i j:ℕ) : P.ColorHil 3 x:= P.viewF 3 x i (certificate P F i j)
variable (F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3){α:ℝ}(t:Jones P M α F C D x) (p:∀ s,F ≤ s→Bills F (s+1) s P.par.R.L (C s) (D s))
include t
lemma goes_by : ∀ᶠ d:ℕ in atTop,let j:=hikeV d; ∀ k:ℕ, let R:= sparrow P F x; let n:=j+k
 ‖((eraK C D fL j n:ℝ):ℂ) • R (n+1) j - R n j‖ ≤ (2/Q)^k*(2^d*(2*ranch P M α j)):=by
 let T:= Q
 have ht:0<T:=boostP _
 filter_upwards [t] with d t j k R n
 have h:=t k true
 rw [billDress _ _ _ _ _ _ _ (fresh P F j)] at h
 unfold tokenA tokenB denom at h
 let B:=2*ranch P M α j; let q:= revenue fL (C n) (D n) n j; let a:=C n n
 have hZ: hGain (C n) (n+1) n=a:=by rw [gain_step _ _ _ (Nat.lt_succ_self _),gain_here,mul_one]
 change ‖((hGain (C n) (n+1) n*(T^(n-j)*q):ℝ):ℂ) • R (n+1) j + ((-(T^(n-j)):ℝ):ℂ) • R n j‖≤ 2^(d+k)*B at h
 rw [hZ,show n-j=k from Nat.add_sub_cancel_left ..] at h; let z:=T^k
 have hz:0<z:=pow_pos ht k
 let V:= ((a*q:ℝ):ℂ) • R (n+1) j-R n j
 change ‖V‖≤ (2/T)^k*(2^d*B)
 rw [div_pow,show (2^k/(T^k))*(2^d*B)=(2^(d+k)*B)/z from (by unfold z; rw [pow_add]; ring),le_div_iff₀ hz,mul_comm ‖V‖,show z= ‖(z:ℂ)‖ from (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]),←norm_smul]
 apply h.trans'; refine le_of_eq (congrArg norm ?_); unfold V; rw [smul_sub,←mul_smul]; rw [show (z:ℂ)*↑(a*q)= ↑(a*(T^k*q)) from (by unfold z; push_cast; ring), sub_eq_add_neg,←neg_smul,←Complex.ofReal_neg]

include p
lemma annihilates {V:Type}[NormedAddCommGroup V][NormedSpace ℂ V] : ∀ᶠ d:ℕ in atTop,let j:= hikeV d; ∀ m:P.ColorHil 3 x→L[ℂ] V, ‖m‖≤1→
 Tendsto (fun i:ℕ=>m (recoup P F C D x i j)) atTop (𝓝 0) →∀ s:ℕ,
 ‖m (sparrow P F x (j+s) j)‖ ≤ 2*((2/Q)^s*(2^d*(2*ranch P M α j))) :=by
 have hG:Tendsto hikeV atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℕ) by decide)).comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℕ) by decide))
 filter_upwards [goes_by P M F C D x t,hG.eventually_ge_atTop F] with d he hj j m hp v s
 let u(i:ℕ):=m (sparrow P F x (j+i) j)
 rw [mul_comm (2:ℝ) ((2/Q)^s*_)]
 apply diminish C D fL p u hj (by have h:= ranch_p P M α j; positivity)
 · have hr:Tendsto (fun i:ℕ=>m (recoup P F C D x (j+i) j)) atTop (𝓝 0):=v.comp ((tendsto_add_atTop_nat j).congr (fun i=>Nat.add_comm i j))
   unfold recoup at hr; simp_rw [map_smul] at hr; exact hr
 intro i _; have ht:= he i
 let a:ℂ:= ((eraK C D fL j (j+i):ℝ):ℂ)
 have hh:= m.le_opNorm (a • sparrow P F x (j+i+1) j - sparrow P F x (j+i) j); rw [map_sub,map_smul] at hh
 unfold u; rw [← Nat.add_assoc j i 1]; exact hh.trans ((mul_le_of_le_one_left (norm_nonneg _) hp).trans ht)

-- sector gap.Price.No assertion boosts.Quink.H.Further condition. elect
#print axioms annihilates
#check @annihilates
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
