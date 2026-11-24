import YM.SatinExist.Election
import SatinThinJetsAnalytic
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
variable (P:Spine) (j:Axis)
local notation "ϵ" t:max => P.macroStep t

/-- Convert exponential rate on a dyadic into genuine polynomial power near zero
 when the price is antitone. -/
lemma real_timed (φ:ℝ→ℝ) (f:∀ t:ℝ,0< t →∀ s:ℝ,t ≤ s → φ s ≤ φ t) {W z:ℝ}
    (d:0 ≤ W)(hz:1 ≤ z)(h:∀ᶠ k:ℕ in atTop,φ (P.macroStep k) ≤ W*z^k) :
     ∃ K> (0:ℝ), ∃ m:ℕ,∀ᶠ e:ℝ in 𝓝[>] 0, φ e ≤ K/e^m:=by
 let k:ℝ:= P.par.R.L.val; have hu:1<k:=by unfold k; exact_mod_cast (timeMesh P.par).Llarge
 obtain ⟨m,p⟩:= (tendsto_pow_atTop_atTop_of_one_lt hu).eventually (eventually_ge_atTop z)|>.exists; have hp:z≤k^m:=p
 obtain ⟨N,H⟩:= eventually_atTop.mp h
 let t:= P.macroStep 0; have hP:= P.macroStep_pos
 let T:= t*k; have ht:0<T:=mul_pos (hP _) (by linarith)
 let W':=W+1; have hd:0<W':=by unfold W'; linarith
 refine ⟨W' * T^m,mul_pos hd (pow_pos ht _),m,?_⟩
 filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (hP N))] with e f' v
 have hv:e<P.macroStep N:=v; have f':0<e:=f'
 let Q(n:ℕ): Prop:= P.macroStep n≤e
 have hx: ∃ n:ℕ,Q n:= (P.macroStep_zero.eventually (ge_mem_nhds f')).exists
 let n:= Nat.find hx; have he: P.macroStep n ≤ e:= Nat.find_spec hx
 have g(u v:ℕ)(p:u≤v):P.macroStep v≤P.macroStep u:=by
    rw [←P.daysF v u p]; exact le_mul_of_one_le_left (hP _ |>.le) (one_le_pow₀ hu.le)
 have hn:N<n:= by by_contra! p; linarith only [g n N p, hv,he]
 have hc:e<P.macroStep (n-1):= lt_of_not_ge (Nat.find_min hx (show n-1<n from Nat.sub_lt (by omega) (by omega)))
 have u : k^n*e ≤ T:=by
    refine (mul_le_mul_of_nonneg_left hc.le (pow_nonneg (by linarith) _)).trans_eq ?_
    have he:k^(n-1)*P.macroStep (n-1)=t:=by simpa only [Nat.sub_zero] using P.daysF (n-1) 0 (by omega)
    conv_lhs=> lhs; rhs; rw [show n=n-1+1 from by omega]
    rw [pow_succ',mul_assoc,he,mul_comm]
 apply le_trans (b:=W*z^n) ((f (P.macroStep n) (hP _) e he).trans (H n hn.le))
 have hh: z^n*e^m ≤ T^m:=by
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hz) hp n) (pow_nonneg f'.le _)).trans ?_
    rw [←pow_mul,Nat.mul_comm m n,pow_mul,←mul_pow]; exact pow_le_pow_left₀ (by have h:=zero_lt_one.trans hu; positivity) u _
 apply (le_div_iff₀ (pow_pos f' _)).mpr; rw [mul_assoc]; exact mul_le_mul (by unfold W'; linarith) hh (mul_nonneg (pow_nonneg (zero_le_one.trans hz) _) (pow_nonneg f'.le _)) hd.le

open SatinNucleus SatinJets
variable {P}{x:P.Spectrum0 3}{f r:ℕ}
variable {a:ℕ→ (ℕ×ℕ)→ℝ}{v:ℕ→ℕ}{V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}(u:StrictMono v)(p:P.ThermalBid x f r v a) {q:ℕ→ Coalition}(h:Radiates P x (P.cinema x f r v a q u) V)
local notation "k" => P.rewardK f r

variable {j}
include p h in
lemma Radiates.price (j:Axis)(l:List Axis): ∃ K> (0:ℝ), ∃ m:ℕ,∀ᶠ e in 𝓝[>] 0, ‖V j l e‖≤ K/e^m:=by
 obtain ⟨W,w,z,t,g⟩:=p j l
 apply P.real_timed _ _ (mul_nonneg (norm_nonneg (k)) w.le) t
 · let W':= W
   filter_upwards [g] with i p0
   let t:= P.macroStep i; let A(n:ℕ):= P.beamRaw j x (((P.cinema x f r v a q u) n).pivot P l) t
   have he:= h.cash j l t (P.macroStep_pos _)
   let K:= ‖k‖* (W*z^i); rw [mul_assoc]
   apply le_of_tendsto he.norm
   obtain ⟨N,H⟩:= eventually_atTop.mp p0
   have hx:Tendsto (fun i=> P.roomy * P.macroStep (v i)) atTop (𝓝 0):=by simpa only [mul_zero,Function.comp] using (P.macroStep_zero.comp u.tendsto_atTop).const_mul (P.roomy:ℝ)
   filter_upwards [eventually_ge_atTop N,hx.eventually (ge_mem_nhds (P.macroStep_pos i))] with n tU vP
   change ‖A n‖ ≤ K; unfold A cinema; let X:= q n
   rw [P.pleading_p _ _ _ _ _ _ _ u _ _ l vP]
   refine ((norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i:ℕ=>X.w i*K) fun d e=> ?_).trans_eq ?_))
   · let c:=(P.rewardK f r); let g:= a (n+d) (f,r); let B:= P.beamWatch j x f (v (n+d)) l t
     change ‖(↑(X.w d*(c*g)):ℂ) • B‖ ≤ _
     rw [Complex.ofReal_mul,Complex.ofReal_mul,mul_smul,mul_smul,norm_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (X.signed d e),Complex.norm_real] -- norm last g
     apply mul_le_mul_of_nonneg_left _ (X.signed d e)
     exact mul_le_mul_of_nonneg_left (H (n+d) (by omega)) (norm_nonneg _)
   rw [← Finset.sum_mul,X.pledges,one_mul]
 intro t p s q₀; let H:= P.physicalEnergy j (P.advocate 3 x j)
 rw [h.choir j l p q₀]; exact ((H.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (H.shrinks _))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
