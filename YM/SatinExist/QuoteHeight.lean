import SatinThinCentury

/-! ## Ticket of a forecast pilot. Use unshifted estimate of ensemble before state selection. -/
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
open Regis.Head.Etch Regis.Circuit
open Push.Local AnalyticBridge.VerifiedReset
local notation "kθ" => hat P.par.R.L P.par.x
variable (f:ℕ)(l:List Axis)
local notation "X" s:max => P.clockPlate s (s+1) (P.rootSpace f s l)
local notation "L" => P.par.R.L
private lemma pilot_cost (d:Axis) : ∀ᶠ s:ℕ in atTop, ((X s) d).natAbs ≤ scout P.par 2 (s+1):=by
 let c:= 2*frameRadius d+2*P.sidesPerTick
 let e:ℝ:= P.par.R.L.val
 have he:0<e:=by unfold e; exact_mod_cast P.par.R.L.property
 let U(x:ℝ):=trailℓ 1 x+c
 have hp: Worth.Pays 0 1 0 (fun x:ℝ=>e*U x):= Pays.scale e (Pays.plus (Pays.whole 0 1 0) (Worth.Pays.merit (constant (c:ℝ)) (by norm_num [Worth.Earlier])))
 filter_upwards [P.pays_root_mile, (turnover P.par).eventually (leap (w:=0) (p:=2) (q:=0) hp (by norm_num [Worth.Earlier])), (Real.tendsto_log_atTop.comp (turnover P.par)).eventually_ge_atTop 1] with s a b h
 let x:= nodeC (P.rootSpace f s l) d; have hv: 0<x:= P.point_bought d s f l; let t:= P.baseK s
 have hk: x.natAbs ≤ t+c:= by have h₁:x≤t+(c:ℤ):=P.node_ceiling d s f l; omega
 have hz: (x.natAbs:ℝ) ≤ (t:ℝ)+c:=by exact_mod_cast hk
 have hs: ↑(((X s) d).natAbs) = e * (x.natAbs:ℝ):=by unfold clockPlate e x; rw [Pi.smul_apply, Nat.add_sub_cancel_left, pow_one,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast,Nat.cast_mul]
 suffices hq: ( ((X s) d).natAbs:ℝ) ≤ (scout P.par 2 (s+1):ℝ) by exact_mod_cast hq
 rw [hs]; apply (mul_le_mul_of_nonneg_left (hz.trans (add_le_add_left a _)) he.le).trans
 apply (le_trans (b:=trailℓ 2 (kθ s)) b); apply (le_trans (b:=trailℓ 2 (kθ (s+1))) _ (Nat.le_ceil _))
 have ht : 0 < log (kθ s):= lt_of_lt_of_le zero_lt_one h
 have hv:= Real.log_le_log ht (Real.log_le_log (P.f_here s) (P.base_height (Nat.le_succ s)))
 have hw:0 ≤ log (log (kθ s)):= Real.log_nonneg h
 unfold trailℓ BProof.coin; simp
 exact pow_le_pow_left₀ hw hv _

variable {C:ℝ}(Q':∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k)
include Q'
private lemma base_pay : ∀ᶠ s:ℕ in atTop,
   ‖P.eReadL (s+1) (P.tariffM witnessZ (s+1) (X s) (opposeQ j (X s)))‖ ≤ 1+pairedN (P:=P.par) witnessZ :=by
 let t(i):= scout P.par 2 i
 let U(s):= twinTrip (X s) (opposeQ j (X s))
 have h:∀ᶠ i:ℕ in atTop,CoversT (U i) (t (i+1)):= by
   filter_upwards [eventually_all.mpr (P.pilot_cost f l)] with i h d v
   cases d
   · let a:=P.clockPlate i (i+1) (P.rootSpace f i l); change (opposeQ j a v).natAbs≤_; have he:(opposeQ j a v).natAbs=(a v).natAbs:=by by_cases p:v=j <;> simp [opposeQ,mirrorΩ,p]
     rw [he]; exact h v
   · exact h v
 let ht:= StrictMono.tendsto_atTop (show StrictMono (fun i:ℕ=>i+1) from fun x y g=> add_lt_add_left g 1)
 filter_upwards [h, ht.eventually ((shrinkT (P:=P.par) (v:=1) zero_lt_one).eventually (ge_mem_nhds (zero_lt_one : (0:ℝ)<1))), ht.eventually (trek (I:=Bool) P.run witnessZ P.large P.law Q' (A:=16) (v:=1) (by norm_num) zero_le_one (P.tollP 2 (by norm_num)))] with s hs t0 hs'
 let T:= P.eReadL (s+1) (P.tariffM witnessZ (s+1) (X s) (opposeQ j (X s)))
 let z:= P.parish witnessZ (U s) (s+1) 16
 obtain ⟨c,x,p,y⟩:= tile_budget _ _ hs
 have hp: ‖T-(z:ℂ)‖ ≤ 1:= by
   refine (hs' (U s) c x (le_trans p ?_) y).trans t0; unfold debt_length numU; unfold t; omega
 refine ((norm_le_norm_sub_add T (z:ℂ)).trans (add_le_add hp ?_)); rw [Complex.norm_real, Real.norm_eq_abs]
 exact lift_priceΩ P.run witnessZ P.large 16 P.law (s+1) (X s) (opposeQ j (X s))

omit Q' in
lemma tiny_purses : ∃ Z> (0:ℝ), ∀ᶠ s:ℕ in atTop,slotFee P.par s ≤ Z ∧ ‖P.tallWorth s‖ ≤ Z:=by
 have h:∀ᶠ s:ℕ in atTop,slotFee P.par (s+1) ≤ slotFee P.par s:=by
    filter_upwards [(turnover P.par).eventually (pal_U L (billX L) P.arc_price.le)] with s p; unfold slotFee; rw [hat_succ]; exact p.2.1
 obtain ⟨N,t⟩:= eventually_atTop.mp (h.and P.reward_positive|>.and P.size_honors)
 refine ⟨_, (t N le_rfl).2.1, ?_⟩
 filter_upwards [eventually_ge_atTop N,P.pays_root_mile] with s b k
 have he : slotFee P.par s ≤ slotFee P.par N := by
   clear k; induction s,b using Nat.le_induction with| base=> exact le_rfl| succ s hs ih=> exact (t s hs).1.1.trans ih
 refine ⟨he,?_⟩; rw [Real.norm_of_nonneg ((t s b).1.2.1).le,P.tariff_law]
 exact (div_le_self ((t s b).2.1.le) (one_le_pow₀ ( (show 1≤(P.baseK s:ℝ) from (by exact_mod_cast P.payment_pos s)).trans k))).trans he

omit Q' in
private lemma piece_fee (s:ℕ) : let y:= P.flume j (P.rootSpace f s l) (s+1) (P.rent_honors j f s l); ‖P.piece j (s+1) y‖^2=‖P.tallWorth (s+1)‖^2 * ‖P.eReadL (s+1) (P.tariffM witnessZ (s+1) (X s) (opposeQ j (X s)))‖:=by
 intro y
 let w := P.piece j (s+1) y
 let k :P.Test:= P.visitOne (s+1) (X s)
 have h: ‖w‖^2=‖inner ℂ w w‖:=by rw [inner_self_eq_norm_sq_to_K,norm_pow]; simp
 rw [h]; unfold w; rw [P.seed_pairing]
 change ‖P.eReadL (s+1) (P.reflectTest j (P.visitOne (s+1) (X s))*(P.visitOne (s+1) (X s)))‖ = _
 rw [P.reflect_visit]; let a:=P.tariffQ witnessZ (s+1) (X s); let z:= P.tallWorth (s+1); let b:=P.tariffQ witnessZ (s+1) (opposeQ j (X s))
 rw [P.tariff_scalar]; change ‖P.eReadL (s+1) (((z:ℂ) • b)*((z:ℂ) • a))‖ = ‖z‖^2*‖P.eReadL (s+1) (b*a)‖
 rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul,norm_smul,norm_smul,Complex.norm_real]; ring

omit Q' in
private lemma staff_quote (x:P.Spectrum0 3)(s:ℕ) :
    ‖P.quoteRay j x s (s+1) (P.rootSpace f s l) (P.rent_honors j f s l)‖ = ‖P.stateVox j (P.advocate 3 x j) (s+1) (P.flume j (P.rootSpace f s l) (s+1) (P.rent_honors j f s l))‖:=by
 rw [← (P.gnsIn j (P.advocate 3 x j)).norm_map]; unfold quoteRay; rw [P.coincides]

lemma pilot_quote : ∃ Z≥(0:ℝ), ∀ᶠ s:ℕ in atTop,
     (∫ x:P.Spectrum0 3, ‖P.quoteRay j x s (s+1) (P.rootSpace f s l) (P.rent_honors j f s l)‖^2 ∂(P.pillars 3)) ≤ Z:=by
 let z:=1+pairedN (P:=P.par) witnessZ
 obtain ⟨Z,h,p⟩:=P.tiny_purses
 have he:0≤z:=by obtain ⟨s,a⟩:=(P.base_pay j f l Q').exists; exact (norm_nonneg _).trans a
 refine ⟨Z^2*z,mul_nonneg (sq_nonneg _) he,?_⟩
 let ht:= StrictMono.tendsto_atTop (show StrictMono (fun i:ℕ=>i+1) from fun x y g=> add_lt_add_left g 1)
 filter_upwards [P.base_pay j f l Q',ht.eventually p] with s u v
 simp_rw [P.staff_quote j f l _,P.heartfelt_q,P.piece_fee j f l]
 exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) v.2 _) u (norm_nonneg _) (sq_nonneg _)
/-- Almost surely, the pilot of these straight quotes has affordable cost,
  exponentially in the rung distance. Not assumed on arbitrarily varying states. -/
lemma pilotsBudget : ∃ K> (0:ℝ), ∀ᵐ x:P.Spectrum0 3 ∂(P.pillars 3),∀ᶠ s:ℕ in atTop,
      ‖P.quoteRay j x s (s+1) (P.rootSpace f s l) (P.rent_honors j f s l)‖ ≤ K * 2^s:=by
 obtain ⟨Z,hz,p⟩:=P.pilot_quote j f l Q'
 obtain ⟨N,H⟩:= eventually_atTop.1 p
 let Z':= 1+Z; have h:0<Z':=by unfold Z'; linarith only [hz]
 let k(s:ℕ)(x:P.Spectrum0 3):= ‖P.quoteRay j x s (s+1) (P.rootSpace f s l) (P.rent_honors j f s l)‖
 let d(s:ℕ):= Z'* 2^s; have H₀(s:ℕ):0<d s:= mul_pos h (by positivity)
 have hK(s:ℕ): Continuous (fun x=>(k s x)^2):=by
   unfold k; simp_rw [P.staff_quote]; exact (P.state_cont_cost j _).comp (P.otherSpectrum 3 j).continuous
 let S(n:ℕ)(_:Unit)(x:P.Spectrum0 3):=if N≤n then (k n x)^2 else (0:ℝ)
 have g(n:ℕ)(j:Unit):Continuous (S n j):=by
   by_cases p:N≤n
   · simp_rw [S,if_pos p]; exact hK n
   simp_rw [S,if_neg p]; exact continuous_const
 have u(n:ℕ)(j:Unit)(x:P.Spectrum0 3):0≤ S n j x:=by unfold S; split; exact sq_nonneg _; exact le_rfl
 have e(n:ℕ)(j:Unit): (∫ x:P.Spectrum0 3, S n j x ∂(P.pillars 3)) ≤ Z:=by
   by_cases p:N≤n
   · simp_rw [S,if_pos p]; exact H n p
   simpa only [S,if_neg p,integral_zero] using hz
 refine ⟨Z',h,(prognosis S _ g u d H₀ e ?_).mono fun x y=>?_⟩
 · intro n; simp only [Fintype.card_unit,Nat.cast_one,one_mul]
   unfold discount d; rw [mul_pow, inv_pow, sq ((2:ℝ)^n), mul_assoc, mul_assoc, mul_inv_cancel₀ (show (2:ℝ)^n≠0 by positivity),mul_one]; exact le_trans (by unfold Z'; nlinarith only [hz] : Z ≤ Z'^2) (le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (by norm_num)))
 filter_upwards [y, eventually_ge_atTop N] with n p a
 have ht:=p (); unfold S at ht; rw [if_pos a] at ht; exact (sq_le_sq₀ (norm_nonneg _) (H₀ n|>.le)).mp ht.le
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
