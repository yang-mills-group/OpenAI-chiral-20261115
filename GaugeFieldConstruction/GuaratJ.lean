import GaugeFieldConstruction.RepleteJ
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.
variable {m i k f:ℕ}
local notation "ΤΓ"=> P.run
local notation "ΓΥ"=> P.run.uv k
variable (w:f0 ≤ P.run.uv k)(h:(P.run.voyage i).kick≤ k)
local notation "Qi"=> p.Z i k w h
#check ProbeθJ
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (Ω:BoonsθJ p B0 M i k w h)(x:P.VMark)(R:Signed × Bool)(u:BandS)
variable {s t r:ℕ} {n:ℕ}
local notation "Ξu"=> Fin (θ u)
local notation "Φ"=> (ΓPrimary P.run i k θ)
local notation "η"=> FrameK (Fin (θ u))
variable (W:X→LaurelJ)(L:finsJ)(U:X→ Signed × Bool)(S:X→P.VMark)(Y:BoardDate X)
variable (B:SailκJ X θ→Waves)(Z:PlumberJ P.run i k X θ)(H: SalaryJ p B0 M i k w h S W U Y B f Z) (x':X) (tQ:R=U x')(pX:S x'=x)
local notation "Fν"=> FrameK (Fin (θ u))
-- Base x, any grade.T Echo test for any y at j*. Expresses ETOP independent Layout, Mirror.C law.
local notation "KΡ"=> RankQJ P.par
local notation "Zζ"=> P.run.uv k
variable (v:LaurelJ) (y:FrameK (Fin (θ u)))
-- label constraints.
set_option linter.unusedSectionVars false
set_option maxHeartbeats 240000
variable (Hv:Adept_T θ B0 M G)
-- reconstruct qualifications for FIN n constant. define transport-independent charge
local notation "cΞ"=> (TideMaskJ (f:=f) p w h B0 M Ω x R u)
local notation "ΤΩ"=> EchoTideJ (f:=f) p w h B0 M Ω x R u
local notation "Αζ"=> SailGateJ p w h B0 M Ω x R u
local notation "Ακ"=> SailSubsidyJ p w h B0 M Ω x R u
local notation "MΤ"=> Mark (side P.run i Zζ)
-- hull_any.Mark on ALL arrangements carrying grants. $L used only in grip. require boot zero. ANY Salary path constant x and R; V lens.Any Y Budget along b=claim from α. Shift palette P inside.
variable (m:ℕ)(κ:ℕ→BandS→ Fin 6)
-- fixed schedule small. Collapse bound by trajectory.
variable (z:Collapse_J P n i f)
local notation "δf"=>P.par.R.L
open SlabMark.Etch
lemma roomProfitJ (z:Collapse_J P n i f): let T:=(P.par.R.L.val^f) *2*P.par.block.val*2; 0<n ∧ n ≤ T^4*((P.run.ir i).val)^4 :=by
 intro T; obtain ⟨r,h,p⟩:=z; constructor
 · by_contra! t
   have hp: n=0:=by omega
   exact (ne_of_gt (pow_pos (mul_pos (by norm_num:0<(4:ℕ)) h.pos) 4)) (Nat.eq_zero_of_le_zero ((p.1).trans_eq (by rw [hp])))
 have he:= h.low; let j:=4*r; let x:=SlabMark.Etch.pitch P.calibration.B (WorkWJ P f); have h1:0<x:= pitch_pos _ h.wid
 have hd:j ≤ (More (Journey.side P.run i f)).val:= le_trans (le_mul_of_one_le_left (Nat.zero_le j) h1) he
 apply p.2.trans; apply (pow_le_pow_left' hd 4).trans; rw [show (More (Journey.side P.run i f)).val=T*(P.run.ir i).val from ?_,mul_pow]
 change (mesh (P.run.ir i) P.par.R.L f).val*2*P.par.block.val*2=T*(P.run.ir i).val; unfold mesh T; push_cast; ring
lemma GateGlanceJ {m:ℕ}(a:Collapse_J P n (P.gatePeriod m) f):n ≤ (((P.par.R.L.val)^f)*2*P.par.block.val*2)^4*P.run.uv (P.gateCut m):=by
 let h':=(P.run.ir (P.gatePeriod m)).property; exact (roomProfitJ a).2.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right h' (show 4≤5 from by omega)).trans (P.history.gate m))) -- tune
-- real plume. n≤C*s. Δ.O. small bound `ε^n` useful
open Real
lemma WingtailJ (P:Spine)(K A B ε:ℝ)(hk:0≤K)(ha:1≤A)(hB:0≤B)(e:0<ε) : ∀ᶠ s:ℕ in atTop,∀ n:ℕ,(n:ℝ)≤ K*s → (n:ℝ)*(plumeZ P.par.R.L s)⁻¹*(B*A^s)^n ≤ ε^n :=by
 let q:= (P.par.R.L.val:ℝ)^((1:ℝ)/4); have hv:1<q:= one_lt_rpow (by exact_mod_cast (show 1<P.par.R.L.val from lt_of_lt_of_le (by norm_num:1<3) P.par.R.coarse)) (by norm_num); have hq:0<q:= zero_lt_one.trans hv
 have hv1:q⁻¹<1:=(inv_lt_one₀ hq).2 hv; have hw(s:ℕ):plumeZ P.par.R.L s= Real.exp (q^s):=by unfold q plumeZ; rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (P.par.R.L.val:ℝ) from by positivity)]; ring_nf -- name tune
 let b:=max 1 (B/ε)
 have hp:1 ≤ b:=le_max_left ..; have hx:0≤B:=hB
 let d:=log A; let c:=log b; have hc:0≤ c:= log_nonneg hp; have hd:0≤d:=log_nonneg ha
 let D(s:ℕ):= K*s + c*K*s + d*K*s^2 -- may Nat s^2 cast simp
 have h0:Tendsto (fun s:ℕ=>D s*(q⁻¹)^s) atTop (𝓝 0):=by
    let hz:=tendsto_pow_const_mul_const_pow_of_lt_one 2 (inv_nonneg.mpr hq.le) hv1; let hz':=tendsto_pow_const_mul_const_pow_of_lt_one 1 (inv_nonneg.mpr hq.le) hv1; have he:= ((hz'.const_mul K).add (hz'.const_mul (c*K))).add (hz.const_mul (d*K)); unfold D; simpa only [mul_zero,zero_add,pow_one,add_mul,mul_assoc] using he -- tune cast
 filter_upwards [h0.eventually (gt_mem_nhds (show 0<(1:ℝ) from zero_lt_one))] with s v n hN -- tune
 have heD:D s ≤ q^s := (le_of_lt ((mul_inv_lt_iff₀ (pow_pos hq s)).1 (show D s*(q^s)⁻¹ < 1 from by rw [← inv_pow]; exact v))).trans_eq (one_mul ..) -- tune
 rw[hw]; have hg: (n:ℝ)*((B/ε*A^s)^n)≤ Real.exp (q^s):=by
    have ht(s':ℝ): s'≤ Real.exp s':= by linarith [add_one_le_exp s'] -- names
    refine le_trans (mul_le_mul (ht n) (pow_le_pow_left₀ (mul_nonneg (div_nonneg hx e.le) (pow_nonneg (zero_le_one.trans ha) _)) (mul_le_mul_of_nonneg_right (show (B/ε) ≤ b from le_max_right ..) (pow_nonneg (zero_le_one.trans ha) _)) n) (by positivity) (Real.exp_pos _).le) ?_
    have hx': (b*A^s)^n=Real.exp (n*(c+(s:ℝ)*d)):=by rw [Real.exp_nat_mul, Real.exp_add, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans_le hp),Real.exp_log (zero_lt_one.trans_le ha)] -- reverse
    rw [hx',←Real.exp_add]; apply Real.exp_monotone; refine le_trans (add_le_add hN (mul_le_mul_of_nonneg_right hN (by positivity))) (le_trans (le_of_eq ?_) heD); unfold D; ring
 have hG:=mul_le_mul_of_nonneg_right hg (pow_nonneg e.le n); rw [mul_right_comm]; apply (mul_inv_le_iff₀ (Real.exp_pos _)).2; apply le_trans _ (hG.trans_eq (mul_comm _ _)); apply le_of_eq; rw [mul_assoc,←mul_pow,show B/ε*A^s *ε = B*A^s from (by field_simp)]; -- tune
#print axioms GateGlanceJ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
