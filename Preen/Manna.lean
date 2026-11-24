import Preen.Horns
import Preen.Burden
import Preen.Spurt
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Dyad Keeping
open Ballad Cordial Cheer Prototype Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn Designs Twah Six Habitat Habitat.Hemlock
open Py.Rate.Pitching.Focus (Morn)
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))(T:RobeRoad P F C D x)(α:ℝ)(v:Jones P M α F C D x)
open _root_.YM.Preen
open CF.BProof Pressure SectorNext.Remainder.Scales SectorNext.Remainder
local notation "Lq"=> P.par.R.L
local notation "L" => (P.par.R.L.val:ℝ)
local notation "Zx"=> Vale.hat (Lq) P.par.x
abbrev stairW(d:ℕ):ℕ:=64*d^2
abbrev stackW(d:ℕ):ℕ:=hikeV d+stairW d
local notation "b"=> Vale.billX (Lq)
private lemma bankH : 0<b:= by unfold Vale.billX; have hz:=P.par.R.coarse; exact mul_pos (Gauge.slopeConstant_pos CF.Thera.yet_one) (Real.log_pos (by exact_mod_cast (hz.trans_lt' (by norm_num:1<3))))
lemma aboveWe : ∀ᶠ d:ℕ in atTop, (peaks d:ℝ)*(b/2) ≤ Zx (stackW d)∧ Zx (stackW d) ≤ (peaks d:ℝ)*(3*b) :=by
 filter_upwards [x_here _ P.par.x (bankH P) 64 Zx (fun s=>rfl)] with d e
 have hr:(peaks d:ℝ)≤ (stackW d:ℝ):=by exact_mod_cast (Nat.le_add_right (hikeV d) (stairW d))
 refine ⟨e.1.trans (add_le_add_right (mul_le_mul_of_nonneg_right hr (bankH P).le) _),e.2⟩
lemma aboard : ∀ᶠ d:ℕ in atTop, shoreH d ≤ breeze (Zx (stackW d))^25 ∧ breeze (Zx (stackW d)) ≤ shoreH d^4:= (mint_arctic _ (bankH P) _ (aboveWe P)).mono fun d h=>⟨h.2.1,h.2.2.1⟩
lemma hollowγ : ∀ᶠ d:ℕ in atTop, (reachQ P (hikeV d):ℝ) ≤ (shoreH d)^8:=by
 have hp:Tendsto (fun d:ℕ=> (2:ℝ)^d) atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt one_lt_two
 let K:=P.calibration
 have Bp:∀ᶠ d:ℕ in atTop,0<Zx (hikeV d) ∧ 0≤Real.log (Zx (hikeV d)) ∧ Real.log (Zx (hikeV d)) ≤ 2*(2:ℝ)^d:=by
    let h:= (x_here _ P.par.x (bankH P) 0 (Zx) (fun s=>rfl))
    simp only [Nat.zero_mul,Nat.add_zero] at h
    refine (mint_arctic _ (bankH P) _ h).mono fun d a'=>⟨a'.1,Real.log_nonneg (le_trans ?_ (crown ..)),a'.2.2.2⟩
    exact (one_le_ofReal P)
 filter_upwards [Bp,Preen.tripleH,shore_up.eventually_gt_atTop ((K.ℓ:ℝ)+pollN P+10000)] with d g t u
 let v:=shoreH d; have ht:1≤v:=shore_paid _
 let m:= (radiusB (Zx (hikeV d)):ℝ)
 have hm:m≤5*v^2:=by
    have hz:m≤ (Real.log (Zx (hikeV d)))^2 +1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hu:= g.2.2.trans (mul_le_mul_of_nonneg_left t (zero_le_two))
    nlinarith only [pow_le_pow_left₀ g.2.1 hu 2,hz,ht]
 have hq : ((P.run.meter.a (hikeV d)).B:ℝ)=m:=congrArg (Nat.cast (R:=ℝ)) (P.run.meter.boot _|>.2.1)
 unfold reachQ minB Calico.amount; push_cast; change _ ≤ v^8; rw [hq]
 let l:= ((P.calibration.ℓ:ℝ)+ pollN P+10000)
 change l<v at u
 have hp':(P.calibration.ℓ:ℝ)+(pollN P)+22 ≤ v:= (show _≤ l from (by unfold l; linarith))|>.trans u.le
 have hn:(16:ℝ)*(K.B.val:ℝ)=pollN P:=(Eq.trans (congrArg (fun z:ℝ=>z*(K.B.val:ℝ)) ((show (16:ℝ)=((16:ℕ):ℝ) by norm_num))) (Nat.cast_mul 16 K.B.val).symm)
 have hv:(10000:ℝ)<v:=lt_of_le_of_lt (le_add_of_nonneg_left (by positivity)) u
 have hy:m^3≤125*v^6:=(pow_le_pow_left₀ (by unfold m; positivity) hm 3).trans_eq (by ring)
 have hw: v^6 ≤ v^7:=pow_le_pow_right₀ ht (by norm_num)
 have hk: v^2 ≤ v^6:=pow_le_pow_right₀ ht (by norm_num)
 rw [←hn] at hp'
 nlinarith only [hy,hw,hk,hm,hp',mul_le_mul_of_nonneg_right hv.le (show 0≤v^7 by positivity)]
where one_le_ofReal(P:Spine):1≤P.par.x:= le_trans (Real.one_le_exp (by norm_num)) P.large
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
