import Preen.Manna
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
local notation "b"=> Vale.billX (Lq)
private lemma bank':0<b:=by unfold Vale.billX; have hz:=P.par.R.coarse; exact mul_pos (Gauge.slopeConstant_pos CF.Thera.yet_one) (Real.log_pos (by exact_mod_cast hz.trans_lt' (by norm_num:1<3)))
-- shifted gas beta inverse
lemma feeRatio : ∀ᶠ d:ℕ in atTop, 0 < payday P (stackW d)∧ 0 ≤ payday P (hikeV d)∧ payday P (hikeV d) ≤ 8*payday P (stackW d) :=by
 let n(s:ℕ):=Zx (s+1)
 have hz:Tendsto (fun d:ℕ=>(peaks d:ℝ)*(b/2)) atTop atTop:= (tendsto_natCast_atTop_atTop.comp goes_town).atTop_mul_const (half_pos (bank' P))
 have hm:=x_here (b) P.par.x (bank' P) 64 (Zx) (fun s=>rfl)
 filter_upwards [hm,hz.eventually_gt_atTop 1] with d e p
 let a:=stackW d; let i:=hikeV d
 have hv : (i:ℝ)*(b/2) ≤ n i∧ n a ≤(i:ℝ)*(4*b) :=by
    have h₀:1 ≤ (i:ℝ):=by exact_mod_cast (show 1 ≤ hikeV d from Nat.one_le_of_lt (pow_pos (by omega) _))
    have ht:(Zx (i+1))= Zx i+b:=by rw [Vale.hat_succ]; rfl
    have ht':(Zx (a+1))= Zx a+b:=by rw [Vale.hat_succ]; rfl
    unfold n; rw [ht,ht']; change (i:ℝ)*(b/2) ≤ Zx i ∧ Zx a ≤ (i:ℝ)*(3*b) at e; obtain ⟨y,t⟩:=e; have hu:=bank' P; constructor<;> nlinarith only [h₀,y,t,hu]
 have h':0<(i:ℝ)*(b/2):=lt_trans zero_lt_one p
 have he: 0<n i:=h'.trans_le hv.1
 have hu:(i+1:ℕ) ≤ a+1:=Nat.add_le_add_right (Nat.le_add_right _ _) _
 have hN:n i ≤ n a:=add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hu) (bank' P).le) _
 have ht:0<n a:= he.trans_le hN
 have hg(u:ℕ)(e:0<n u): payday P u=(n u)⁻¹:=by
    have hs: n u= Scales.y SU.group (Lq) (Zx u):= Vale.hat_succ _ _ _
    rw [hs]; rw [hs] at e -- problematic
    have he:=Scales.yg2 SU.group (Lq) (x:=Zx u) e -- n issue
    change Scales.g SU.group (Lq) (Zx u)^2=_; field_simp; linarith
 rw [hg i he,hg a ht]
 refine ⟨inv_pos.mpr ht,(inv_pos.mpr he).le,?_⟩
 field_simp; linarith only [hv.1,hv.2]
lemma boostScale : 0<L∧64*L^4 ≤ ThinGauge.boost (Xη (Lq)):=by
 have ht:P.par.R.L.val≥1:= P.par.R.L.property
 have hv:(1:ℝ)≤L:=by exact_mod_cast ht
 have hp:0<L:=zero_lt_one.trans_le hv
 refine ⟨hp,?_⟩
 unfold ThinGauge.boost Xη ThinGauge.gain
 change _ ≤ (64*ThinGauge.Bmain+64)/L⁻¹^4
 rw [inv_pow, div_inv_eq_mul]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by linarith only [ThinGauge.bm_pos])) (pow_nonneg hp.le _)
-- allowances. R= trailerH exactly.Native pose distance. Want R^4 q> etc. bounds Radi . 
lemma travelCast (d k:ℕ): (trailerH P d k:ℝ)= L^k*(reachQ P (hikeV d):ℝ)+(idleCar P:ℝ):= by
 unfold trailerH idleCar; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one]; ring
lemma keyV :∀ᶠ d:ℕ in atTop,let k:=stairW d; let R:ℝ:=(trailerH P d k:ℝ)
 ((thresholdU P M α d k)*R^4*(shoreH d)^9) ≤ payday P (stackW d) :=by
 let Λ(d:ℕ):ℝ:=reachQ P (hikeV d)+(idleCar P:ℝ)
 let A:=32*priceQ (P:=P) M α *Real.exp 1; have hp:0 ≤ A:=by unfold A; have h:=Real.exp_pos (1:ℝ); unfold priceQ; positivity
 have bL: (1:ℝ) ≤ L:=by exact_mod_cast P.par.R.L.property
 have hz:∀ᶠ d:ℕ in atTop,0≤Λ d∧Λ d ≤ shoreH d^10:=by
    filter_upwards [hollowγ P,shore_up.eventually_gt_atTop ((idleCar P:ℝ)+2)] with d t p
    have hw:1 ≤ shoreH d:=shore_paid _
    have ht:shoreH d  ≤ shoreH d^8:= by simpa only [pow_one] using (pow_le_pow_right₀ hw (show 1 ≤8 by omega))
    unfold Λ; constructor
    · positivity
    have hc:(idleCar P:ℝ)+2< shoreH d:= p
    have hθ:(2:ℝ) ≤ shoreH d:= (by linarith only [hc,Nat.cast_nonneg (α:=ℝ) (idleCar P)])
    nlinarith only [t,ht,hc,mul_le_mul_of_nonneg_right hθ (show 0 ≤ shoreH d^8 by positivity),pow_le_pow_right₀ hw (show 9 ≤10 by omega)]
 filter_upwards [feeRatio P,heavy_cut bL hz hp] with d f t k R
 obtain ⟨hl,hb⟩:=boostScale P
 let Q:=ThinGauge.boost (Xη (Lq))
 have hq:0<Q:=boostP _
 have he:(2/Q)^k ≤ (2/(64*L^4))^k:= pow_le_pow_left₀ (div_nonneg (by norm_num) hq.le) (by gcongr) k -- likely missing positivity
 let y:= payday P (stackW d)
 have hy: R^4 ≤(L^k * Λ d)^4:= by
    have g:1 ≤ L^k := one_le_pow₀ bL
    have hℓ:R=L^k*(reachQ P (hikeV d):ℝ)+(idleCar P:ℝ):=travelCast ..
    refine pow_le_pow_left₀ (by unfold R; positivity) ?_ 4
    unfold Λ; rw [hℓ,mul_add]; gcongr; exact le_mul_of_one_le_left (by positivity) g
 let m:= priceQ (P:=P) M α; have hM:0 ≤ m:=by unfold m priceQ; positivity
 have hh: thresholdU P M α d k ≤ y*((2/(64*L^4))^k *((2:ℝ)^d*A)):= by
    let z:=payday P (hikeV d); have hw: z ≤ 8*y:=f.2.2
    change 2*((2/Q)^k*(2^d*(2*(z*m*Real.exp 1))))≤_
    have ho:0 ≤ z:=f.2.1
    unfold A; change _≤ y*((2/(64*L^4))^k *((2:ℝ)^d*(32*m* Real.exp 1)))
    calc
      _ ≤ 2*((2/(64*L^4))^k*(2^d*(2*((8*y)*m*Real.exp 1)))):=by gcongr
      _= _:=by ring
 calc
   _ ≤ y*((2/(64*L^4))^k *((2:ℝ)^d*A)) * ((L^k * Λ d)^4) * shoreH d^9:= by gcongr
   _ ≤ y:=by have hw:=mul_le_mul_of_nonneg_left t f.1.le; change y*_ ≤ _ at hw; unfold k; linarith only [hw]
#print axioms keyV
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
