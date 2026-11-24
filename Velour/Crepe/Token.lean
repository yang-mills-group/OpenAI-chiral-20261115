import Velour.Crepe.Backer
import SatinThinFare
/-! Pointwise price for masked root. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6200
set_option maxHeartbeats 1200000
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
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
/-! # Fix ranks independently of layout and period. Extract for every *fixed* v from very same P (no law mutation). -/
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
variable {A C U:ℝ}

open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke Worth VelourBoard
variable {B:ℕ}{X:Cover}

open StressFlux AnalyticBridge.VerifiedReset
section
variable {n:Side}{G:Gauge}(U:Config G n)(o:Site n)(p:PlaqAxes)
-- adapted YM/SU5/Thin/Camp/Plume
private lemma petalBar (τ:ℝ)(p₀:CF.Scree.pingS τ (halo 10 {o}) U): ‖petals U o p‖ ≤ τ:=by
 have he(s t: Step)(h:s.dir<t.dir): ‖plate U o s t‖ ≤ τ:=by unfold StressFlux.plate; refine (G.curvature_norm _).trans ?_; rw [price_shift_pos G.chord U G.chord_inv (fun k g => G.chord_conj g k) s t o]; exact (p₀ (atFace o s t,⟨(s.dir,t.dir),h⟩) (fun p=> Finset.disjoint_left.mp p (halo_spec.mpr ⟨o,mem_singleton_self _,by simp⟩) (Square.touched_here o s t h))).le
 let i:=posDir p.val.1; let j:= posDir p.val.2; let x:=negDir p.val.1; let y:=negDir p.val.2
 unfold AnalyticBridge.VerifiedReset.petals clover stencil; rw [norm_smul]; change _*‖(plate U o i j-plate U o i y)-(plate U o x j-plate U o x y)‖≤ τ; apply (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (he i j p.property) (he i y p.property))) ((norm_sub_le ..).trans (add_le_add (he x j p.property) (he x y p.property))))) (norm_nonneg _)).trans_eq (?_); rw [Real.norm_eq_abs]; norm_num; ring

end

-- one token
abbrev token:ℝ:= (∑i:PlaqAxes, |starWeight i|) +1
lemma tk_budget : (∑i:PlaqAxes, |starWeight i|)/2 ≤ token ∧ 0<token:=by
 have w:=Finset.sum_nonneg (s:=Finset.univ) (f:=fun i:PlaqAxes=> |starWeight i|) (fun i _=> abs_nonneg _); unfold token; constructor <;> linarith only [w]



lemma tokenBar {n:Side} (τ:ℝ)(o:Site n) (E:Pane n)
 (p: pingS τ (Lattice.halo 10 {node o}) E) : |quadScore (node o) E| ≤ τ^2*token:=by
 unfold quadScore; rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
 let S:= ∑i:PlaqAxes, |starWeight i|
 suffices |(∑i:PlaqAxes, starWeight i * ‖petals E (node o) i‖^2)|≤ τ^2*S from
    calc _ ≤ τ^2*(S/2):=by rw [←mul_div_assoc]; gcongr
         _≤ _:=mul_le_mul_of_nonneg_left tk_budget.1 (by positivity)
 unfold S; refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_
 rw [abs_mul,abs_of_nonneg (by positivity:0≤ ‖petals E (node o) i‖^2),mul_comm]; gcongr
 exact petalBar E _ _ _ p
lemma scoreCost {n:Side} (τ:ℝ)(o:Site n)(E:Pane n)(b:ℝ)(p:|b|≤1): |clothMark b τ o E| ≤ token:= by
 unfold clothMark; split; swap
 · exact abs_zero.trans_le tk_budget.2.le


 rename_i h; have hp:=tokenBar τ o E h
 by_cases u:τ=0; · simp [u]; exact tk_budget.2.le
 rw [←mul_div_right_comm,abs_div,abs_of_pos (sq_pos_of_ne_zero u), div_le_iff₀ (sq_pos_of_ne_zero u),abs_mul]
 exact le_trans (mul_le_mul p hp (abs_nonneg _) (by norm_num)) (by rw [one_mul,mul_comm])
lemma token_paid (r:ℕ)(h:|slotFee P.par r|≤1) : P.singleQuiet r token:=by
 intro i k _ x T
 unfold routeTip turfMark
 let τ:=(RootBook Y i k r).p.threshold
 rw [Complex.ofReal_one,one_smul]
 exact ⟨_,(Complex.norm_real _).trans_le (show ‖clothMark _ τ x T.1‖≤_ from
        Real.norm_eq_abs _|>.trans_le (scoreCost _ _ _ _ h)),rfl⟩
-- eventual fees
lemma slotlate : ∀ᶠs in atTop,0<slotFee P.par s ∧ slotFee P.par s≤1:=
 ((turnover P.par).eventually (cap_meter P.par.R)).mono fun _ h=> ⟨h.2.2.1,h.2.2.2.1.trans h.2.2.2.2⟩


/-- Independent of v, and fixed base and f comparison r=f+1. -/
def dayRate (A:ℝ):=
 4*Real.exp (8*A+1)/zoomM L +4*(token*Real.exp 1)
lemma day_p : 0 < P.dayRate A:=by
 unfold dayRate; have h:=tk_budget.2; have h':=zoomM_p L; positivity
lemma paysDay :
  ∀ᶠ f:ℕ in atTop,0 < slotFee P.par f ∧ P.singleQuiet (f+1) token ∧
    P.cordRate A f (f+1) token ≤ P.dayRate A:=by
 filter_upwards [P.slotlate, eventually_forall_ge_atTop.mpr P.slotlate] with f h q
 refine ⟨h.1,P.token_paid _ ((abs_of_pos (q (f+1) (Nat.le_succ _) |>.1)).trans_le
      ((q (f+1) (Nat.le_succ _)).2)),?_⟩ 
 unfold cordRate dayRate owedF
 rw [Nat.cast_one,mul_one,pow_one,show f+1-f=1 from Nat.add_sub_cancel_left f 1, pow_one]
 have hp:= zoomM_p L; gcongr
 exact mul_le_of_le_one_left (by positivity) h.2
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

