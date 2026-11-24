import Velour.Tassel.Shift
import YM.SU5.Six.Aprons
set_option autoImplicit false

set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
set_option maxHeartbeats 800000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set

open Py.Rate.LocalLimit.Papal (Weaver household meanF)
variable (P:Spine)(Z:Lead.Clan)(n:ℕ)
local notation "e₃"=> YM.basis (3:Axis)
local notation "ℓ"=> P.calibration.ℓ

def velvetBirth : Fin 1 → Twah := fun _=>liftS (P.flash n)
local notation "ℱ"=>nearPoints n (P.velvetBirth n)
local notation "ﬂ"=> (ℓ:ℝ)/(n:ℝ)
lemma vB_l (p:0<n):
 (ℱ) (0,false)=ﬂ • e₃+e₃:=by
 change riseX n (P.kernel0 n)=_
 ext j; by_cases t:j=3
 · subst j; simp [riseX,moor,kernel0,add_div]; exact p.ne'
 simp [kernel0,riseX,moor,t]
lemma vB_r(p:0<n): (ℱ) (0,true)=ﬂ • e₃+(2:ℝ) • e₃:=by
 change riseX n (P.flash n).death=_
 have ht:0<(n:ℝ):=by exact_mod_cast p
 ext j; by_cases t:j=3
 · subst j; simp [riseX,moor,kernel0,flash,add_div];rw [div_self ht.ne'];ring
 simp [kernel0,flash,riseX,moor,t]
lemma vB_dist(p:0<n): (ℱ) (0,true) - (ℱ) (0,false)=e₃:=by
 rw [P.vB_l n p,P.vB_r n p]; module


lemma vB_spill(p:0<n)(q:ℓ<n): Spill (P.velvetBirth n) (3*‖e₃‖) ‖e₃‖ n:=by
 have h (i:Cellz (Fin 1)):i=(0,i.2):=Prod.ext (Subsingleton.elim ..) rfl
 have z:‖ﬂ • e₃‖≤‖e₃‖:=by
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    apply mul_le_of_le_one_left (norm_nonneg _) 
    exact (div_le_one (by positivity)).2 (by exact_mod_cast q.le)
 have e:dist ((ℱ) (0,true)) ((ℱ) (0,false))=‖e₃‖:=by rw [dist_eq_norm,P.vB_dist n p]
 constructor
 · intro i; rw [h i,dist_zero_right]; cases i.2
   · rw [P.vB_l n p]
     exact (norm_add_le ..).trans (by linarith [norm_nonneg (e₃)])
   rw [P.vB_r n p]
   exact (norm_add_le ..).trans (by rw [norm_smul (2:ℝ),Real.norm_of_nonneg (show 0 ≤ (2:ℝ) by norm_num)]; linarith)
 intro i j; rw [h i,h j]; cases i.2 <;> cases j.2
 · simp
 · rw [dist_comm,e]; exact fun _=>le_rfl
 · exact fun _=>e.ge
 simp
def velvetSpin (_:Fin 1) : DirSpin := (0,0)
local notation "Pay"=> (purePrice Z:ℂ)
lemma flash_paid (p:0<n): Lead.cash false * (Twah.witness (fun _:Fin 1=>Z) [0] ℱ velvetSpin)= Pay:=by
 rw [chorus2,lyric,Cordial.billX]


 rw [P.vB_dist n p,show Onyx.pencil e₃ (dnSpin (velvetSpin 0).2) (upSpin (velvetSpin 0).1) = P20 from k_birth,price_as]
 unfold numberX
 rw [show Lead.cash false=(1/5:ℂ) by simp [Lead.cash,phaseF]]
 ring

local notation "gap"=>meanF ((P.flash n).groundWord Z) (purePrice Z:ℂ)
local notation "fade"=>P.frontMat Z n - Pay • (1:P.Test)
local notation "Wing"=> insert 0 (P.flash n).patio
local notation "sl"=>Twah.plait (P.velvetBirth n) (fun _ =>Z) [0] n
local notation "pr"=>Twah.witness (fun _:Fin 1=>Z) [0] ℱ velvetSpin

lemma flick_day: Lamour.Bridge.Celeste.Voice gap Wing := by
 let t:= (Lamour.Bridge.Celeste.flourish (P.flash n) Z)
 exact (t.mono (Finset.subset_insert ..)).sub ((Lamour.Bridge.Celeste.Voice.one Wing).hushed Pay)
lemma flick_body:P.tuneK (P.flick_day Z n)= fade:=rfl

lemma flick_shift (p:0<n):gap= Lead.cash false • meanF sl pr:=by
 have ht:(sl) = (liftS (P.flash n)).groundWord n Z:=mul_one _
 unfold meanF
 rw [transferMark, ←P.flash_paid Z n p, ht]; rw [smul_sub,smul_smul]; rfl


lemma flickCrystal {v:ℝ} (t:0<v): ∀ᶠ n in atTop,Clarity (meanF ((P.flash n).groundWord Z) (purePrice Z:ℂ)) P.par.K.j v:=by
 have e:e₃≠(0:Gaia):=by intro h; have ht:=congrArg (fun x:Gaia=> x (3:Axis)) h; simp at ht
 have hx: ‖Lead.cash false‖ ≤ 1:=by
    rw [show Lead.cash false=(1/5:ℂ) by simp [Lead.cash,phaseF]]
    norm_num
 filter_upwards [eventually_gt_atTop ℓ, aroma P.par.K.j (fun _:Fin 1=> Z) [0] velvetSpin 
     (by rw [P.par.kJ]; decide) v (norm_pos_iff.mpr e) (3*‖e₃‖) t] with n p h
 let pn:0<n:=Nat.zero_le _ |>.trans_lt p
 rw [P.flick_shift Z n pn]
 unfold Clarity; filter_upwards [h (P.velvetBirth n) (P.vB_spill n pn p) rfl] with N a q M x c
 rw [Pi.smul_apply,Pi.smul_apply, map_smul]
 rw [smul_eq_mul,norm_mul]
 exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans (a q M x c)


abbrev FlickTone (n b s:ℕ)(c:ℝ) :=
  0<b ∧ (∀ Z:Lead.Clan,∀ j:Axis, 
      P.Tonal j s b (P.frontMat Z n - (purePrice Z:ℂ) • (1:P.Test)) c)
open Lamour.Bridge
/-- Feather estimate. **Unnormalized**. Works with this fixed uniform
purchase P (plus coldness), at all later r across launch sizes:
along an arbitrary n before choosing b, s afterwards.
-/
theorem feather {R:P.Register}{U:Supplier}{e v C:ℝ}
 (paid:uniform P R U e v) (g:P.NightCop) (t:0<C):
  ∀ᶠ n:ℕ in atTop,∀ᶠ b:ℕ in atTop,∀ᶠ s:ℕ in atTop, P.FlickTone n b s C:=by
 let σ:= C/(4*Real.exp 1)
 have pos:0<σ:=by unfold σ; positivity
 have eq:4*(Real.exp 1*σ)=C:=by rw [←mul_assoc,mul_comm]; exact div_mul_cancel₀ C (by positivity)
 rw [←eq]
 filter_upwards [Filter.eventually_all.mpr fun Z=> P.flickCrystal Z (show 0<σ/4 from by positivity)] with n h
 filter_upwards [eventually_gt_atTop 0, Filter.eventually_all.mpr (fun Z=> P.hammockTremor
       (P.flick_day Z n) paid g (Finset.mem_insert_self ..) (h Z) pos)] with b p r
 filter_upwards [Filter.eventually_all.mpr r] with s h
 exact ⟨p,h⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.feather

