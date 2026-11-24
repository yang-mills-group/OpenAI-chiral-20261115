import Preen.Inquests
import Preen.Vise
import Preen.Gamma
import Preen.FoyerX
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
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
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Nc" i:max=> count P.run s i
local notation "Y"=>P.run
local notation "π₀" i:max => P.period (P.projection.rows i)
local notation "ζ₀" i:max => P.cutoff (P.projection.columns i)
open _root_.YM.Gleam.Luster Almanac _root_.YM.Preen
variable (LH k:ℕ)
local notation "φ"=>scaleY
local notation "M" n:max=> φ (hat P.par.R.L P.par.x (stackW n))
local notation "T" n:max=> stampβ P LH n
noncomputable abbrev Petty (P:Spine)(n LH A:ℕ)(i:Schema (stampβ P LH n)):P.Test:=
 let s:=stackW n; let w:= intervalZ s LH P; trialY P s (3*w+10) (parka i) i.2 (pilot P s A (parka i) i.2).price A
variable (pc:BoltCharge P.run)(pH:∀ᶠ s:ℕ in atTop,∀ i k,(P.run.voyage i).kick ≤ k→s ≤ P.run.uv k→ closeDen P.run s i k)
include pc pH
private lemma prop_e :∀ᶠ n:ℕ in atTop,∀ i:Schema (T n), ∫ x,‖P.singleState 3 (stackW n) x (Petty P n LH A i)‖^2∂P.pillars 3 ≤ Real.exp 10:=by
 have he:Tendsto stackW atTop atTop:=tendsto_atTop_mono (show hikeV≤ stackW from fun i=>Nat.le_add_right ..) goes_town
 filter_upwards [he.eventually (budgetα P A LH),feeRatio P,he.eventually (fuelAgenda P A pc pH)] with n q t h i
 let w:=intervalZ (stackW n) LH P; let d:=stampβ P LH n
 have hs:withinT (parka i) (3*w+10):=fun b j=>by obtain ⟨a,c⟩:=(epochCount i) b j; change _≤ _ ∧ _ ≤ ((3*w+10:ℕ):ℤ); unfold stampβ at a c; change _ ≤ _ ∧ _ ≤ _; change - ((2*(w+1)+1:ℕ):ℤ) ≤ _ at a; change _≤ ((2*(w+1)+1:ℕ):ℤ) at c; omega
 exact (health P (stackW n) A (parka i) i.2 (3*w+10) hs (pilot P ..) t.1 h).trans (Real.exp_le_exp.mpr (by linarith only [q]))
local notation "J" n:max=> Schema (T n)
lemma hauteur :∀ᵐ x∂P.pillars 3,∀ᶠ n:ℕ in atTop,∀ i:Schema (T n),
 ‖P.singleState 3 (stackW n) x (Petty P n LH A i)‖≤ (M n)^(25+8*LH+22):=by
 let q(n:ℕ):=¬ ∀ i:Schema (T n), ∫ x,‖P.singleState 3 (stackW n) x (Petty P n LH A i)‖^2∂P.pillars 3 ≤ Real.exp 10
 let S(n:ℕ)(i:Schema (T n))(x:P.Spectrum0 3):= if q n then 0 else ‖P.singleState 3 (stackW n) x (Petty P n LH A i)‖^2
 have hc(n:ℕ)(i:Schema (T n)):Continuous (S n i):=by
    unfold S; split; · exact continuous_const
    exact ((P.chi_joint 3 (P.reading 3 _ _)).norm.pow _)
 have hn(n:ℕ)(i:Schema (T n))(x:P.Spectrum0 3):0 ≤ S n i x:=by unfold S; split; rfl; exact sq_nonneg _ -- rfl LE
 have hB(n:ℕ)(i:Schema (T n)): (∫ x,S n i x∂ P.pillars 3) ≤ Real.exp 10:=by
    unfold S; split<;> rename_i h; · rw [integral_zero]; exact (Real.exp_pos _).le
    exact (not_not.mp h) i
 let F(n:ℕ):ℝ:= Fintype.card (Schema (T n))
 haveI(n:ℕ):Nonempty (Schema (T n)):=⟨(fun _ _=>⟨0,by omega⟩,false)⟩
 have hF(n):1≤ F n:=by unfold F; exact_mod_cast (show 1 ≤ Fintype.card (Schema (T n)) from  (Fintype.card_pos (α:=Schema (T n))))
 let K0:=Real.exp 10
 have hK:1≤K0:=Real.one_le_exp (by norm_num)
 let D(n:ℕ):ℝ:=2^n*F n*K0
 have hD(n):0<D n:=mul_pos (mul_pos (pow_pos zero_lt_two _) (zero_lt_one.trans_le (hF n))) (Real.exp_pos _)
 have he:= prognosis S (fun _=>K0) hc hn D hD hB (fun n=>?_) (μ:=P.pillars 3)
 swap
 · change (F n)*K0 ≤ discount n (D n); unfold discount D; rw [inv_pow]; field_simp
   have h₀:1≤ (2:ℝ)^n:=(one_le_pow₀ (by norm_num))
   have h:1 ≤ F n*K0:= one_le_mul_of_one_le_of_one_le (hF _) hK
   nlinarith only [mul_le_mul_of_nonneg_right h (show 0≤F n from zero_le_one.trans (hF _)), mul_le_mul_of_nonneg_right h₀ (show 0≤F n^2*K0 from mul_nonneg (sq_nonneg _) (zero_le_one.trans hK))] -- syntax
 filter_upwards [he] with x HE
 have hE:Tendsto (fun n=>M n) atTop atTop:=Gleam.Luster.Risa.summitG.comp (turnover P.par|>.comp (tendsto_atTop_mono (show hikeV ≤ stackW from fun _=>Nat.le_add_right ..) goes_town))
 filter_upwards [HE, Preen.tripleH, haway P LH,hE.eventually_ge_atTop K0, aboard P,prop_e P A LH pc pH] with n h ht hW hL hT hu i
 specialize h i; unfold S at h; rw [if_neg (show ¬ q n from fun h=>h hu)] at h
 apply ((pow_lt_pow_iff_left₀ (norm_nonneg _) (hD n|>.le) (by omega:2≠0)).mp h).le.trans
 let r:ℝ:= M n; have hm:1 ≤ r:= Gleam.Luster.Risa.summitT _
 have hx:(2:ℝ)^n ≤ r^25:=by apply ht.trans; unfold r; rw [coin_scale]; exact hT.1
 have hg:r ≤ r^2:=by nlinarith only [hm]
 unfold D
 calc
 _ ≤ (r^25*r^(8*LH+20))*r^2:= mul_le_mul (mul_le_mul hx hW (zero_le_one.trans (hF _)) (pow_nonneg (zero_le_one.trans hm) _)) (hL.trans hg) (Real.exp_pos _).le (by positivity)
 _ = _:= by rw [←pow_add,←pow_add]; unfold r; congr 1
#print axioms hauteur
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
