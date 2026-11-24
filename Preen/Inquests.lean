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
open _root_.YM.Gleam.Luster Almanac
open _root_.YM.Preen
local notation "φ"=>scaleY
-- PoseWidth. arrays finite. Assertion.H costs input world.Locker.
noncomputable abbrev stampβ(P:Spine)(L d:ℕ):ℕ:= intervalZ (stackW d) L P +1
local notation "f" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
abbrev Schema (w:ℕ):Type:= (Bool→(Axis→Fin (2*w+1))) × Bool
noncomputable abbrev parka {w:ℕ}(j:Schema w)(b:Bool)(i:Axis):ℤ:=(j.1 b i).val-w
lemma epochCount {w:ℕ}(i:Schema w):withinT (parka i) (2*w+1):=by
 intro b j; let x:=parka i b
 have he: nodeC x j=2*x j+1:= rfl --? pointwise nsmul
 have h(i:Schema w): (i.1 b j).val<2*w+1:=(i.1 b j).isLt
 change _ ≤ nodeC x j ∧ nodeC x j ≤ _; rw [he]; unfold x parka; specialize h i; omega
lemma bornSchema{o:Bool→ Cover}{w:ℕ}(p:withinT o w) (b:Bool) :∃ i:Schema (w+1),parka i=o∧ i.2=b:=by
 let y(j:Bool)(i:Axis):ℤ:= o j i+(w+1:ℕ)
 have he(j i): 0 ≤ y j i ∧ y j i<(2*(w+1:ℕ)+1:ℕ):=by obtain ⟨s,t⟩:=p j i; have hv:nodeC (o j) i=2*o j i+1:=rfl; unfold y; rw [hv] at s t; omega
 refine ⟨(fun j i=> ⟨(y j i).toNat,by have hp:=he j i; omega⟩, b),funext fun i=> ?_,rfl⟩; funext j; unfold parka; dsimp only; rw [Int.toNat_of_nonneg (he ..|>.1)]; unfold y; ring
lemma haway(L:ℕ):∀ᶠ d:ℕ in atTop, (Fintype.card (Schema (stampβ P L d)):ℝ) ≤ (f d)^(8*L +20):=by
 have hs:Tendsto (fun i=> f i) atTop atTop:=Gleam.Luster.Risa.summitG.comp (turnover P.par|>.comp (tendsto_atTop_mono (show hikeV ≤ stackW from fun _=> Nat.le_add_right ..) goes_town))
 filter_upwards [hs.eventually_ge_atTop (100:ℝ)] with d h
 let a:= f d; let b:= stampβ P L d
 have hb:(b:ℝ) ≤ a^L+2:= by unfold b stampβ; push_cast; linarith only [(Nat.ceil_lt_add_one (by unfold a; positivity :(0:ℝ) ≤ a^L)).le]
 have hr:1  ≤ a:= Gleam.Luster.Risa.summitT _
 have hy:(2:ℝ)*(b:ℝ)+1 ≤ a^(L+2):=by
    rw [pow_add]; change 100 ≤ a at h; have ht:1 ≤ a^L:= one_le_pow₀ hr; nlinarith only [hb,mul_le_mul_of_nonneg_left (show 8≤ a^2 by nlinarith only [h]) (show 0 ≤ a^L by positivity),ht]
 unfold Schema; simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fun,Fintype.card_fin,show Fintype.card Axis=4 from rfl]; change ((( ((2*b+1)^4)^2*2:ℕ)):ℝ) ≤ _; simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
 rw [←pow_mul]
 have hf:(2:ℝ)≤ a^4:=by change 100 ≤ a at h; linarith only [h,show a ≤ a^4 from (by simpa only [pow_one] using (pow_le_pow_right₀ hr (show 1 ≤ 4 by omega)))]
 exact (mul_le_mul (pow_le_pow_left₀ (by positivity) hy (4*2)) hf (by norm_num) (pow_nonneg (pow_nonneg (by linarith only [hr]) _) _)).trans_eq (show (a^(L+2))^(4*2)*a^4=a^(8*L+20) from (by rw [←pow_mul,←pow_add]; congr 1; omega))
#check @prognosis
#print axioms epochCount
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
