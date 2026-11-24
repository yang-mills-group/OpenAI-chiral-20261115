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
open Py.Rate.LocalLimit Py Py.Dyad
variable (P:Spine)(s w:ℕ)(o:Bool → Cover)(n₀:Bool)(z:ℝ)(A:ℕ)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
-- index payment.Positive roots both for simplicity. w≥ |nodeC*.Slide ticks.Endorse.Both.B trans.
abbrev withinT(o:Bool → Cover)(w:ℕ):Prop:=∀b:Bool,∀i:Axis,-(w:ℤ)≤ nodeC (o b) i∧ nodeC (o b) i≤ w
noncomputable abbrev cardD(s:ℕ):ℕ:=capacityS A (hat P.par.R.L P.par.x s)
local notation "I"=>Fin (cardD P A s)
noncomputable abbrev flightY (P:Spine) (w:ℕ)(i:ℕ):ℕ:=w+P.calibration.ℓ+24+i
local notation "Δ" i:max=> (flightY P w (i:ℕ))
noncomputable abbrev cabinY (P:Spine)(u:Cover)(w j:ℕ):Cover:= Calico.slid P.calibration 3 (flightY P w j) u
local notation "η" i:max b:max=> cabinY P (o b) w (i:I).val
local notation "h" u:max=> fellerT P s u
def testZ (P:Spine)(W:Bool)(f:Bool→P.Test):P.Test:= if W then f false*f true else f true
noncomputable abbrev bodyT(P:Spine)(s:ℕ)(o:Bool → Cover)(n₀:Bool):P.Test:= testZ P n₀ (fun b=>fellerT P s (o b))
noncomputable abbrev yacht(i:ℕ):P.Test:=bodyT P s (fun j=> cabinY P (o j) w i) n₀
noncomputable abbrev trialY :P.Test:= ∑ i:I, ((σ:ℝ):ℂ) • (yacht P s w o n₀ i.val-(z:ℂ) • (1:P.Test))
noncomputable abbrev spots:Finset Cover:= Finset.univ.biUnion fun i:I=> Finset.univ.biUnion fun b:Bool=> bands (η i b) 22
local notation "S₀"=>spots P s w o A
local notation "T₀"=>trialY P s w o n₀ z A
lemma transport (i:I):P.shifts 3 (Δ i.val) (bodyT P s o n₀) = yacht P s w o n₀ i.val:=by
 unfold yacht bodyT testZ; simp only; split; · rw [map_mul]; unfold fellerT; rw [map_smul,map_smul,wp_shift,wp_shift]
 unfold fellerT; rw [map_smul,wp_shift]
#check yacht
lemma zoned : T₀ ∈ bay K S₀ true :=by
 refine Subalgebra.sum_mem _ fun i _=> Subalgebra.smul_mem _ (Subalgebra.sub_mem _ ?_ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)) _
 have hv(b): h (η i b)∈bay K S₀ true:=by
    have e:h (η i b) ∈ bay K (bands (η i b) 22) true:= Subalgebra.smul_mem _ (lining_test ..) _
    exact tallerBay K _ true (fun c q=> mem_biUnion.mpr ⟨i, Finset.mem_univ _,mem_biUnion.mpr ⟨b,Finset.mem_univ _,q⟩⟩) e
 unfold yacht bodyT testZ; split; · exact Subalgebra.mul_mem _ (hv false) (hv true)
 exact hv _
lemma wished: T₀∈ enclave K:=by
 unfold trialY; refine Subalgebra.sum_mem _ fun i _=> Subalgebra.smul_mem _ (Subalgebra.sub_mem _ ?_ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)) _
 have hv(b): h (η i b)∈enclave K:=Subalgebra.smul_mem _ (color_wp P s _) _
 unfold yacht bodyT testZ; split; · exact Subalgebra.mul_mem _ (hv false) (hv true)
 exact hv _
noncomputable abbrev slip (P:Spine)(s w A:ℕ):ℕ:= (pollN P)* flightY P w (capacityS A (hat P.par.R.L P.par.x s))+w+24
lemma ticking(i k:Axis)(b:Bool)(u:ℕ):nodeC (cabinY P (o b) w u) i=nodeC (o b) i + if i=(3:Axis) then ((pollN P:ℕ):ℤ)*Δ u else 0:=by unfold cabinY; rw [bellV]; rfl
local notation "hS"=>slip P s w A
lemma higherZ (p:withinT o w):Tower.region 3 0 (K).ℓ (S₀)∧∀ y:Cover,y∈S₀→∀ j:Axis,-(hS:ℤ) ≤ y j ∧ y j ≤ hS:=by
 have hY(i:I):((pollN P:ℕ):ℤ)*Δ i.val ≤ (pollN P:ℕ) * (flightY P w (capacityS A (hat P.par.R.L P.par.x s)):ℤ):= by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity); exact_mod_cast Nat.add_le_add_left i.isLt.le _
 have hp:1 ≤ ((pollN P:ℕ):ℤ):= le_trans (by decide:(1:ℤ) ≤1) (Int.add_one_le_of_lt (ruler_gene _)) -- tune
 have he(y:Cover)(v:y∈S₀)(j:Axis):-(hS:ℤ) ≤ y j ∧ y j ≤ hS ∧ (j=3 →0+(K).ℓ≤ y j):=by
    obtain ⟨i,e,v⟩:=mem_biUnion.mp v; obtain ⟨b,t,l⟩:=mem_biUnion.mp v; obtain ⟨l,r⟩:= Calico.bands_spec _ l j; obtain ⟨h₁,h₂⟩:=p b j; rw [ticking P w o j j] at l r; split_ifs at l r with u -- neg branch tune
    · have hj:(Δ i.val:ℤ) ≤ ((pollN P:ℕ):ℤ)* (Δ i.val:ℤ):=le_mul_of_one_le_left (by positivity) hp
      have hb: (hS:ℤ)= (pollN P:ℕ)*(flightY P w (capacityS A (Yx)):ℤ)+w+24:=by unfold slip; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      specialize hY i; rw [hb]; simp only [flightY,Nat.cast_add] at *; omega
    have hb: (w:ℤ)+24 ≤ hS:=by unfold slip; exact_mod_cast (show w+24 ≤ pollN P*flightY P w (capacityS A (Yx))+w+24 from Nat.add_le_add_right (Nat.le_add_left ..) _)
    refine ⟨by omega,by omega,fun e=>(u e).elim⟩
 exact ⟨fun y p=>(he y p 3).2.2 rfl, fun y p j=> ⟨(he y p j).1,(he y p j).2.1⟩⟩
variable (x:P.Spectrum0 3)
lemma payroll (b:ℂ)(u:P.singleState 3 s x (bodyT P s o n₀)=b): P.singleState 3 s x (T₀)= (θ)^A • ((b:ℂ)-z):=by -- `(scaleY:ℝ) • Complex`, match cast. general b:ℂ
 unfold trialY; let f:=P.singleState 3 s x; have hi:f 1=1:=by unfold f; rw [P.single_state,P.reading_unit,map_one]
 have hv(i:I): P.singleState 3 s x (yacht P s w o n₀ i.val)=b:=by rw [←transport P s w o n₀ A i,P.slide_single,u]
 rw [map_sum]; have hk:P.singleState 3 s x 1=1:=hi; simp only [map_smul,map_sub,hv,hk,smul_eq_mul,mul_one]
 rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_assoc,←Complex.coe_smul]
 congr 1 -- casts product = ℝ
 push_cast; unfold cardD Gleam.Luster.Risa.sock; push_cast; field_simp [(show (((capacityS A (Yx)):ℕ):ℂ)≠0 from (by exact_mod_cast (Gleam.Luster.Risa.reaches A (Yx)).ne'))]
#print axioms zoned
#print axioms payroll
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
