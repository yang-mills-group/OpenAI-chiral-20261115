import ZecaFired
import ZecaRose
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
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)

local notation "ξ"=> P.advocate 3 x j
local notation "EH"=>P.physicalEnergy j ξ
local notation "M"=> P.ColorHil j ξ
local notation "Ω"=> P.colorZero j ξ
local notation "Μ"=> timeMesh P.par
section cost
variable {G':Hilbert}
/-- Vacuum-centering map. -/
def leroy (a:G')(y:G'.Op): G'.Op →ₗ[ℂ] G'.Op where
 toFun z:=z-(inner ℂ a (z a)) • y
 map_add' z u:=by rw [add_apply,inner_add_right,add_smul]; abel
 map_smul' t z:=by change _=t • _; rw [smul_apply,inner_smul_right,smul_sub,smul_smul]
lemma leroy_pay (a:G')(y:G'.Op)(p:‖a‖=1)(h:‖y‖≤1)(z:G'.Op):
 ‖leroy a y z‖ ≤2*‖z‖:=by
 change ‖z - inner ℂ a (z a) • y‖≤_
 apply (norm_sub_le ..).trans
 rw [norm_smul,two_mul]; gcongr
 -- gcongr may leave
 exact (mul_le_of_le_one_right (norm_nonneg _) h).trans
     ((norm_inner_le_norm (𝕜:=ℂ) ..).trans (by rw [p,one_mul]; exact (z.le_opNorm _).trans_eq (by rw [p,mul_one])))
end cost

local notation "B"=>P.Fired j ξ
variable {w:ℕ}
lemma full_takes (a:ℝ≥0)(v₀:whenly Μ t w=a)(F:P.Test)(T:(P.ColorHil j (P.advocate 3 x j)).Op)
 (q:B t w (P.dewy F (P.singleState 3 t x F)) T):
 ∃ A,B t w F A∧leroy (G':=M) Ω ((EH).E a) A=T:=by
 let m:=P.singleState 3 t x F
 let A:= T+m • (EH).E a
 have p:= q.add ((Fired.identity q.pos).smul m)
 rw [v₀] at p
 have t':B t w F A:=by 
    change B t w (F-m • (1:P.Test) + m • (1:P.Test)) A at p
    rwa [sub_add_cancel] at p -- subst wrong replaces F in goal too?
 refine ⟨A,t',?_⟩
 change A-inner ℂ Ω (A Ω) • _= T
 rw [t'.scalar,P.single_agrees]
 exact add_sub_cancel_right T _

variable {C A:ℝ}{g:ℝ}{δ:ℕ→ℝ}{z:ℕ→ℕ}
variable (K:lender A C s r v δ g z P) (X:Cover)(O:Odessa j X s w P)(N₁:P.NightCop)
local notation "m" t:max=>P.gum w s t
local notation "Y" t:max=> P.clockPlate s t X
local notation "e" t:max=> P.visitOne t (P.clockPlate s t X)
local notation "ν"=>violet P.par s A
local notation "Z₁"=> (↑(zoomM P.par.R.L^(r-s)):ℂ)

include K O N₁
lemma fires_buy {T U:(P.ColorHil j (P.advocate 3 x j)).Op}
 (h:B r (m r) (P.centeredQ x r (Y r)) T)
 (i':B v (m v) (P.centeredQ x v (Y v)) U):
 ‖T‖ ≤4*(fareMin P.par.R.L (r-s)*ν) ∧
 ‖Z₁ • ((g:ℂ) • U-T)‖ ≤4*ν:=by
 let a:=whenly Μ r (m r)
 have ha:whenly Μ v (m v)=a:=by
   apply NNReal.eq
   exact ((show ((whenly Μ v (m v)):ℝ) = (P.gum w s v:ℝ)*P.macroStep v by
      rw [whenly, NNReal.coe_mul,NNReal.coe_natCast]; rfl).trans
      (P.gum_tick (K.treasury.price.le.trans K.treasury.step))).trans
      (by rw [←P.gum_tick K.treasury.price.le]; unfold a;rw [whenly, NNReal.coe_mul,NNReal.coe_natCast];rfl)

 obtain ⟨V,p₀,y₀⟩:= P.full_takes j x a rfl (e r) T h
 obtain ⟨V',p₁,y₁⟩:= P.full_takes j x a ha (e v) U i'
 let L₀:=leroy (G':=M) Ω ((EH).E a)
 have ht: ∀ {V:(M).Op} {d:ℝ},‖V‖≤ 2*d → ‖L₀ V‖≤4*d:= by
    intro J d h
    apply (leroy_pay (G':=M) Ω _ (P.norms_color ..) ((EH).shrinks a) _).trans
    linarith only [h]
 refine ⟨?_,?_⟩
 · rw [←y₀]; apply ht; apply p₀.mean_le
   intro f hi hv
   exact P.norm_odessa_floret j X K O N₁ f (congrArg (fun t:P.Test=> t.val) hv)
 have pu:=p₀.refine K.treasury.step
 rw [show P.par.R.L.val^(v-r)*P.gum w s r= _ from P.gum_step K.treasury.price.le K.treasury.step] at pu
 rw [←y₀,←y₁, ← map_smul, ← map_sub, ← map_smul]
 apply ht
 apply (((p₁.smul (g:ℂ)).sub pu).smul Z₁).mean_le
 intro f hi hf
 exact P.norm_odessa_gap j X K O N₁ f (congrArg (fun t:P.Test=> t.val) hf)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
