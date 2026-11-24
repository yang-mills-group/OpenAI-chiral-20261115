import YM.SU5.Assay.Wipe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
local notation "β"=>P.rawBase j x
local notation "τ"=>P.tock
local notation "Ϝ"=>P.engineAxle j x
local notation "ϱ"=>P.respool j x
/-! Changing the stamp (and optional repricing) within a level -/

variable {P j}{a b w:ℝ}{D D':P.Apron}{z:ℂ}
lemma rawBase_shares (p:D'.s=D.s)(e:D'.F=z•D.F)
 (q₁:D.realWidth P j≤a)(q₂:D.realWidth P j≤b)(r₁:D'.realWidth P j≤a)(r₂:D'.realWidth P j≤b):β D' a b=z•β D a b:=by
 have u:τ D.s (D.u j)≤a:=q₁;have g:τ D.s (D.u j)≤b:=q₂
 have l:τ D'.s (D'.u j)≤a:=r₁;have r:τ D'.s (D'.u j)≤b:=r₂
 rw [p] at l r
 rcases le_total (D.u j) (D'.u j) with h|h
 · rw [←engineAxle_widen x _ p le_rfl l r,←engineAxle_widen x _ (D:=D) rfl h l r,e]
   exact engineAxle_smul x _ (Focused.widen x h) ..
 rw [←engineAxle_widen x _ p h u g,←engineAxle_widen x _ (D:=D) rfl le_rfl u g,e]
 exact engineAxle_smul x _ (Focused.widen x (D:=D) le_rfl) ..
lemma rawBase_replica (p:D'.s=D.s)(e:D'.F=D.F)
 (q₁:D.realWidth P j≤a)(q₂:D.realWidth P j≤b)(r₁:D'.realWidth P j≤a)(r₂:D'.realWidth P j≤b):β D' a b=β D a b:=by
 simpa using rawBase_shares x (z:=1) p (by rw [e,one_smul]) q₁ q₂ r₁ r₂

variable {x}{T:P.RawLag j x}{L:P.LagOp j x}{Q Q':ℕ→P.Apron}{g:ℕ→P.VMark}{r:Vantage}
lemma RawNormal.scale (h:P.RawNormal j x Q g r T)(u:P.Fades Q')(v:∀i,(Q' i).s=(Q i).s)(t:∀i,(Q' i).F=z•(Q i).F):
  P.RawNormal j x Q' g r (z•T):=by
 refine ⟨u,h.shift,fun a e b k=>((h.showAt _ e _ k).const_smul z).congr' ?_⟩
 filter_upwards [h.fades.one e j,h.fades.one k j,u.one e j,u.one k j] with i k₁ k₂ k₃ k₄
 unfold align; rw [rawBase_shares x (v i) (t i) k₁.le k₂.le k₃.le k₄.le,P.charter_smul]
lemma RawNormal.changeStamp (h:P.RawNormal j x Q g r T)(u:P.Fades Q')(v:∀i,(Q' i).s=(Q i).s)(t:∀i,(Q' i).F=(Q i).F):
 P.RawNormal j x Q' g r T:=by simpa using h.scale (z:=1) u v (fun i=>by rw [t,one_smul])

variable (P j x)
lemma respool_scale (p:Vantage)(T:P.RawLag j x)(z:ℂ):ϱ p (z•T)=z• ϱ p T:=by
 funext a b;unfold respool
 simp only [Pi.smul_apply,P.reprise_smul,P.locate_smul]
lemma rawOther_scale (T:P.RawLag j x)(z:ℂ):P.rawOther j x (z•T)=star z•P.rawOther j x T:=by
 funext a b;unfold rawOther; rw [Pi.smul_apply,Pi.smul_apply,star_smul]; rfl
lemma otherLag_scale (T:P.LagOp j x)(z:ℂ):P.otherLag j x (z•T)=star z•P.otherLag j x T:=by
 funext a b;unfold otherLag; rw [Pi.smul_apply,Pi.smul_apply,star_smul]; rfl
lemma slot_scale (T:P.LagOp j x)(a b:ℝ)(y:Vantage)(z:ℂ):P.slot j x (z•T) a b y=z• P.slot j x T a b y:=by
 unfold slot flown;rw [Pi.smul_apply,Pi.smul_apply,P.locate_smul]
variable {P j x}
lemma _root_.YM.OS.Semigroup.Credits.smul {H':Hilbert}{S':OS.Semigroup H' j}{A:ℝ→ℝ→H'.Op}(p:S'.Credits w A)(z:ℂ):S'.Credits w (z•A):=by
 intro a b c d v t m n
 simp only [Pi.smul_apply,p v t m n,sand_smul]
lemma coffee_scale {F:SampleDose}(p:(S).Credits w L)(h:Walled j F a b w)(z:ℂ):
 P.coffee j x (z•L) a b F=z•P.coffee j x L a b F:=by
 ext1 y
 rw [ContinuousLinearMap.smul_apply,(h.brew (p.smul z)).drink,(h.brew p).drink,←integral_smul]
 simp_rw [P.slot_scale,ContinuousLinearMap.smul_apply,smul_comm _ z]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
