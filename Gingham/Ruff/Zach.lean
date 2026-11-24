import Gingham.Ruff.Virelai
import Gingham.Ruff.Organza
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch Nacre
variable {n:ℕ}{e a c b ρ:ℝ}(X:Rialto n e ρ b)
 {f g:Chin N → OP N}{u:Side}(B:GarlandBook u a c e f g)
 (h:Plumes f g a c e)

lemma stir_flat (b:Bool)(d:Shape):
 stir (xtra b) d (1:Pane N)=1:=by
 funext z; unfold stir Lattice.pull; simp [Step.read]; --?

lemma pate_yem:
 dabble (N:=N) ρ 0=1:= by simp [dabble, pencil_flat ρ]

include X h
lemma pitchflat(u:Side):
  bust f u 0 (pate X 0).val = 0:=by
 have v:Guard (1:Pane N) e:=pate_yem ▸ X.good N 0
 let k:Axis:=0
 let d:= Scroll.Shape.mk (Signed.mirror k) 0
 have y:detX d.s=true:=det_t k
 have t:=signboard h 1 v u (0:Site N) d false _ (y.symm ▸ mirrorX k)
 have t0:finale d (0:Site N)=0:=by simp [finale,affine,d]
 simp only [y,if_true,t0,stir_flat] at t
 rw [show (pate X (N:=N) 0).val = Tulip.profile (1:Pane N) by dsimp only [pate]; rw [pate_yem]]
 linear_combination t/2 


lemma pitched_plain(u:Side):
 hum X (fun z=>yoke f u 0 z.val) 0=0:=pitchflat X h u

/-- For posed, including all uses. -/
lemma pitched (u:Side)(d:Shape)(U:UNI SpinIdx):
 hum X (baldaquin d U f u e) 0=0:=by
 let x:Dyed N e:= ⟨dabble ρ 0,X.good N 0,X.strict⟩
 change Matrix.trace (baldaquin _ _ _ _ e x.stack)=0
 rw [baldaquin, posed_stack]
 have p:(x.actsD d).stack.val=(pate X 0).val:=by
     change Tulip.profile (stir (xtra false) d (dabble (N:=N) ρ 0))=Tulip.profile (dabble ρ 0)
     rw [pate_yem,stir_flat]
 change Matrix.trace (twist _ (siphon _ _))=0
 rw [twistTr,siphon_or]
 split
 · rw [star_trace, p] -- star_trace orientation
   rw [←bust_yoke,pitchflat X h,star_zero]
 rw [p,←bust_yoke,pitchflat X h]

