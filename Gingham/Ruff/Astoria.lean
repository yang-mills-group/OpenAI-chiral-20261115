import Gingham.Ruff.Recitative
import Gingham.Ruff.Purse
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

variable {n:ℕ}{e ρ b:ℝ} (H:Rialto n e ρ b)
    {S: Support (More N)}{w: Toll (Single N)}{F:Raw ↥(Openc (More N) e) (Single N)}
    (A:Suite (badge _) (bail N e) (bail N e) S w F)

def hum (H:Rialto n e ρ b)(F:Raw ↥(Openc (More N) e) (Single N))(x:Doub N):ℂ:=
 (F (pate H x)).trace

def blush (w:Toll (Single N)):ℝ:=∑i,w i i

include H A
lemma kelp (u : Seat N → SU.E)(x y:↥(Openc (More N) e))
    (p:y= (forum N e).drive u x):
  (F y).trace=(F x).trace:=by
  rw [p,A.frame.frame]
  rw [Matrix.trace_mul_comm, ←mul_assoc]
  rw [(bail N e |>.run u).property.1,one_mul]
lemma wiggle (u:SU.E) (x:Doub N)(s:ℝ)(h:‖s • x‖<1)(i:‖s • bothway u x‖<1):
 hum H F (s • bothway u x)=hum H F (s • x):=
   kelp H A (fun _=>u) _ _ (Subtype.ext (by
     dsimp only [pate,forum,affair]
     rw [dabble, if_pos i,dabble,if_pos h,overall_pencil,profile_g]))


lemma aria (x:Doub N)(h:‖x‖<1):
 Allows n (hum H F) x (blush w):=by
 have hx:= H.action F w A (Doub N) (pate H) x (dabble ρ) (fun _=>rfl)
    (H.good N x) (fun i _=>dabble_paid H x h i)
 suffices ∀ t : Finset (Single N), Allows n (fun v=>∑i∈t,F (pate H v) i i) x (∑i∈t,w i i)
      from this univ
 intro t
 induction t using Finset.induction_on with
 | empty=> simp only [sum_empty];exact allows_const x (by simp)
 | @insert i t u r=>simp_rw [sum_insert u];exact (hx i i).add r

lemma flat_aria (k:1≤n): fderiv ℝ (hum H F) 0=0:=
 off_key (hum H F)
    ((aria H A 0 (by simp)).smooth.differentiableAt (by exact_mod_cast (show n≠0 by omega))) (wiggle H A)

#print axioms flat_aria
