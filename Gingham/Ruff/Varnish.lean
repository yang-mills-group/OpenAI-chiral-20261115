import Gingham.Ruff.Jadeite
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical

open Nacre

variable (d:Shape)(U: UNI SpinIdx)
/-- Action on operator values. -/
def rotary(X:FC (Single N)):=
 if detX d.s then theta (owl N d U) X
 else twist (quantU (owl N d U)) X
abbrev ditch (T:OP N) :=
 if detX d.s then -Matrix.trace T else 0
def tackfee (A M:OP N):ℂ := effect d (Matrix.trace A)+ ditch d M
lemma tack_add (A M B L:OP N):
 tackfee d (A+B) (M+L)=tackfee d A M+tackfee d B L:=by
 unfold tackfee effect ditch
 rw [Matrix.trace_add,Matrix.trace_add]
 split <;> abel
lemma PE_tack (A M:OP N):
 ‖tackfee d A M‖ ≤ parce A+parce M:=by
 unfold tackfee effect ditch
 split
 · apply (norm_add_le ..).trans
   rw [norm_neg,norm_neg]
   exact add_le_add (PE_trace _) (PE_trace _)
 rw [add_zero]
 exact (PE_trace _).trans (le_add_of_nonneg_right (PE_nonneg _))

/- Selected spin is for the action via inverse (prepU). -/
variable (j: JetS d.s false (detX d.s) U)
include j
lemma sta :
 twist (owl N d U) (swapX (detX d.s) (tickA N)) = tickA N :=by
 rw [touchP]
 have t:swapX (detX d.s) (cutM (Tset N))=twist (prepU d U inert N) (cutM (Tset N)):= (tickR d inert U j N).symm
 rw [t, recoil]


def ribbonSign (d:Shape)(X:FC (Single N)) :=
 if detX d.s then -X else X

lemma rotary_portico (A M:OP N):
    let B:=plinth d U A
    let L:=plinth d U M
    rotary d U (portico (tickA N) (Matrix.trace A) M)=
      ribbonSign d (portico (tickA N) (tackfee d B L) L):=by
   have t:=sta (N:=N) d U j
   have k(X:OP N): plinth d U X = twist (owl N d U) (if detX d.s then star X else X):=
     congrArg (twist (owl N d U)) (siphon_or _ _)
   dsimp only
   unfold tackfee effect ditch rotary ribbonSign
   rw [k A,k M,twistTr,twistTr]
   by_cases v:detX d.s=true
   · simp only [v,if_true,swapX,star_trace] at t ⊢
     rw [turn_portico (tickPin N),t,residuum]
     rw [neg_add]
   simp only [Bool.eq_false_iff.mpr v,Bool.false_eq_true,if_false,swapX,add_zero] at t ⊢
   rw [←wind_portico,t]
omit j in
lemma rotary_lag (z:Cover)(u:JetS 1 false (detX (1:Signed)) 1) (L:OP N) :
   twist (quantU (owl N (lagX z) 1)) (𝒿 (tickA N) L)=
      𝒿 (tickA N) (plinth (lagX z) 1 L):=by
   have v:detX (lagX z).s=false:=det_i
   have t:=sta (N:=N) (lagX z) 1 u
   simp only [v,swapX,Bool.false_eq_true,if_false] at t

   rw [←wind_𝒿,t]
   change _=𝒿 _ (twist _ (siphon _ _))
   rw [v,siphon_no]

