import Gingham.Ruff.Lint

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


namespace GarlandBook

variable {m Z u L:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e a c E:ℝ}
    (P:Grasp Y Z e) (R:GramM (mid m Z)) {A:Loom (mid m Z)} {r l:ℕ}
    (B:GarlandBook u a c e (prince j R) (princeps R))
    (g:Briefly R.p r e A)(G:Tagbill a E u l r R.p.B)
    (D:Diadem R j a c e)(h:P.roundZ ≤ (mid m Z).val)
    (d:Shape)(U:UNI SpinIdx)(i:JetS d.s false (detX d.s) U)
    (x:Orbit (mid m Z))

/-- Exact raw aperture acting on actual regulator. -/
def answer :=
 flightKet P R A x
     (shockBoard R x (hitch (spar j R.J.M (A x)) (hitchAt (mid m Z) u d)))
      - acts (B.alarm g d U x) (denZ R P A x)
      - acts (B.quarry g d U x) (denZ R P A x)

include D i h
lemma vaulted:
    acts (B.villa g d U x) (denZ R P A x)=
     B.answer P R g d U x:=by
 unfold answer
 rw [B.villa_split g d U D i, (plume_den R j _).1, (plume_den R j _).2,
    act_sub, act_sub]
 rw [show acts (𝒵 _ _ _) (denZ R P A x)=_ from
     birdcall P R A x h (g.dye x).live (hitchAt (mid m Z) u d)]

lemma inlaid {X:FC (Single (mid m Z))}
    (q:Commute (B.pen g d U x) X)(t:Commute (B.villa g d U x) X) :
    beamZ _ (acts (X * B.pen g d U x) (denZ R P A x))=
    beamZ _ (acts X (B.answer P R g d U x)):=by
   rw [←B.vaulted P R g D h d U i,←q.eq, act_mul, ←act_mul X,
       ←t.eq, act_mul]
   exact B.cavity g d U x _

#print axioms inlaid

