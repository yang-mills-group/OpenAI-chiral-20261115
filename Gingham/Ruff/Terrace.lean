import Gingham.Ruff.Varnish
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

variable {p:BudgetPoint}{u:Side}{r l:ℕ}{E a c e:ℝ}
    {U':Scree.Loom N}{f h:Chin N→OP N}
    (B:GarlandBook u a c e f h)(g:Briefly p r e U')
    (G:Tagbill a E u l r p.B)
    (d:Shape)(U:UNI SpinIdx)
    (T:Plumes f h a c e)(j:JetS d.s false (detX d.s) U)

abbrev lamprey(w:Cover)(i:Axis):= framed (lagX w) 1 (B.point i)

-- budget_m and budget_b:
abbrev standard:=framed d U B.pump
abbrev streamer(i:Axis)(w:Cover):=framed d U (B.lamprey w i)

abbrev tire(x:Orbit N):=coinF g B.pump true x
abbrev eye(i:Axis)(x:Orbit N):=coinF g (B.point i) true x
abbrev eyeAt(w:Cover)(i:Axis)(x:Orbit N):= coinF g (B.lamprey w i) true x
def ombre(x:Orbit N):=
 surplus u (fun i w=>B.eyeAt g w i x)
/-- Actual unscaled physical expression (128), on actual kernel lookup. -/
def brocade(x:Orbit N):=
 portico (tickA N) (Matrix.trace (B.tire g x)) (B.ombre g x)

lemma brocade_eq(x:Orbit N):
    B.brocade g x = (Matrix.trace (B.tire g x)) • 1 +
      ∑i:Axis, (𝒿 (tickA N) (B.eyeAt g (advancePlus u i) i x) -
               𝒿 (tickA N) (B.eyeAt g (advanceNeg u i) i x)):= by
    unfold brocade portico ombre surplus
    rw [𝒿_sum]; simp_rw [𝒿_sub]

include G
lemma shiften (w:Cover)(i:Axis)(x z:Orbit N)(t:z.1=Yg (lagX w) x.1):
    twist (quantU (owl N (lagX w) 1)) (𝒿 (tickA N) (B.eye g i z))
       = 𝒿 (tickA N) (B.eyeAt g w i x):=by
   rw [rotary_lag w (by rw [det_i]; exact calmSX)]
   rw [eyeAt,cologne _ _ g _ G x z t]
omit G

abbrev trim(β:Bool)(x:Orbit N):= coinF g (B.standard d U) β x
def fill(β:Bool)(x:Orbit N):=
 surplus u (fun i w=> coinF g (B.streamer d U i w) β x)
abbrev trussEnd(x:Orbit N):= farF g (B.standard d U) x
def fillEnd(x:Orbit N):=
 surplus u (fun i w=> farF g (B.streamer d U i w) x)
def thread(x:Orbit N):ℂ :=
  tackfee d (B.trim g d U true x) (B.fill g d U true x)
def pen(x:Orbit N):= portico (tickA N) (B.thread g d U x)
  (B.fill g d U true x)

/- d-posed, up to outer sign. -/
include G j
lemma ornate(x z: Orbit N)(t:z.1=Yg d x.1):
 rotary d U (B.brocade g z)= ribbonSign d (B.pen g d U x):=by
 have a:B.trim g d U true x= plinth d U (B.tire g z):=cologne d U g B.pump G x z t
 have b:B.fill g d U true x= plinth d U (B.ombre g z):=by
     unfold fill ombre
     rw [←surplus_map];exact congrArg (surplus u) (funext (fun i=>funext fun w=>
        cologne d U g (B.lamprey w i) G x z t))
 unfold brocade pen thread
 rw [a,b]
 exact rotary_portico d U j _ _

#print axioms ornate

