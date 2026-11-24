import Anomaly.Second.Strike
import Anomaly.Second.Sail
import YM.SU5.Exchange.Stack.Nest
import YM.SU5.Exchange.Stack.Racket
import YM.SU5.Exchange.Visa.Guide
import YM.SU5.Exchange.Seed.Transit
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill
open Kennel
variable {C B L:Side}{X Y:SOp C}{o:Seat C}{a b c d v s t Nτ:ℝ}{n l q j:ℕ}{p:BudgetPoint}
variable {h:Odd L.val}{H:Pricing j L h (Thread j)}{e:ℝ}(P:Grasp H B e)
open Sault Leaf Vow.TreasuryFog
local notation "N"=> mid C B
variable (R:GramM (mid C B))(K:Scree.Loom (mid C B))
variable {k m:ℝ} {V:phy (mid C B)} (u:Roof (mid C B) k e q K) (z:P.roundZ≤ (mid C B).val)
local notation "⚑r"=> funde j R.J.M (mid C B)
local notation "⚑P"=> Moire.bloom R.J.P
local notation "Ω_N"=> (Dwell N)
open QuadClock
-- frame version (requirements pointwise only on no-ties). arbitrary supported;
-- even enqueued atop thresholding. `Y_s resp` phase old Mark included.
structure Vessel (F:Bag N)(V:phy N):Prop where
 rank (x:Orbit N)(t:Injective (priorP x.2)): rank2 (giveB F x)
 science (x:Orbit N)(p:Injective (priorP x.2))(h:IsStarProjection (spar j R.J.M (K x)))(v:Wave (Dwell N)):pilotH P R K x h (acts (giveB F x) v)=acts (V x) (pilotH P R K x h v)
open Oise
local notation "Pι" G:max F:max s:max=> color_b R R.beta (R.F+G) R.slip F (R.v+s)
lemma pilot_scalar (G:RegBudget N)(F':ForceBudget N)(x:Orbit N)(y:ℂ)(h:IsStarProjection (spar j R.J.M (K x)))(v:Wave (Dwell N)): pilotH P (Pι G F' y) K x h v= Complex.exp y • pilotH P R K x h (acts (exp (exponentL R.p G x.1)).val v):=by
 let R':=Pι G F' y; let X:=color_b R R.beta (R.F+G) R.slip F' R.v
 rw [← pilot_kindle P R K G F' x]; have he:R'.betaL K x=y+X.betaL K x:=by unfold R' X color_b GramM.betaL GramM.H0; dsimp only; abel
 -- tune simp
 change Complex.exp (R'.betaL K x) • _ = Complex.exp y • (Complex.exp (X.betaL K x) • (_:Phys N))
 rw [he, Complex.exp_add,mul_smul]
variable {F LQ:Bag (mid C B)}{AQ:Support (More (mid C B))}
lemma vessel_flow (t:Vessel P R K F V)(w:Barrage R.p q AQ m F (s+d+d) a b)(G:RegBudget N)(F':ForceBudget N)(y z:ℂ)(r:Sectoral R.p q LQ m (s+d) c)(i:Orbit N)(p':Injective (priorP i.2))(hy: giveB LQ i=y • (1:FC (Dwell N))+(exponentL R.p G i.1).val)(h:IsStarProjection (spar j R.J.M (K i)))(hu:0 ≤ s)(v:0 < d)(A:Wave (Dwell N)): pilotH P (Pι G F' z) K i h (acts (giveB (weaveOut F LQ) i) A)= acts (V i) (pilotH P (Pι G F' z) K i h A):=by
 rw [pilot_scalar P R K G F' i z h, pilot_scalar P R K G F' i z h, weave_formula w r hu v i _ y hy,←act_mul,attireExp _ _ (t.rank i p'),act_mul,map_smul,t.science i p'] -- tune grammar <,
end YM.CF.Swell
