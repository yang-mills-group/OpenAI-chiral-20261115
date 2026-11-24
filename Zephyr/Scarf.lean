import YM.CF.Milo.Cusp
import Zephyr.Glyph
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {N:Side} (T S:BeatL N)(E:χL N κ)
local notation "Sta"=> fC N S E
local notation "Bel"=> κR N E
local notation "Q"=> tickA N
local notation "Lx"=> Firing N
namespace BondL
variable {a b c d e s:ℝ}{T S E}(A: BondL T S E b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
variable (s_:Sweep N)(V:Orbit N)(i:κ)(Z:Aura N)(pF:Injective (priorP V.2))
open Levier Salt Ione
local notation "Λ"=> sauce s_.charge (detX s_.s) (γS s_)
local notation "OA"=> σX p Z ∅
local notation "WZ"=> yellA s_ V
local notation "Px"=> p.B
local notation "Sg"=> Support (More N)
local notation "Ut"=> (moldA s_ Z)
open Cadre Wray Larch Ione
variable {H p0:ℝ}{I: Aura N→ Support (More N)→ ℝ}(F:Vow.Cusp N)
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤5*p.B)(w:3≤p.B)
variable (f:∀ X:Aura N,∀ D⊆X.val,Fray p W (cipherK q) X D (F X D) (I X D))(r:Bake.Turf (fun X=>F X ∅))
variable (pS: ∀ s:Sweep N,∀ i:Aura N,∀ V:Orbit N,Injective (priorP V.2)→∀ D⊆i.val,F (moldA s i) (actY s D) (yellA s V)=suit_Y s (F i D V))
local notation "τx"=> A.bead W p
local notation "L'"=> (fun i:κ=> litB A g h W w0 k hv y hx v w i)
open Stax Glyph
local notation "Θi"=> (L' i)
local notation "B'"=> Λ
local notation "K'"=> Bias.payX Θi

open Zephyr
include w0 k hv y hx v w
variable (he:0 < a)(fα:2*(p.supportExponent+1)*Fief.tileN 1 ≤ a/2*p.B)(e': a ≤1)
include he fα e'
lemma raiseLine : IncX Utrue (lineH (p:=p) A g h i) (plusP p) W (cap2 (plusP p) b W a):=
  scopeRaised g h (pal_v W w0) A.ela i y hx v w k hv w0 (fun j=>(A.sQ j).1) (fun s x=>arm ..) A.ela.bank fα he e'

lemma raiseFloat : IncX Utrue (floatH (p:=p) A g h i) (plusP p) W (cap2 (plusP p) c W a):=
  scopeRaised g h (pal_v W w0) A.elt i y hx v w k hv w0 (fun j=>(A.sQ j).2.1) (fun s x=>arm ..) A.elt.bank fα he e'

lemma raiseScarf : IncX Utrue (scarf (p:=p) A g h i) (plusP p) W (cap2 (plusP p) b W a):=
  scopeRaised g h (oreV W w0 _) A.coreS i y hx v w k hv w0 (fun j=>(A.sQ j).2.2.1) (fun s x=>tiltH ..) A.coreS.bank fα he e'

end BondL
end YM.CF.Sour
