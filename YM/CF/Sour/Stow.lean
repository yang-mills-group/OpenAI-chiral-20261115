import YM.CF.Sour.Star
import YM.CF.Sour.Cabot
import YM.CF.Sour.Pie
import YM.CF.Sour.Wave
import YM.CF.Stax.Cast
import YM.CF.Sour.Maize
import YM.CF.Sour.Seal
import YM.CF.Exa.Water
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
-- clean Y reads NO tags, precision local; global operator kernel before saturation. Shift for any h exact on all.Price covariance.P_CORE Stamp Noninj permitted ∅.
variable (rP:p.threshold≤ t)(qX:q+10≤p.B)(P0:Aura N)(tP:V.1∈σX p P0 ∅)(wP:Z.val⊆P0.val)(Y:Ids N)
include tP wP rP qX g
lemma warp_v {K:ℝ}(F:Elm N κ d a K)(H:Op (Single N)→ FC (Dwell N)):F.into.vik H g h p i Z (V.1,Y)=F.into.vik H g h p i Z V:=by
 change (∑ j∈αW p.B _,Glyph.cure H g h _) (V.1,Y)=(∑ j∈αW p.B _,Glyph.cure H g h _) V; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j w; apply congrArg H; refine pact_p h g (F.coat _|>.1 i) (V.1,Y) V ?_; intro e p y; -- stamp
 have hv:halo (q+10) j⊆ P0.val := (Corona.halo_mono qX le_rfl).trans (((show Z.val=halo _ j from (mem_filter.mp w).2) ▸ wP)); exact (fern g rP j hv V.1 tP _ p rfl Y).trans (fern g rP j hv V.1 tP _ p rfl V.2).symm
lemma costF : A.choir (p:=p) g h i Z (V.1,Y)=A.choir (p:=p) g h i Z V:=by unfold choir; simp only [Pi.add_apply]; simp_rw [warp_v g h V i Z rP qX P0 tP wP Y]
omit tP wP rP qX
-- parameter continuity for any V (spin det profile.L Analytic). no norm needed iter
variable {H:Op (Single N)→FC (Dwell N)}{K:Single N→Single N→FC (Dwell N)}
lemma skyP {x:ℝ}(q:Glyph H K W)(T:Elm N κ d a x) : Continuous (fun i:κ=>T.into.vik H g h p i Z V):=by
 have hp:Continuous H:=by rw [funext q.whirl]; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; exact Continuous.smul (continuous_id.matrix_elem i j) continuous_const
 change Continuous (fun i:κ=> (∑ k∈αW p.B Z,Glyph.cure H g h (T.F k i)) V); simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ fun k _=>hp.comp ((T.coat k).2 _)
lemma skyE : Continuous (fun i:κ=> A.choir (p:=p) g h i Z V):=by unfold choir; simp only [Pi.add_apply]; exact (((((skyP g h 1 V Z (pal_v _ le_rfl) _).add (skyP g h 1 V Z (pal_v _ le_rfl) _)).add (skyP g h 1 V Z (oreV 1 le_rfl _) _)).add (skyP g h 1 V Z (tail_k _ le_rfl) _)).add (skyP g h 1 V Z (leg_k _ le_rfl) _)).add (skyP g h 1 V Z (less_k _ le_rfl) _) -- tune type
end BondL
end YM.CF.Sour
