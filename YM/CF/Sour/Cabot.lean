import YM.CF.Sour.Cherry
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
namespace Elm
variable {d a v:ℝ}(P0:Elm N κ d a v)
-- utility convert old.E functions arbitrary.Finz. expo. real tape.Shape.N kernel actually at Guard.
def tape(i:κ)(x:Chin N):Op (Single N):= if h:x∈Openc (More N) d then ∑ X,P0.F X i ⟨_,h⟩ else 0
def into : Lawn N d P0.tape a v:=⟨P0.F,P0.W,P0.coat,P0.bank,fun i x=> dif_pos x.property⟩
variable {L:Scree.Loom N}{p:BudgetPoint}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)
lemma fire {V':κ→BeatL N}(u:NearL P0 V')(x:Orbit N)(i:κ):P0.tape i (roller h g x).val=V' i (roller h g x).val:=(P0.into.shape i _).trans (u _ _ _ (g.paid _) rfl).symm -- tune
lemma reelV {F0:κ→BeatL N}(f:NearL P0 F0)(i:κ)(x:Orbit N){K:Op (Single N)→FC (Dwell N)}{Z:Single N→Single N→ FC (Dwell N)}{H:ℝ}(T: Glyph K Z H): (∑ X:Aura N,P0.into.vik K g h p i X x)= K (F0 i (roller h g x).val):=(P0.into.reel T g h i x).trans (congrArg K (P0.fire g h f _ _))
end Elm
local notation "Lx"=> Firing N
namespace BondL
variable {a b c d e s:ℝ}{T S E}(A: BondL T S E b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
abbrev choir (i:κ):Bag N:= A.ela.into.vik (faceD true false) g h p i + A.elt.into.vik (faceD true false) g h p i + A.coreS.into.vik (fun A=> Matrix.trace A • (1:FC (LeanV (Single N)))) g h p i + (A.cosY false).into.vik (Sault.crib false) g h p i+ (A.cosY true).into.vik (Sault.crib true) g h p i+ A.heel.into.vik (Sault.urn (trailM false) (trailM true)) g h p i
abbrev bead (p:BudgetPoint) : Aura N→ℝ:= A.ela.into.nick W p + A.elt.into.nick W p+A.coreS.into.nick W p+(A.cosY false).into.nick W p+(A.cosY true).into.nick W p + A.heel.into.nick W p
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤ 5*p.B)(w:3≤p.B)
include w0 k hv y hx v w
lemma litB(i:κ): Bias (cipherK q) (A.choir (p:=p) g h i) p W (A.bead W p):=by
 exact (((((A.ela.into.turnX (pal_v W w0) g h k hv y hx v w i).plus (A.elt.into.turnX (pal_v W w0) g h k hv y hx v w i)).plus (A.coreS.into.turnX (oreV W w0 _) g h k hv y hx v w i)).plus ((A.cosY false).into.turnX (tail_k W w0) g h k hv y hx v w i)).plus ((A.cosY true).into.turnX (leg_k W w0) g h k hv y hx v w i)).plus (A.heel.into.turnX (less_k W w0) g h k hv y hx v w i)
omit k hv y hx v w
lemma Ω_P (i:κ)(x:Orbit N) : let R:Chin N:=(roller h g x).val; (∑ X:Aura N,A.choir (p:=p) g h i X x)=dma (T R) (S R) (κR N E i) (Dial.tickA N):=by
 intro R; unfold choir; simp only [Pi.add_apply,sum_add_distrib]; rw [A.ela.reelV g h A.Yh i x (pal_v W w0), A.elt.reelV g h A.Th i x (pal_v W w0),A.coreS.reelV g h A.Ch i x (oreV W w0 _),(A.cosY false).reelV g h (A.Hh false) i x (tail_k W w0),(A.cosY true).reelV g h (A.Hh true) i x (leg_k W w0),A.heel.reelV g h A.Hc i x (less_k W w0),dma] -- tune
 let B:=κR N E i; let D:=S R; let U:=fC N S E i R
 rw [show _=faceD true false U from (show faceD true false B+faceD true false (U-B)=_ from ?_ ),forkL]; swap
 · unfold faceD twinD; simp_rw [←sum_add_distrib,←add_smul,Matrix.sub_apply,add_sub_cancel]; -- tune
 change _+ Matrix.trace (Sault.tally (T R) (tickA N) U B) • (1:FC (LeanV (Single N)))+ Sault.crib false (T R*U)+Sault.crib true (U*(1-T R))+Sault.urn (trailM false) (trailM true) (T R*U*(1-T R)) = faceD true false U+ Sault.crib true (U*(1-T R))+ (Matrix.trace (Sault.tally (T R) (tickA N) U B) • 1+Sault.crib false (T R*U))+ Sault.urn (trailM false) (trailM true) (T R*U*(1-T R)); abel
omit w0
lemma duty (p:BudgetPoint)(m:ℝ)(ht:0 < a)(h:0 ≤ m)(k:2*m*Fief.tileN 1≤ a/2/2*p.B)(x:Seat N): Cadre.nook (A.bead W p*loom_v m 0 (widthK N p.B) 0) x≤ (p.order+1:ℝ)*W^2*aimV p.B a m*(5*b+c):=by
 unfold bead; simp only [add_mul,Cadre.nook,Pi.add_apply,sum_add_distrib]; let U:= (p.order+1:ℝ)*W^2*aimV p.B a m
 refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (A.ela.into.cents p W m ht h k x) (A.elt.into.cents p W m ht h k x)) (A.coreS.into.cents p W m ht h k x)) ((A.cosY false).into.cents p W m ht h k x)) ((A.cosY true).into.cents p W m ht h k x)) (A.heel.into.cents p W m ht h k x)).trans_eq ?_; change U*b+U*c+U*b+U*b+U*b+U*b= _; unfold U; ring
end BondL
end YM.CF.Sour
