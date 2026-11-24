import YM.CF.Sour.Print
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
lemma Bias.plus {H V:Bag n}{T E: Aura n→ ℝ}{h:ℝ}{δ:ℕ}(b:Bias δ H P h T)(p: Bias δ V P h E):Bias δ (H+V) P h (T+E):=by
 refine ⟨fun i x=> Sector.add (b.valid ..) (p.valid ..),add_nonneg b.weight p.weight, fun X Y D v w k=> ?_⟩; let J' (x:Bool):= if x then H Y else V Y; let K(x:Bool):=if x then T Y else E Y
 have ht(i:Bool): Marque P X Y D (J' i) h (K i):=by cases i; exact p.scope _ _ _ v w k; exact b.scope _ _ _ v w k
 have hp:=Marque.tiltR h univ J' K fun i _=> ht i; simp only [Fintype.sum_bool,J',K,ite_true,Bool.false_eq_true,ite_false] at hp; exact hp -- expect false true
local notation "Lx"=> Firing N
namespace LedgerS
variable {a b c d e s:ℝ}{T S E}(A: LedgerS T S E a b c d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
abbrev choir (i:κ):Bag N:= A.openX.vik (faceD true false) g h p i + A.tint.vik (faceD true false) g h p i + A.art.vik (fun A=> Matrix.trace A • (1:FC (LeanV (Single N)))) g h p i + A.hi.vik (Sault.crib false) g h p i+ A.lo.vik (Sault.crib true) g h p i+ A.cav.vik (Sault.urn (trailM false) (trailM true)) g h p i
abbrev bead (p:BudgetPoint) : Aura N→ℝ:= A.openX.nick W p + A.tint.nick W p+A.art.nick W p+A.hi.nick W p+A.lo.nick W p + A.cav.nick W p
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤ 5*p.B)(w:3≤p.B)
include w0 k hv y hx v w
lemma litB(i:κ): Bias (cipherK q) (A.choir (p:=p) g h i) p W (A.bead W p):=by
 exact (((((A.openX.turnX (pal_v W w0) g h k hv y hx v w i).plus (A.tint.turnX (pal_v W w0) g h k hv y hx v w i)).plus (A.art.turnX (oreV W w0 _) g h k hv y hx v w i)).plus (A.hi.turnX (tail_k W w0) g h k hv y hx v w i)).plus (A.lo.turnX (leg_k W w0) g h k hv y hx v w i)).plus (A.cav.turnX (less_k W w0) g h k hv y hx v w i)
omit k hv y hx v w
lemma Ω_P (i:κ)(x:Orbit N) : let R:Chin N:=(roller h g x).val; (∑ X:Aura N,A.choir (p:=p) g h i X x)=dma (T R) (S R) (κR N E i) (Dial.tickA N):=by
 intro R; unfold choir; simp only [Pi.add_apply,sum_add_distrib]; rw [A.openX.reel (pal_v W w0) g h, A.tint.reel (pal_v W w0) g h,A.art.reel (oreV W w0 _) g h,A.hi.reel (tail_k W w0) g h,A.lo.reel (leg_k W w0) g h,A.cav.reel (less_k W w0) g h,dma] -- tune
 let B:=κR N E i; let D:=S R; let U:=fC N S E i R
 rw [show _=faceD true false U from (show faceD true false B+faceD true false (U-B)=_ from ?_ ),forkL]; swap
 · unfold faceD twinD; simp_rw [←sum_add_distrib,←add_smul,Matrix.sub_apply,add_sub_cancel]; -- tune
 abel
omit w0
lemma duty (p:BudgetPoint)(m:ℝ)(ht:0 < a)(h:0 ≤ m)(k:2*m*Fief.tileN 1≤ a/2/2*p.B)(x:Seat N): Cadre.nook (A.bead W p*loom_v m 0 (widthK N p.B) 0) x≤ (p.order+1:ℝ)*W^2*aimV p.B a m*(5*b+c):=by
 unfold bead; simp only [add_mul,Cadre.nook,Pi.add_apply,sum_add_distrib]; let U:= (p.order+1:ℝ)*W^2*aimV p.B a m
 refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (A.openX.cents p W m ht h k x) (A.tint.cents p W m ht h k x)) (A.art.cents p W m ht h k x)) (A.hi.cents p W m ht h k x)) (A.lo.cents p W m ht h k x)) (A.cav.cents p W m ht h k x)).trans_eq ?_; change U*b+U*c+U*b+U*b+U*b+U*b= _; unfold U; ring
end LedgerS
end YM.CF.Sour
