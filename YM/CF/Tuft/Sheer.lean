import YM.CF.Ione.Pose
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
variable {I:Type*}[DecidableEq I]
def grab_A{N:Type*}[LinearOrder N][Fintype N]: (Dough N)→+ (Dough N) where
 toFun:=wage_Q 2
 map_zero':=up_r _ fun _ _=>rfl
 map_add':=plus_Y 2
abbrev MonQ (U:Copy n): Prop:=∀ V,wage_Q 2 (U V)=U V
lemma arise_C{F G:InkD n}{X:Hz}(i:Hz): True:=True.intro -- tune
lemma type_c {H:I → Copy n}(X:Finset I)(x:∀ i∈ X,MonQ (H i)): MonQ (∑ i∈X,H i):=by intro i; change grab_A _=_; rw [Finset.sum_apply,map_sum]; exact sum_congr rfl fun j p=>x j p i
lemma crux_T {H:Copy n}(u:MonQ H)(X:Aura n)(i:Support (More n)):MonQ (Vow.flick X H i):=by unfold Vow.flick; split; exact u; exact fun _=> (map_zero (grab_A (N:=Dwell n)))
lemma aura_T(W:Finset I)(U:I→Aura n)(V Y:I→Aura n)(F:I→ Copy n)(p:∀ i∈W, MonQ (F i)): Mono_W (soot_T W U V Y F):=by
 intro i D h t; unfold soot_T; rw [Finset.sum_apply,Finset.sum_apply]; apply type_c; intro j v
 unfold stroke chasmR; by_cases l:i=Y j
 · subst_vars -- can't subst i maybe
   rw [Pi.single_eq_same]; intro V'; change grab_A (N:=Dwell n) ((Vow.flick (U j) (F j) D) V'-(Vow.flick (V j) (F j) D) V')=_; rw [map_sub,show grab_A _= _ from crux_T (p j v) (U j) D V',show grab_A _= _ from crux_T (p j v) (V j) D V']; rfl
 rw [Pi.single_eq_of_ne l]; exact fun _=> map_zero (grab_A (N:=Dwell n))
lemma dead_Q {N:Type*}[LinearOrder N][Fintype N](H:Dough N){Q: Dough N}(h:wage_Q 2 Q=Q): deadP (H-Q)=deadP H:=by
 unfold deadP; rw [show wage_Q 2 (H-Q)=grab_A (H-Q) from rfl,map_sub,show grab_A Q=Q from h]; change H-Q-(_-Q)=_; abel
lemma darn_K (F:I→Cipher n)(X: Finset I):deadP (∑ i∈X,F i)=∑ i∈X,deadP (F i):=by unfold deadP; rw [show wage_Q 2 _=grab_A _ from rfl,map_sum,sum_sub_distrib]; rfl
lemma mint_p (F G:RegBudget n)(p:Sym_P (numbD F))(v:∀ (i:Hz) (V:Pane n), wage_Q 2 (G i V)= G i V):Sym_P (numbD (F+G)):=by
 suffices hx:numbD (F+G)=numbD F by rw [hx]; exact p
 apply funext; intro i; apply funext; intro V; change _=F i V- _; change F i V+ G i V-wage_Q 2 (_+_)=_; rw [plus_Y,v]; abel
end YM.CF.Ione
