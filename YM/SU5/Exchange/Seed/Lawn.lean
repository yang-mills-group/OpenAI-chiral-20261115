import YM.SU5.Exchange.Seed.Ticket
import SatinThinBeacon
import YM.SU5.Exchange.Seed.Ship
import YM.SU5.Exchange.Seed.Station
import SatinThinPoles
import YM.CF.Roots.Sort
import YM.SU5.Exchange.Seed.Zero
import YM.SU5.Exchange.Seed.Keys
import YM.SU5.Exchange.Seed.Marks
import YM.CF.Rive.New
import YM.CF.Song.Pads
import SatinThinTopic
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog
open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open Roots Py
open scoped YM.CF.Mew
variable {I:Type}[LinearOrder I][Fintype I] (σ:I→ Seat n)
variable (G:I→RegBudget n)(E:Key I→RegBudget n)(F:Key I→ForceBudget n)
variable (pE:∀ X:Scree.Hub n,Hush σ X.val.2 (fun z=> E z X)∧∀ i,River (fun z:Key I=> E z X i))
variable (pF:∀ X:Force n,Hush σ X.val.1.val.2 (fun z=> F z X)∧∀ i,River (fun z:Key I=> F z X i))
local notation "Qξ"=> trueSet σ
local notation "QW"=> manySet σ
local notation "ΘΩ"=> awake σ E G
local notation "ΘF"=> bustle σ F
variable (A:∀ i (X:Scree.Hub n), G i X≠0 → σ i ∈ X.val.2)
def graft_E (B:Key I→RegBudget n)(i:I) : RegBudget n:=fun x V=>tipI (fun z=> B z x V) [i]
lemma pointPine (i:Finset I):Differentiable ℂ (fun z:Key I=> Mew.pine i z):=by
 induction i using Finset.induction_on with
 | empty=> simp [Mew.pine]
 | insert i s t ih=> simp_rw [Mew.pine,prod_insert t]; exact (differentiable_apply _).mul ih
lemma horn(i:Finset I)(j:I)(w:ℂ)(t:1 < i.card) : Mew.pine i (Function.update (0:Key I) j w)=0:=by
 obtain ⟨x,g,y,h,l⟩:= one_lt_card.mp t
 have he(i:I)(t:i≠ j): update (0:Key I) j w i=0:= update_of_ne t ..
 by_cases p:x=j; · exact prod_eq_zero h (he _ (fun t=>l (p.trans t.symm)))
 exact prod_eq_zero g (he _ p)
lemma crest_E (i:I)(w:ℂ) : ΘΩ (Function.update (0:Key I) i w)=w • G i:=by
 unfold awake rim_C; rw [Finset.sum_eq_zero (fun x p=> ?_),add_zero] -- order
 · unfold core_C; rw [sum_eq_single i,Function.update_self]; intro j _ p; rw [Function.update_of_ne p]; exact zero_smul ..; simp
 rw [horn x i w (mem_filter.mp p).2.1,zero_smul]
lemma crest_K (i:I)(w:ℂ) : ΘF (Function.update (0:Key I) i w) = w • νΦK F {i}:=by
 unfold bustle; rw [sumOpen,Finset.sum_eq_zero (s:=QW) (fun x p=>?_),add_zero]; swap; · rw [horn x i w (mem_filter.mp p).2.1,zero_smul]
 simp_rw [Mew.pine,prod_singleton]; rw [sum_eq_single i,Function.update_self]; intro j _ p; rw [Function.update_of_ne p]; exact zero_smul ..; simp
lemma cash0 : ΘΩ 0=0 ∧ ΘF 0=0:=by
 constructor
 · unfold awake rim_C core_C; simp only [Pi.zero_apply,zero_smul, sum_const_zero]; rw [Finset.sum_eq_zero (s:=QW) (fun j p=>?_ ),zero_add]; rw [charm_D _ (by intro z; have hx:1 < j.card:= (mem_filter.mp p).2.1; simp only [z,card_empty,show ¬ 1 < 0 from by omega] at hx),zero_smul]
 unfold bustle; exact sum_eq_zero fun i v=> by rw [charm_D]; exact zero_smul ..; exact (mem_filter.mp v).2.1.ne_empty -- need unfold
lemma eReady (X:Scree.Hub n)(i:Pane n): Differentiable ℂ (fun z=> ΘΩ z X i):=by
 unfold awake rim_C core_C; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply]; exact (Differentiable.fun_sum (fun j _=> (show Differentiable ℂ (fun z:Key I=>z j) from differentiable_apply _).smul (differentiable_const _))).add (Differentiable.fun_sum (fun j _=>(pointPine j).smul (differentiable_const _)))
lemma fReady (X:Force n)(u:Orbit n): Differentiable ℂ (fun z=> ΘF z X u):=by
 unfold bustle; simp_rw [Finset.sum_apply, Pi.smul_apply]; exact Differentiable.fun_sum (fun i _=>(pointPine i).smul (differentiable_const _))
lemma value_E (i:I) : graft_E ΘΩ i=G i:=by
 funext X U; change cutI (fun z=> ΘΩ z X U) i 0=_
 rw [← (mitt (river_all _ (eReady σ G E X U)) roots i).deriv]; simp_rw [crest_E]; exact (show deriv (fun z:ℂ=>z • ((G i) X U)) 0= G i X U from by simpa using ((hasDerivAt_id' (0:ℂ)).smul_const (G i X U)).deriv)
lemma value_F (i:I) : emberTip ΘF i=νΦK F {i}:=by
 funext X U; change cutI (fun z=> ΘF z X U) i 0=_
 rw [←(mitt (river_all _ (fReady σ F X U)) roots i).deriv]; simp_rw [crest_K]; exact (show deriv (fun z:ℂ=>z • (νΦK F {i} X U)) 0= _ from by simpa using ((hasDerivAt_id' (0:ℂ)).smul_const (νΦK F {i} X U)).deriv)
include A pE
lemma quietE (X:Scree.Hub n) : Quiet σ X.val.2 fun z=> ΘΩ z X:=by
 intro z w k; unfold awake core_C rim_C; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply]; refine congrArg₂ (·+·) (Finset.sum_congr rfl fun i _=> ?_) (Finset.sum_congr rfl fun i v=>?_)
 · by_cases u:G i X=0; · rw [u,smul_zero,smul_zero]
   rw [k i (A i X u)]
 by_cases q:νΦX E i X=0; · rw [q,smul_zero,smul_zero];
 refine congrArg (· • νΦX E i X) (Finset.prod_congr rfl (fun j u=> k j ?_))
 by_contra t; apply q; funext i'; exact Neon.husht_B σ X.val.2 _ (fun a e b c v=> congrFun ((pE X).1 a e b c v) i') ((pE X).2 i') _ j t (by simpa [Mew.Cue] using u) -- order tune
omit A pE
include pF
lemma quietF(X:Force n): Quiet σ X.val.1.val.2 fun z=> ΘF z X:=by
 intro z w k; unfold bustle; simp_rw [Finset.sum_apply,Pi.smul_apply]; refine Finset.sum_congr rfl fun i v=>?_
 by_cases q:νΦK F i X=0; · rw [q,smul_zero,smul_zero]
 refine congrArg (· • νΦK F i X) (Finset.prod_congr rfl (fun j u=> k j ?_))
 by_contra t; apply q; funext i'; exact Neon.husht_B σ X.val.1.val.2 _ (fun a e b c v=> congrFun ((pF X).1 a e b c v) i') ((pF X).2 i') _ j t (by simpa [Mew.Cue] using u)
end TreasuryFog
end YM.CF.Vow
