import YM.SU5.Exchange.Seed.Trim
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
open Mew Cadre Ione Rive Py Neon Roots Oise Larch Wray Salt Bake
open scoped YM.CF.Mew
variable {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n)

-- public programs:
-- t≠1− multi, only distinct poses. j per label.
-- shape solution E₁ i independent of keys and of spectator arrangement.
def core_C (E:I→RegBudget n) (z:Key I): RegBudget n:=∑ i,z i • E i
def rim_C (E:Key I→RegBudget n)(z:Key I): RegBudget n:=∑ i∈manySet σ, pine i z • νΦX E i
-- incoming raw K(0) needn't be Gram before adding increments

def awake (E:Key I→RegBudget n)(G:I→RegBudget n)(z:Key I):RegBudget n:= core_C G z+rim_C σ E z

def bustle (F:Key I→ForceBudget n)(z:Key I) : ForceBudget n:=∑ j∈trueSet σ, pine j z • νΦK F j

variable (E:Key I→RegBudget n)(G:I→RegBudget n)(F:Key I→ForceBudget n)
variable (q0:E 0=0)
variable (pE:∀ i x, River fun z=> E z i x)(pF:∀ i x,River fun z=> F z i x)(β0:∀ i U, exponentL P (G i) U= exponentL P (νΦX E {i}) U) -- update budgets. Expect ∀ lit? exponentL already masks

abbrev circE (U:Pane n)(x:Key I→RegBudget n)(z:Key I):=Scree.exponentL P (x z) U
abbrev circF (U:Orbit n)(x:Key I→ForceBudget n)(z:Key I):=fueled P (x z) U

lemma aloneSet (i:Finset I)(u:i∈trueSet σ)(l:¬ 1 < i.card): ∃ j:I,i={j}:=by
 apply Finset.card_eq_one.mp
 have hv:= Finset.card_pos.mpr (mem_filter.mp u).2.1; omega

lemma sumOpen {M₀:Type*}[AddCommMonoid M₀](f:Finset I→M₀):
 (∑ j∈trueSet σ,f j)=(∑ i:I,f {i})+∑ j∈manySet σ,f j :=by
 let A:=trueSet σ; let B:=manySet σ; have h:B ⊆ A:= fun i u=> mem_filter.mpr ⟨mem_univ _, card_pos.mp ((by exact lt_trans zero_lt_one (mem_filter.mp u).2.1)),(mem_filter.mp u).2.2⟩
 let q:I↪Finset I:= ⟨fun i=>{i},singleton_injective⟩; have ht:A \ B= univ.map q:=by
    ext i; constructor
    · intro v; obtain ⟨k,t⟩:= mem_sdiff.mp v; obtain ⟨j,rfl⟩:=aloneSet σ i k (fun p=>t (mem_filter.mpr ⟨mem_univ _,p,(mem_filter.mp k).2.2⟩)); exact mem_map.mpr ⟨_,mem_univ j,rfl⟩
    intro p; obtain ⟨x,v,rfl⟩:=mem_map.mp p; unfold A B; simp [q,manySet,trueSet]
 change ∑ j∈A,_= _ + ∑ j∈B,f j; rw [←sum_sdiff h,ht,sum_map]; rfl

lemma costF {U:Orbit n}(z:Key I)(i:Force n): bustle σ F z i U= molten σ (fun z=> F z i U) z:=by unfold bustle molten; simp_rw [Finset.sum_apply,Pi.smul_apply]
lemma costE(i:Scree.Hub n)(x: Pane n)(z:Key I):
 (core_C (fun i:I=> νΦX E {i}) z+ rim_C σ E z) i x=molten σ (fun z=>E z i x) z:=by
 rw [molten,sumOpen]; unfold core_C rim_C νΦX; simp [Pi.add_apply,Mew.pine, Finset.sum_apply] -- tune

lemma exp_gain {i:Pane n} (F G:RegBudget n) (c:ℂ): exponentL P (c • F) i= c • exponentL P F i∧ exponentL P (F+G) i=exponentL P F i+exponentL P G i:=by
 constructor <;> unfold exponentL
 · rw [smul_sum]; apply sum_congr rfl; intro j p; unfold numbE; by_cases v:pingS P.threshold j.val.2 i; rw [Set.indicator_of_mem v,Set.indicator_of_mem v]; rfl; rw [Set.indicator_of_notMem v,Set.indicator_of_notMem v,smul_zero] -- v types tune
 exact ripe_H P ((i, Classical.arbitrary _):Orbit n) F G
lemma exp_port {i:Pane n}(S:Finset I) (G:I→RegBudget n): exponentL P (∑ j∈ S,G j) i=∑ j∈ S, exponentL P (G j) i:=by
 induction S using Finset.induction_on with
 | empty=> simp [exponentL,numbE]
 | insert j s u ih=> rw [sum_insert u,(exp_gain (i:=i) _ _ (0:ℂ)).2, ih,sum_insert u]

variable (l:List I)(p:ψS σ l)
include q0 β0 pE p
lemma castEra (U:Pane n): Soft l (circE (P:=P) U E) (circE (P:=P) U (awake σ E G)):=by
 let G'(i:I):= νΦX E {i}; have he(v:Key I):circE (P:=P) U (awake σ E G) v=circE (P:=P) U (awake σ E G') v:=by
    unfold circE awake; rw [(exp_gain (i:=U) _ _ 0).2,(exp_gain (i:=U) (core_C G' v) _ 0).2]; unfold core_C; rw [exp_port,exp_port]
    refine congrArg (· + _) (sum_congr rfl fun i w=> ?_); rw [(exp_gain (i:=U) (G i) (G' i) _).1,(exp_gain (i:=U) (G' i) (G i) _).1,β0]
 rw [funext he]; unfold circE exponentL; apply Soft.sum' univ; intro X _
 by_cases hx:pingS P.threshold X.val.2 U; swap; · unfold numbE; simp_rw [Set.indicator_of_notMem (show U∉ {U:Pane n|pingS P.threshold X.val.2 U} from hx)]; exact Soft.same_t ..
 unfold awake G' numbE; simp_rw [Set.indicator_of_mem (show U∈ {U:Pane n|pingS P.threshold X.val.2 U} from hx),costE σ E];
 let W:= softMolten σ (fun z=> E z X U) (pE ..) l p; simp only [q0,Pi.zero_apply,zero_add] at W; exact W
omit q0 β0 pE
include pF
lemma castFuel (A:ForceBudget n)(U:Orbit n): Soft l (circF (P:=P) U (fun z=> A+(F z-F 0))) (circF (P:=P) U (fun z=> A+bustle σ F z)):=by
 let f(z:Key I):=A + (F z-F 0); let g(z):= A + bustle σ F z
 have hG (i:Force n):Soft l (fun z=>f z i U) (fun z=> g z i U):=by
    let v:=(Soft.same_t l (A i U - F 0 i U)).plus (softMolten σ (fun z=> F z i U) (pF ..) l p); refine ?_
    unfold g; simp only [Pi.add_apply]; simp_rw [costF σ F];
    let x:Key I→ Cipher n:= fun z=> F z i U
    rw [show (fun z=> f z i U)= _ from funext (fun z=> show f z i U= A i U-F 0 i U +F z i U from by unfold f; simp only [Pi.add_apply,Pi.sub_apply]; abel)];
    have he(z:Key I): A i U + molten σ x z=A i U-F 0 i U+(x 0+molten σ x z):=by unfold x; abel
    rw [show (fun z=> _)=_ from (funext he)]; exact v
 unfold circF fueled; refine Soft.sum' univ fun j v=>?_ ; split; swap; exact Soft.same_t ..
 refine Soft.gain j (fun i z=>clamp P i (f z i) U) (fun i z=>clamp P i (g z i) U) ?_ (uS_b σ p)
 intro i w; unfold clamp; split; exact hG i; exact Soft.same_t ..
end TreasuryFog
end YM.CF.Vow
