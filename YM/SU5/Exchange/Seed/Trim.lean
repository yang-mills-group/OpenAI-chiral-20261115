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
-- uses any marked seats (Axon will require exactly own anchored)
variable {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n)
structure Soft {A:Type}[NormedAddCommGroup A][NormedSpace ℂ A][CompleteSpace A](Z:List I)(x y:Key I→ A):Prop where
   leftR:River x
   rightR: River y
   tip (l:List I)(p:l.Sublist Z): tipI x l=tipI y l
-- put h.Two sets. l.Ph.Pad.
variable (E:Key I→ RegBudget n)(F:Key I→ForceBudget n)(U:Orbit n)
local notation "CΞ"=> Cipher n
abbrev trueSet : Finset (Finset I):=univ.filter fun j=>j.Nonempty∧ Set.InjOn σ (j:Set I)
abbrev manySet: Finset (Finset I):= univ.filter fun j=>1 < j.card∧ Set.InjOn σ (j:Set I)

lemma fibres_N (l:List I)(p:ψS σ l): Set.InjOn σ (l.toFinset:Set I):=by
 exact pays_z σ p
variable {M₀:Type*}[NormedAddCommGroup M₀][NormedSpace ℂ M₀][CompleteSpace M₀]
def molten (X:Key I→ M₀)(z:Key I):= ∑ j∈trueSet σ,Mew.pine j z • gemI X j
lemma moltenFlow (f:Key I→ M₀) : Differentiable ℂ (molten σ f):=by
 apply Differentiable.fun_sum; intro U v; refine Differentiable.smul (show Differentiable ℂ (fun z:Mew.Key I=> Mew.pine U z) from ?_) (differentiable_const _)
 clear v; induction U using Finset.induction_on with
   |empty=> simp [Mew.pine]
   |insert i U t ih=> simp_rw [Mew.pine,prod_insert t]; exact (differentiable_apply _).mul ih
lemma moltenR (f:Key I→ M₀):River (molten σ f):= (tip_bank _ (fun i z=> Mew.pine i z • gemI f i) (fun i _=> lift_b i _)).1
lemma molten_p (x:Key I→M₀)(u:River x)(Z:List I)(v:ψS σ Z): tipI (molten σ x) Z= if Z=[] then 0 else tipI x Z:=by
 have b:=uS_b σ v; let A:=trueSet σ; let F(i:Finset I)(z:Key I):= pine i z • gemI x i
 rw [show tipI (molten σ x) _=∑ i∈A,tipI (F i) Z from (tip_bank _ F (fun i _=>lift_b _ _)).2 _]
 simp_rw [F,tip_tape _ b]; split
 next e=> apply sum_eq_zero; intro i v; apply if_neg; intro p; rw [←p,e] at v; exact Finset.not_nonempty_empty (mem_filter.mp v).2.1
 next w=> rw [sum_eq_single_of_mem Z.toFinset ?_,if_pos rfl, orbit_ζ u b]
          · intro a v p; exact if_neg (Ne.symm p)
          apply mem_filter.mpr; exact ⟨mem_univ _, (by cases Z <;> simp_all), fibres_N σ Z v⟩
lemma softMolten {A:Type}[NormedAddCommGroup A][NormedSpace ℂ A][CompleteSpace A](x:Key I→ A)(p:River x)(Z:List I)(h:ψS σ Z) : Soft Z x (fun z=> x 0 + molten σ x z):=by
 refine ⟨p,dub_V (zeroR _) (moltenR _ _),fun l b=>?_⟩; rw [tip_A (zeroR _) (moltenR _ _),molten_p σ _ p l (List.Sublist.nodup (b.map _) h)]
 cases l; · simp; rfl -- tune
 simp only [List.cons_ne_nil,if_false]; rw [proper,zero_add]
-- topological linearity only. constructors as in South
variable {A A':Type}[NormedAddCommGroup A][NormedSpace ℂ A][CompleteSpace A][NormedAddCommGroup A'][NormedSpace ℂ A'][CompleteSpace A']
lemma Soft.same_t (l:List I)(x:A): Soft l (fun _=>x) (fun _=>x):= ⟨zeroR x,zeroR x,fun _ _=>rfl⟩
lemma Soft.graph {l:List I}{x y:Key I→ A}(p:Soft l x y)(L:A→L[ℂ]A'): Soft l (fun z=>L (x z)) (fun z=>L (y z)):= ⟨sc_V p.leftR L,sc_V p.rightR L,fun l v=> Eq.trans (sim_H p.leftR L l roots) (Eq.trans (congrArg L (p.tip _ v)) (sim_H p.rightR L l roots).symm)⟩
lemma Soft.sum' {T:Type*}(z:Finset T){l:List I}{x y:T→Key I→ A}(t:∀ i∈z,Soft l (x i) (y i)): Soft l (fun j=>∑ i∈z,x i j) (fun j=>∑ i∈z,y i j):=by
 let p:=tip_bank z x (fun i w=>(t i w).leftR); let q:=tip_bank z y (fun i w=>(t i w).rightR); exact ⟨p.1,q.1,fun l b=> Eq.trans (p.2 l) ((sum_congr rfl fun i w=>(t i w).tip _ b).trans (q.2 l).symm)⟩
lemma Soft.plus {l:List I}{x y u v:Key I→A}(p: Soft l x y)(t:Soft l u v): Soft l (fun i=>x i+u i) (fun i=>y i+v i):=⟨dub_V p.1 t.1,dub_V p.2 t.2,fun i u=> (tip_A p.1 t.1 _).trans ((congrArg₂ _ (p.tip i u) (t.tip i u)).trans (tip_A p.2 t.2 _).symm)⟩ -- structure access .2? `.rightR` numeric
lemma Soft.east {l:List I}{x y:Key I→A}(p:Soft l x y):South (fun _=>1) l x y:=by intro i b; rw [p.tip i b]; simp
lemma westS {l:List I}{x y:Key I→A}(v:River x)(t:River y)(p:South (fun _=>1) l x y):Soft l x y:=by
 refine ⟨v,t,fun i b=>?_⟩; simpa using (p i b).symm
variable {B:Type}[NormedCommRing B][NormedAlgebra ℂ B][CompleteSpace B]{x y g u:Key I→B}{l:List I}
lemma Soft.expΩ (t:Soft l x y)(p:l.Nodup): Soft l (exp ∘ x) (exp ∘ y):=westS t.1.exp_V t.2.exp_V (south_e t.1 t.2 _ p t.east)
lemma Soft.mul (t:Soft l x y)(r:Soft l g u)(p:l.Nodup): Soft l (fun z=> x z*g z) (fun z=> y z*u z):=westS (t.1.mul_T r.1) (t.2.mul_T r.2) (south_prod t.1 r.1 t.2 r.2 _ p t.east r.east) -- parameter typos
lemma Soft.gain{T:Type*}(s:Finset T)(X Y:T→Key I→B)(t:∀ i∈s,Soft l (X i) (Y i))(p:l.Nodup): Soft l (fun z=>∏ i∈s,X i z) (fun z=>∏ i∈s,Y i z):=by
 induction s using Finset.induction_on with
 | empty=> simp_rw [prod_empty]; exact Soft.same_t ..
 | insert i s u ih=> simp_rw [prod_insert u]; exact (t i (mem_insert_self ..)).mul (ih (fun i h=> t i (mem_insert_of_mem h))) p
end TreasuryFog
end YM.CF.Vow
