import SatinThinGear
import YM.CF.Brood.Rink
import YM.CF.Brood.Ship

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


variable {I:Type} [Fintype I][LinearOrder I] {J:Type} [Fintype J][LinearOrder J]
abbrev Article (I:Type):= Lex (I×Fin 2)
abbrev host (j:Article I): I:= (ofLex j).1
abbrev layer (j:Article I): Fin 2:= (ofLex j).2
abbrev phaseMark (i:I)(p: Fin 2): Article I:=toLex (i,p)
lemma recover_art (x:Article I): x=phaseMark (host x) (layer x):=rfl
lemma art_fork {p: Article I → Prop}(q:∀ x, p (phaseMark x 0))(r:∀ x,p (phaseMark x 1))(x:Article I) : p x:=by
 rw [recover_art x]; generalize host x=i; generalize layer x=j; fin_cases j; exact q i; exact r i
lemma two_pages {p: Article I → Prop}(q:∀ x j, p (phaseMark x j))(x:Article I):p x:=q (host x) (layer x)
abbrev links (i:I):Fin 2↪Article I:=⟨phaseMark i,fun _ _ h=>congrArg layer h⟩
attribute [-instance] instDecidableEqLex
variable {N B:Side}
local notation "Ω"=> mid N B
variable (p:I→Site (mid N B))(ε:Injective (Cube.node ∘ p))
abbrev treeO : Article I→Site (mid N B):= p ∘ host
local notation "pζ"=> Cube.node ∘ treeO p
include ε
lemma doubled (i:Article I):pipe_ζ pζ i=univ.map (links (host i)):=by
 ext j; constructor
 · intro z; have hp: host j = host i := ε (mem_filter.mp z).2; exact mem_map.mpr ⟨layer j,mem_univ _,hp ▸ (recover_art j).symm⟩
 rintro z; obtain ⟨a,h,rfl⟩:= mem_map.mp z; exact mem_filter.mpr ⟨mem_univ _,rfl⟩
lemma doubler {Y:Type}[AddCommMonoid Y] (f:Article I→ Y)(i:I)(a:Fin 2): ∑ j∈pipe_ζ pζ (phaseMark i a), f j=f (phaseMark i 0)+f (phaseMark i 1):=by
 rw [doubled p ε,Finset.sum_map, Fin.sum_univ_two]; rfl
omit ε
lemma double_force (X:BudgetPoint)(h:Very_Ψ p X.B): Roots.Force_M X.B pζ 2:=by
 let B:= X.B
 constructor; · intro i j z; apply h.2 _ _ z
 intro x; let c:=cape_B B; let S:= reach_B c B pζ x; change S.card≤ 2; by_cases t:S.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp t]; simp
 obtain ⟨i,e⟩:= t; have hf: S⊆ univ.map (links (host i)):=by
    intro j z; have hzS(g)(v:g∈S): separation x ((Cube.node ∘p) (host g))≤ B+c:= (Finset.mem_filter.mp v).2; have heτ:(Cube.node ∘p) (host i)=(Cube.node∘p) (host j):=by
       by_contra k; have hp:= h.2 _ _ k; have ht:separation ((Cube.node ∘p) (host i)) ((Cube.node ∘p) (host j))≤ (B+c)+(B+c):=(separation_triangle _ x _).trans (add_le_add ((separation_comm ..).le.trans (hzS i e)) (hzS j z)); unfold c B at ht; omega
    rw [← doubled p h.1]; exact Finset.mem_filter.mpr ⟨mem_univ _,heτ.symm⟩
 exact (card_le_card hf).trans (by simp)
lemma double_gap (L:Side)(X:BudgetPoint)(h:Very_Ψ p X.B)(u: ((L.val+1)*(4*X.B+2)+2*X.B)≤ X.B+cape_B X.B): GapN (treeO p) X.B L.val 2 :=by
 intro y; exact le_trans (Finset.card_le_card fun i z=> mem_filter.mpr ⟨mem_univ _, ((separation_comm ..).le.trans ((mem_filter.mp z).2.trans u))⟩) ((double_force p X h).2 y)
structure Funds (L:Side) where
 ticket: ℝ
 adjustment: ℝ
 nonzero: ticket≠0
 floor:|ticket⁻¹| ≤ 64*((L.val:ℝ)⁻¹)^4
 lid:|ticket|≤zoomC L
 small:|adjustment| ≤ 1/8
variable (L:Side)(t k b:ℝ)
def dust_F : ℝ:=if 0<t ∧ KeyRadius L t k then t/k else (L.val:ℝ)^4 -- independent gap
private lemma dusty (hf:0<t)(p:KeyRadius L t k) : k ≠0:= by
 have he:= p.dn; have h:0 < ((L.val:ℝ)⁻¹)^4*t/64:=by positivity
 exact abs_pos.mp (h.trans_le he)
def get_F : Funds L:=by
 refine ⟨dust_F L t k,if 0<t ∧ KeyRadius L t k ∧ |b|≤|k|/8 then -b/k else 0, ?_, ?_,?_,?_⟩
 · unfold dust_F; split; next h=> exact div_ne_zero h.1.ne' (dusty _ _ _ h.1 h.2)
   positivity
 · unfold dust_F; split; next h=>
     rw [abs_inv,abs_div, inv_div,div_le_iff₀ (abs_pos.mpr h.1.ne'),abs_of_pos h.1]; exact h.2.up
   rw [abs_inv,abs_of_pos (by positivity),←inv_pow]; have h:0≤((L.val:ℝ)⁻¹)^4:=by positivity
   linarith
 · unfold zoomC dust_F; split; next h=>
     rw [abs_div,div_le_iff₀ (abs_pos.mpr (dusty _ _ _ h.1 h.2)),abs_of_pos h.1]; refine le_trans ?_ (mul_le_mul_of_nonneg_left h.2.dn (by positivity)); field_simp; linarith -- tune
   rw [abs_of_pos (by positivity)]; have h:0≤(L.val:ℝ)^4:=by positivity
   linarith
 split; next h=>
   rw [abs_div,abs_neg,div_le_iff₀ (abs_pos.mpr (dusty _ _ _ h.1 h.2.1))]; linarith only [h.2.2]
 simp
lemma fund_a (hf:0<t)(p:KeyRadius L t k) : (get_F L t k b).ticket*k=t:=by simp only [get_F,dust_F,if_pos (And.intro hf p),div_mul_cancel₀ _ (dusty _ _ _ hf p)] -- ⟨⟩ elaboration implicit tune
lemma fund_b (hf:0<t)(p:KeyRadius L t k)(s: |b|≤ |k|/8) : (get_F L t k b).adjustment*k+b=0:=by unfold get_F; dsimp only; rw [if_pos ⟨hf,p,s⟩,div_mul_cancel₀ _ (dusty _ _ _ hf p)]; exact neg_add_cancel _

variable (D:Funds L)
def moveCost (i j:Fin 2):ℝ := !![ D.ticket, zoomM L*D.adjustment; 0, zoomM L] i j
lemma move_zeroes : moveCost L D 1 0=0 ∧ moveCost L D 0 0=D.ticket∧moveCost L D 1 1=zoomM L ∧ moveCost L D 0 1=zoomM L*D.adjustment:= ⟨rfl,rfl,rfl,rfl⟩
def TicketM (i j:Article I):ℂ:= (moveCost L D (layer i) (layer j):ℝ)
lemma cost_bound (i j:Fin 2) : |moveCost L D i j| ≤ zoomM L:=by
 have ⟨y,e,h,p⟩:=move_zeroes L D; have ht:=zoomM_p L; have hL:zoomC L≤ zoomM L:= by
    have h:0 ≤ (L.val:ℝ)^4:=by positivity
    unfold zoomC zoomM; linarith; -- tune
 have h0 : |D.adjustment| ≤1:=D.small.trans (by norm_num)
 fin_cases i<;>fin_cases j
 · exact (by change |moveCost L D 0 0|≤_; rw [e]; exact D.lid.trans hL)
 · change |moveCost L D 0 1|≤_; rw [p,abs_mul,abs_of_pos ht]; exact mul_le_of_le_one_right ht.le h0
 · change |moveCost L D 1 0|≤_; rw [y,abs_zero]; exact ht.le
 change |moveCost L D 1 1|≤_; rw [h,abs_of_pos ht]
lemma tax_bound (i j:Article I): ‖TicketM L D i j‖ ≤ zoomM L:=by rw [TicketM,Complex.norm_real,Real.norm_eq_abs]; exact cost_bound ..
def compassκ (L:Side):ℝ:= 4*zoomM L
lemma compass_pos : 1 ≤ compassκ L:=by have he:= zoomC_p L; unfold compassκ zoomM; unfold zoomC at he; linarith
include ε
lemma bound_C (z:Key (Article I))(v:∀ i, ‖z i‖ ≤ 2*b)(a:Article I): ‖ toV_C pζ (TicketM L D) z a‖ ≤ compassκ L*b:=by
 rw [recover_art a,toV_C,doubler p ε]; have hp(x y:Article I): ‖TicketM L D x y *z y‖ ≤ zoomM L*(2*b):=by rw [norm_mul]; exact mul_le_mul (tax_bound ..) (v y) (norm_nonneg _) (zoomM_p L).le
 apply (norm_add_le ..).trans; unfold compassκ; refine (add_le_add (hp _ _) (hp _ _)).trans_eq ?_; ring
end YM.CF.QuadClock
