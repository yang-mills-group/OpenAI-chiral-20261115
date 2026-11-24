import SatinThinFace
import SatinThinTeach
/-! Credentials for using cap reclamations. Ordinary L_v0 calls at actual REAL step. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Vow
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
open Salt Ione Bake Trees Ursell

/- Keep 'input-response-symmetry' and 'actor sign' different. Here ordinary
    Ledger locale transformations, no (-1)^q character yet. -/
def passingR (N:Side)(T:Sweep N)(u v:RegBudget N):Prop:=∀ i x, v (moveHub T i) (flashA T x)=suit_Y T (u i x)
def passingF (N:Side)(s:Sweep N)(u v:ForceBudget N):Prop:= ∀ (i:Force N) (x:Orbit N), Injective (priorP x.2)→ v (moveForce s i) (yellA s x)= suit_Y s (u i x)
def passingU (N:Side)(T:Sweep N)(u v:Cusp N):Prop:=∀ i:Aura N,∀ x:Orbit N,Injective (priorP x.2)→∀ D⊆i.val,v (moldA T i) (actY T D) (yellA T x)=suit_Y T (u i D x)
def passingU_n (N:Side)(T:Sweep N)(u v:Cusp N):Prop:=∀ i:Aura N,∀ x:Orbit N,Injective (priorP x.2)→∀ D:Support (More N), D.Nonempty → D⊆i.val→ v (moldA T i) (actY T D) (yellA T x)=suit_Y T (u i D x)
def passingFee (N:Side)(T:Sweep N)(u v:Pax N):Prop:=∀ i x, v (moldA T i) (yellA T x)=suit_Y T (u i x)
lemma no_pr (N:Side)(T:Sweep N)(u v:Cusp N)(t:passingU N T u v): passingU_n N T u v:=fun i x p D h g=> t i x p D g
lemma passingCost (u v:Pax n)(T:Sweep n)(p:Turf u)(t:Turf v) (h:∀ i:Aura n,∀ x:Orbit n,Injective (priorP x.2)→ v (moldA T i) (yellA T x)=suit_Y T (u i x)): passingFee n T u v:=by
 intro i x; obtain ⟨o,q⟩:= (sepT (n:=n)).exists; let y:Orbit n:=(x.1,o); rw [p i x o,t (moldA T i) (yellA T x) (yellA T y).2]; exact h i y q
abbrev rust_P (P:BudgetPoint)(K:Vow.Cusp n):= FeeD P (Jade.nixV K) -- nixV namespace?
abbrev rust_L (P:BudgetPoint)(K KΦ:Vow.Cusp n):= budgetR (roomV P (Jade.nixV K) K KΦ)
structure MirrorBill (n:Side)(P:BudgetPoint)(T:Sweep n)(u v:Cusp n): Prop where
 inks: passingU n T u v
 wax: passingFee n T (rust_P P u) (rust_P P v)
 lamp(u' v':Cusp n): passingU_n n T u' v' → passingF n T (rust_L P u u') (rust_L P v v')

/- Special relation supported on paid comparisons; credits stored here for all
    arguments in that upstream rule, include actual bounds of cap purchases. -/
def Unravel (P:BudgetPoint)(u:Pax n)(h:ℝ):Prop:= Turf u ∧∃ (a:ℕ)(b c d e:ℝ)(v:Aura n→ℝ),0≤b ∧ Ready Palot.stern a v b c d e ∧∀ i:Aura n,Medal P i.val ∅ (u i) h (v i)
lemma MirrorBill.vest (T:Sweep n)(u v:Cusp n)(ℓ:passingU n T u v)(p:Unravel P (Jade.nixV u) h)(q:Unravel P (Jade.nixV v) h)(h0:1≤h): MirrorBill n P T u v:=by
 obtain ⟨p,M,a,b,c,d,Z,hz,ht,k⟩:=p; obtain ⟨q,M',a',b',c',d',Z',hz',ht',k'⟩:=q
 let F:=Jade.nixV u; let G:=Jade.nixV v; have he:passingFee n T F G:= passingCost F G T p q (by
    intro i x y; have hu:= ℓ i x y ∅ (empty_subset _); rw [show actY T ∅=(∅:Support _) from map_empty _] at hu; exact hu)
 refine ⟨ℓ,fun i x=> rel_spinsE T i (suit_Y T) x G (fun i=>he i x) ht h0 k hz Z' ht' hz' k' 0,?_⟩
 intro u' v' l i x v; exact rel_valiant T (suit_Y T) x _ (fun i D d p=> ℓ i x v D p) u' v' G (fun i D d p=> l i x v D d p) (fun i=>he i x) ht h0 k hz Z' ht' hz' k' _

/-- BondL.pivotS precise computations have these costs. The hinge φ here
    will be set to that *same* function at each location on any comp. -/
def Matures(n:Side)(P:BudgetPoint)(φ: Cusp n→Cusp n)(h:ℝ)(F:Cusp n):Prop:= Unravel P (Jade.nixV (φ F)) h ∧∀ (s:Sweep n)(X:Cusp n),passingU n s F X→ passingU n s (φ F) (φ X)
lemma Matures.paid (f:Cusp n→Cusp n){F G:Cusp n} (t:Matures n P f h F)(tt:Matures n P f h G)(h0:1≤h)(s:Sweep n)(v:passingU n s F G): MirrorBill n P s (f F) (f G):= MirrorBill.vest s _ _ (t.2 s _ v) t.1 tt.1 h0
end YM.CF.QuadClock
