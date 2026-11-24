import SatinThinCarry
import SatinThinParliament
import SatinThinLoyal
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
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
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
-- arithmetic delivery & Versions
local notation "X" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s
/- Parliament finances. -/
variable {I:Type} [Fintype I] [LinearOrder I]
local notation:max "Rn" s:max=> slotFee P s
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
local notation "ΞM"=>List (Article I)
variable (o:I→Site (side Y i f))(E:Key (Article I)→RegBudget (side Y i (f+1)))(F:Key (Article I)→ForceBudget (side Y i (f+1)))
variable (T:Fin 2→Topic (side Y i (f+1)))
local notation "Kt"=> (patternQ Y f i k).val
local notation "µ" s:max=> city (Ω s)
local notation "NA" s:max=> nightSet (I:=I) Y i s
local notation "RA" s:max=> rideSet (I:=I) Y i s
variable {A:ℝ}{U:Funds P.R.L}{E':nightSet Y i f (I:=I)}{F':rideSet Y i f (I:=I)}(u:transportA Y i k o E F E' F' U)
local notation "Γ"=> TicketM L U
local notation "𝚨"=> Cube.node ∘ treeO o
/- Snow invoice. Relative tolls already bought; true integrals in Version b class. -/
local notation "Πt"=> Roots.snow (Cube.node ∘ treeO o) (TicketM L U)
local notation "Ψc"=> artwork Y i k E' F'
local notation "Ψf"=> artwork Y i k E F
local notation:max "χ" l:max=> carryStep Y i k (artwork Y i k E F l)
variable (p:Satin.PairIdx Y f i k)(t:Very_Ψ o (RootBook Y i k f).p.B)
local notation "Hc" s:max=> morning Y i k s
structure Visor (s l: ℕ)(A:Key (Article I)→RegBudget (side Y i s))(B':Key (Article I)→ForceBudget (side Y i s))(F:Article I→Mark (side Y i l)):Prop where
 owns (j:Article I): AtSupport false univ (F j)
 safe (l:List (Article I))(t:CasePage l): Version (µ s) (artwork Y i k A B' l) -- shadow i hygienic explicit missing _
 arrive (l':List (Article I))(t:CasePage l'): markedRead (1:Mark (side Y i s)) (S s) (artwork Y i k A B' l')= mark_cost Y i k l (l'.map F).prod
variable (xyz:Article I→Mark (side Y i v))(g:Visor Y i k (f+1) v E F xyz)
variable (v':v ≤ Y.uv k)
local notation "sp" l:max=> ((l).map xyz).prod
noncomputable def appeal (j:Article I): Mark (side Y i v) := Γ (toPrin j) j • xyz (toPrin j)+ Γ (toGap j) j • xyz (toGap j)
local notation "Idt"=> appeal Y i xyz (U:=U)
include g
lemma owns_app (j:Article I):AtSupport false univ (appeal Y i xyz j (U:=U)):= by unfold appeal; exact ((g.owns _).smulM _).addM ((g.owns _).smulM _)
include p t v'
-- not yet Flight above; snow billing all consults. avoid unique F etc.
lemma ledger_snow (l c:List (Article I))(h:CasePage (c++l)): let H:=(fun x:Orbit (side Y i f)=>Πt (fun y=> χ (c++y) x) l); Version (µ f) H ∧ markedRead 1 (S f) H = mark_cost Y i k v (sp c * (l.map Idt).prod):=by
 induction l generalizing c with
 | nil=> intro H; have hh:CasePage c:= by simpa using h
 -- tune
         have hz:= g.safe c hh; rw [show H= χ c from (by unfold H; simp only [Roots.snow,List.append_nil]),List.map_nil,List.prod_nil,mul_one]; refine ⟨phaseStep Y _ _ p hz,?_⟩; rw [kayStep Y i k p hz _ (AtSupport.oneM _),ascendUnit Y f i k p]; exact g.arrive c hh
 | cons j l ih=>
    intro H; let j0:= toPrin j; let j1:= toGap j; let d(t:Ξ):=c++[t]; let Y0(t:Ξ):=(d t).map QuadClock.host; have hp(t)(u:QuadClock.host t=QuadClock.host j):CasePage (d t++l):=by unfold CasePage; unfold d; simp only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append,u]; unfold CasePage at h; simpa [u] using h
    let z(η:Ξ)(x:Orbit (side Y i f)):=Πt (fun y=> χ (d η++y) x) l; let L':=(l.map Idt).prod
    have he':H=(fun x=> Γ j0 j • z j0 x+ Γ j1 j • z j1 x):=by
       funext x; unfold H z; rw [Roots.snow]; -- `doubler o t.1`; at j not phaseMark, rest restructure.
       rw [doubled o t.1,Finset.sum_map,Fin.sum_univ_two]; unfold d; simp only [List.append_assoc,List.singleton_append]; rfl
    obtain ⟨X0,e⟩:= ih (d j0) (hp _ rfl); obtain ⟨X1,gQ⟩:=ih (d j1) (hp _ rfl); -- maybe definitional `let H` survives
    let d0:= Γ j0 j; let d1:= Γ j1 j; let W:= mark_cost Y i k v; let T:= sp c; let P0:= xyz j0; let P1:=xyz j1
    let K0:Mark (side Y i v):=(T*P0)*L'; let K1:Mark (side Y i v):=(T*P1)*L'; have qv:= (AtSupport.oneM (univ:Support (More (Ω f)))).env
    have hv0: markedRead 1 (S f) (z j0)=W K0:=by change markedRead 1 _ (z j0)= W (sp (d j0)*L') at e; unfold d at e; simpa only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one] using e -- parentheses
    have hv1: markedRead 1 (S f) (z j1)=W K1:=by change markedRead 1 _ (z j1)= W (sp (d j1)*L') at gQ; unfold d at gQ; simpa only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one] using gQ
    rw [he']; have hQ: Version (µ f) (z j0):=X0; have hP:Version (µ f) (z j1):=X1; let pH:= multV (a:=d0) hQ; let pQ:= multV (a:=d1) hP
    refine ⟨plusV pH pQ,?_⟩; rw [ring_plus Y i 1 qv pH pQ,ring_scale Y i,ring_scale Y i,hv0,hv1];
    have ht:T*(Idt j*L')= (d0•K0)+(d1•K1):=by unfold appeal K0 K1; change T*((d0•P0+d1•P1)*L')=_; rw [add_mul,mul_add,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.mul_smul_comm,mul_assoc T,mul_assoc T] -- tune
    change d0 • W K0+d1 • W K1 = W (T*(Idt j*L')); rw [ht]
    let p':=morning_safe Y i k p.1 v'; have hw:AtSupport false univ T:= receipt_word (g.owns) _ (fun i _=>Finset.Subset.refl _); have hw':AtSupport false univ L':=receipt_word (fun j=>owns_app (U:=U) Y i k E F xyz g j) _ (fun i _=>Finset.Subset.refl _)
    have hk:Envelope (d0 • K0):= ((((hw.mulM (g.owns j0)).mulM hw').smulM _)).env; have hy:Envelope (d1 • K1):= (((hw.mulM (g.owns j1)).mulM hw').smulM _).env
    unfold W mark_cost; rw [palm_plus Y i (d0 • K0) hk hy p',palm_scale Y i,palm_scale Y i]
include u
lemma visor_step (G':Article I→Mark (side Y i v))(x:Idt=G') : Visor Y i k f v E' F' G':=by
 subst G'; constructor; · intro j; exact owns_app Y i k E F xyz g j
 · intro l v; have u:= receipt_AE Y i k o E F u p t l v; exact (ledger_snow Y i k o E F p t (U:=U) xyz g v' l [] ((List.nil_append l).symm ▸ v)).1.cong u.symm
 intro l v; rw [read_version _ _ (receipt_AE Y i k o E F u p t l v)]; exact (ledger_snow Y i k o E F p t (U:=U) xyz g v' l [] ((List.nil_append l).symm ▸ v)).2.trans (congrArg _ (one_mul _))
#print axioms visor_step
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
