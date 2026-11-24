import YM.CF.Pith.Grid
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
variable {r:ℕ}
variable (w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
variable (V_:ℝ)
local notation "Φ"=> F.hat R x
variable(Y1: Monk SU.group S)
-- Rflare independent of Y except Bravo, discounted pref before.All
variable {a A' ε b α γ:ℝ}{q q':Chi}{u u0 s:ℝ}(ε':Fend V H M Z F q Y.p X.p γ α j l r)
variable{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y X U)
variable (k₀ k₁:ℕ)(s0:ℝ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(pV:1<I.fine)(k_W:5*Y.p.B +4≤10*radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hT:0 < s) (pT:0<u)(hU:u< firstRadius SU.group)
variable (Uq:(j+110)*radiusB x+14 ≤ r) (pQ:2*((j+5)*radiusB x) ≤ r)(ht:0 ≤ V_)(hY:Y.p.order=k)(pX:X.p.order=k)(hK:radiusB x ≤ X.p.B)
variable (P_B:Stake.PondP V F x s u j l (k+2)) (K0: Troupe S r (Words S))(P0: Eire.Ride S)
open Plume
open Nor
variable {c vL:ℝ}(Pz: Folk S r (Words S)→ Track (Eire.Ride S) ℝ)
open scoped Classical
variable {γ':ℝ}
variable (h0:vL=(tolQ X.p).supportExponent+γ')(uQ:X.p.B=radiusB x)(p0:0<γ')
local notation "Ue"=> Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B)))
local notation "Ωe"=> Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B)
-- Ribbon vector measured local Aux Proto.SP.Anchor.Norin. Does not assume vacuum.
open Vow Bake
variable (KcV:Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B))))(F':Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B))(Pinc: GroV V F Z M P_ w' ε' D_ KcV F' V_ c γ')
local notation "Zκ"=> pence_v X.p KcV V_
local notation "Zp"=> cone_f F'
open Lilt Feu
local notation "Πq"=> Troupe S r (Words S)
local notation "σn"=> Palot.leaf (Site (Domain N B))
local notation "Γ"=>rowsT S r
local notation "Σ'"=> (mid N B)
private lemma skip(T:Πq)(v:grounded T):¬elderB T:=by
 rintro ⟨b,rfl⟩; obtain ⟨p,h⟩:= v.2 _ (mem_singleton_self _); cases h -- tune
private lemma ground_flags(i:Πq)(p:i∈Γ):bargainP i=∅:=by obtain ⟨T,rfl,_⟩:= rowV i (mem_filter.mp p).2; exact (pine_d ..).2.2
lemma elder_q(Pi:Πq)(u:elderB Pi):bargainP Pi=∅:=by
 obtain ⟨u,rfl⟩:=u; have hz:({sentR u}:Πq).toLeft=∅:=by ext; simp [sentR]
 exact (show (cook S ({sentR u}:Πq).toLeft).flags=∅ from by rw [hz]; exact Feu.kflags ..)
abbrev reign_t (S:StepData (Domain N B) (Domain P B))(r:ℕ):Finset (Troupe S r (Words S)):=univ.filter elderB
abbrev nearR(S:StepData (Domain N B) (Domain P B))(r:ℕ):Finset (Troupe S r (Words S)):= (fallow S r).filter fun j=> bargainP j=∅
local notation "Ac_"=> reign_t S r
local notation "Fa"=> nearR S r
local notation "Πz"=> cone_f F'
abbrev high_Q : Pax (mid N B):=fun i=>∑ t∈ nearR S r,F' t i
abbrev old_Q : Pax (mid N B):=fun i=>∑ t:Troupe S r (Words S) with elderB t,F' t i
abbrev birth_C : Pax (mid N B):=fun i=>∑ t∈ rowsT S r,F' t i
abbrev yesC (P:Πq):= (cook S P.toLeft).flags=∅
private lemma bobble: univ.filter (fun P:Πq=>yesC P) = (nearR S r∪ reign_t S r) ∪ rowsT S r:=by
 ext i; constructor
 · intro t; have h:= (mem_filter.mp t).2; simp only [nearR,reign_t,rowsT,fallow,mem_union,mem_filter,mem_univ,true_and]; by_cases z:grounded i; exact Or.inr z; left; by_cases p:elderB i; exact Or.inr p; exact Or.inl ⟨⟨z,p⟩,h⟩
 intro w; rw [mem_union, mem_union] at w; apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
 rcases w with (w|w)|w
 · exact (mem_filter.mp w).2
 · exact elder_q i (mem_filter.mp w).2
 exact ground_flags i w
lemma unwoven_c(i:σn): (nixV (Πz)) i= high_Q F' i + old_Q F' i + birth_C F' i:=by -- Pix needs parentheses
 unfold nixV cone_f high_Q old_Q birth_C
 rw [bobble, sum_union (s₂:=Γ),sum_union (s₂:=Ac_)]
 · exact Finset.disjoint_left.mpr fun i h v=> ((mem_filter.mp (mem_filter.mp (show i∈ Fa from h)).1).2.2 (mem_filter.mp v).2)
 rw [Finset.disjoint_union_left]; refine ⟨?_,?_⟩; · exact Finset.disjoint_left.mpr fun i v p=>(mem_filter.mp (mem_filter.mp v).1).2.1 (mem_filter.mp p).2 -- tune scopes
 exact Finset.disjoint_left.mpr fun i v p=>skip _ (mem_filter.mp p).2 (mem_filter.mp v).2
private lemma bygone (t:Rust (mid P B)):({sentR t}:Πq)∈Ac_:= mem_filter.mpr ⟨mem_univ _,t,rfl⟩
include Pinc
lemma sow_v (i:σn):old_Q F' i= ∑ p:Roc (mid P B), F' (subtK S p) i:=by
 let H' (t:Rust (mid P B)):=({sentR t}:Πq); have h:(∑ t:Rust (mid P B),F' (H' t) i)=old_Q F' i:=by
    refine sum_bij (fun t _=>H' t) (fun j _=>bygone j) (fun i h j v k=>?_ ) (fun i v=>?_ ) (fun _ _=>rfl)
    · simpa [H',sentR] using k
    obtain ⟨b,u⟩:= (mem_filter.mp v).2; exact ⟨b,mem_univ _,u.symm⟩
 rw [←h, Fintype.sum_sum_type, sum_eq_zero (s:=univ) (f:=fun t:Force (mid P B)=>F' (H' (.inr t)) i), add_zero];  intro j _; exact fall_p V F Z M P_ w' ε' D_ (H' (.inr j)) _ _ (Pinc.quiet _ _).toLullT j rfl
 -- defeq
end YM.CF.Jade
