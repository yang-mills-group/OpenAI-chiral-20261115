import YM.CF.Bake.Pal
import YM.CF.Lilt.Flow
import YM.CF.Wray.Graze
import YM.CF.Jade.Move
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
abbrev grounded(i:Troupe S r (Words S)):Prop:= i.card ≤ 2 ∧∀ j∈i,∃ v:Site (Domain N B), j=Lilt.binL v
abbrev elderB (i:Troupe S r (Words S)):Prop:=∃ p:Rust (mid P B),i={sentR p}
abbrev fallow (S:StepData (Domain N B) (Domain P B))(r:ℕ):Finset (Troupe S r (Words S)):=univ.filter fun i=>¬grounded i∧¬elderB i
lemma binV(u:Rill.Arch G d)(i:Lattice.Site (Domain N B))(H H':ℝ) : UQ H H' (Lilt.binL (S:=S) (r:=r) i)=1:=rfl -- remove Arch
local notation "L₁"=> stampY
lemma shelfX(B:Troupe S r (Words S))(K' K:ℝ)(h:1 ≤ K')(h':1 ≤ K):1 ≤ stampY K' K B:= one_le_prod fun i _=> by rcases i with i|i; exact h; rcases i with i|i; exact h'; rcases i with i|i; exact h; rcases i with i|i; exact le_rfl; exact h -- order rcases sequencing
local notation "Π"=> Troupe S r (Words S)
lemma hot_v (R' K:ℝ)(h:1 ≤ R')(h':1≤ K)(T:Π)(i:Folk S r (Words S))(hp:i∈T): UQ R' K i ≤ stampY R' K T:=by
 nth_rw 1 [←insert_erase hp]; rw [stampY,prod_insert (show i∉_ from notMem_erase i T)]
 exact le_mul_of_one_le_right (show 0 ≤ UQ R' K i from (zero_le_one.trans (by simpa [stampY] using shelfX {i} R' K h h'))) (shelfX _ _ _ h h') -- tune nth_rw
open Lilt
lemma pay_v(R' K:ℝ)(h:1 ≤ K)(hp:K ≤ R')(T:Π)(t:T∈fallow S r): R' ≤ stampY R' K T ∨ (Palot.outC 1 T∧ K≤ stampY R' K T) ∨ (Palot.outC 2 T∧ 1 ≤ stampY R' K T):=by
 obtain ⟨u,v⟩:=(mem_filter.mp t).2; by_cases w:T.card>2
 · exact Or.inr (Or.inr ⟨(show 2 ≤ T.card-1 from by omega), shelfX _ _ _ (h.trans hp) h⟩)
 obtain ⟨i,w,y⟩:∃ i∈T,∀ j:Site (Domain N B),i≠ binL j:=by contrapose! u; exact ⟨le_of_not_gt w,u⟩ -- neg? test
 have X:= hot_v R' K (h.trans hp) h T i w; rcases i with i|i
 · exact Or.inl X
 rcases i with i|i
 · refine Or.inr (Or.inl ⟨?_,X⟩); change 1≤T.card-1
   have hh:T.card ≠1:=by intro g; apply v; obtain ⟨b,rfl⟩:=Finset.card_eq_one.mp g; rw [mem_singleton] at w; exact ⟨i,w ▸ rfl⟩ -- tune
   have ht:= card_pos.mpr ⟨_,w⟩; omega
 rcases i with i|i
 · exact Or.inl X
 rcases i with i|i
 · exact False.elim (y i rfl)
 exact Or.inl X
end YM.CF.Jade
