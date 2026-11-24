import YM.CF.Pith.Class
import YM.CF.Pith.Seed
import YM.CF.Lilt.Sumac
set_option autoImplicit false
set_option maxHeartbeats 520000
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
local notation "M'"=> Stilo.bay
local notation "Tp_"=> Tpt (r:=r) (S:=S)
local notation "AX"=> BranchX (r:=r) S (vast (k:=Z.N1*radiusB x) H) ((H.post+90)*radiusB x)
abbrev rowsT (S:StepData (Domain N B) (Domain P B))(r:ℕ):Finset (Troupe S r (Words S)):= univ.filter grounded
abbrev hitsV(B:Troupe S r (Words S))(V:σn):Prop:= beamH V.val= Scion.cluster AX B
lemma rowV(i:Πq)(p:grounded i):∃ Pt:List (Site (Domain N B)),i=Tpt Pt ∧ Pt.Nodup∧Pt.length≤2:=by
 let T:=univ.filter fun j:Site (Domain N B)=> (Lilt.binL (S:=S) (r:=r) j)∈i; have ht:i=T.image Lilt.binL:=by apply Subset.antisymm; intro j w; obtain ⟨b,h⟩:= p.2 j w; rw [h] at w ⊢; exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,w⟩); intro x v; obtain ⟨j,w,rfl⟩:=mem_image.mp v; exact (mem_filter.mp w).2 -- sequencing tune
 refine ⟨T.toList,(ht.trans ?_), Finset.nodup_toList _,?_⟩
 · ext; simp [Tpt] -- tune
 rw [Finset.length_toList, ← card_image_of_injective T (bin_inj (S:=S) (r:=r)),←ht]; exact p.1
variable (htB:0<radiusB x)
local notation "κp"=> hitsV (r:=r) (H:=H) Z
abbrev around_x (n K:ℕ):ℕ:= 2*railH n * (4*K+2)+2*K
abbrev porch_i (n K:ℕ):ℕ:= (around_x n K+around_x n K+1)^4
abbrev ear_p (L:ℕ):=1+L+L^2
local notation "Ac_"=>rowsT S r
lemma star_p (B:Πq)(P Q:σn)(h:κp B P)(p:κp B Q): P=Q:= Subtype.ext ((bay_beam _).symm.trans ((congr_arg Stilo.bay (h.trans p.symm)).trans (bay_beam _))) -- hits abbrev Eq.trans issue
abbrev reach_P (o:Site (Domain N B)):= halo (around_x Z.N1 (radiusB x)) {o}
local notation "W'"=> reach_P (x:=x) (B:=B) (N:=N) Z
lemma wake_z (o:Site (Domain N B)) : (W' o).card≤ porch_i Z.N1 (radiusB x):= (Corona.halo_size _ _).trans (by simp only [card_singleton,one_mul]; exact le_rfl)
include htB
lemma rowP (B:Πq)(v:B∈ Ac_)(X:σn)(p:κp B X) : coverNumber (radiusB x) X.val ≤2 * railH Z.N1:=by
 obtain ⟨T,rfl,z,b⟩:=rowV B (mem_filter.mp v).2; exact sizedV Z T X p b htB
lemma rowB (B':Πq)(p:B'∈ Ac_)(P₁:σn)(h:κp B' P₁)(o:Site (Domain N B))(xv:o∈P₁.val): B' ⊆ (W' o).image (Lilt.binL (S:=S) (r:=r)):=by
 obtain ⟨T,rfl,z,b⟩:= rowV B' (mem_filter.mp p).2
 intro i w; obtain ⟨j,u,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp w); apply mem_image_of_mem; have he:=pulseS (H:=H) Z T P₁ h j u
 exact halo_spec.mpr ⟨_,mem_singleton_self _,(Corona.extent _ _ xv he).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (rowP Z htB _ p P₁ h)) _)⟩ -- pulseS htB omitted
omit htB
lemma small_I {ι:Type*}[DecidableEq ι](W:Finset ι)(X_:Finset (Finset ι))(h:∀ i∈X_,i⊆W∧ i.card≤2)(v:W.card ≤ k): X_.card ≤ ear_p k:=by
 have he:X_⊆ W.powersetCard 0 ∪ W.powersetCard 1 ∪ W.powersetCard 2:=by intro i p; simp only [mem_union,mem_powersetCard]; obtain ⟨b,z⟩:= h i p; exact Or.imp (Or.imp (fun w=>⟨b,w⟩) (fun w=>⟨b,w⟩)) (fun w=>⟨b,w⟩) (show ((i.card=0 ∨ i.card=1) ∨ i.card=2) from by omega)
 apply (card_le_card he).trans; apply (card_union_le ..).trans; apply (Nat.add_le_add_right (card_union_le ..) _).trans; simp_rw [card_powersetCard,Nat.choose_zero_right,Nat.choose_one_right]; refine add_le_add (Nat.add_le_add_left v _) ?_; exact (Nat.choose_le_pow ..).trans (Nat.pow_le_pow_left v _) -- tune
abbrev sealsD (o:Site (Domain N B)):= (rowsT S r).filter (fun bV=>∃ W:Palot.leaf (Site (Domain N B)),o∈W.val ∧κp bV W)
include htB
lemma card_W(o:Site (Domain N B)) : (sealsD (S:=S) (r:=r) (H:=H) Z o).card ≤ ear_p (porch_i Z.N1 (radiusB x)):=by
 refine small_I ((W' o).image (@binL N P B S r)) _ ?_ ((card_image_le).trans (wake_z Z o)); intro i v; obtain ⟨p,j,w,k⟩:=mem_filter.mp v; exact ⟨rowB Z htB _ p j k o w,(mem_filter.mp p).2.1⟩ -- ABI tune
end YM.CF.Jade
