import YM.CF.Buffered.Duels
import GaugeFieldConstruction.TurnBridgeJ
import GaugeFieldConstruction.FineAlJ
import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
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
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k:ℕ) {P' V: Side} {f r t v :ℕ}
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "X_" s:max=> RootBook Y i k s
local notation "µ" s:max=> city (Ω s)
variable {I J G:Type} [Fintype I] [Fintype J][LinearOrder I][LinearOrder J] [LinearOrder G]
variable (p:(Y.voyage i).kick≤ k)
local notation "ν"=> Y.uv k
local notation "θ"=> P.R.L
variable (w:I→G)(X: HousingJ Y i G)(K:G→Prop)(t:f ≤Y.uv k)(E: List I→Orbit (side Y i f)→ Phys (side Y i f))(A:I→Mark (side Y i (Y.uv k)))
variable {N:Side}
variable (σ:I→Seat (side Y i f))(R:I→I→ℂ)
variable (vP:κWork G (Seat (side Y i f)) w σ)
local notation "κ0"=> RevenueT Y i k
local notation "ƒ"=> convoy Y i k t
local notation "Gc"=> city (side Y i (Y.uv k))
variable (Q:Finset I)(M:I→Mark (side Y i f))(qM:∀ j∈ Q,AtSupport false (X f (w j)) (M j))
abbrev AtJO (l:List I):= (l.map w).toFinset
lemma tile0J (R S:Finset G)(q:R⊆S): Tiling Y i X R f⊆ Tiling Y i X S f:= by intro i u; obtain ⟨j,p,t⟩:= mem_biUnion.mp u; exact mem_biUnion.mpr ⟨j,q p,t⟩
lemma tilesOne (j:G): Tiling Y i X {j} f=X f j:= by unfold Tiling; simp
lemma tilesUnion (R S:Finset G): Tiling Y i X (R∪ S) f= Tiling Y i X R f∪ Tiling Y i X S f:=union_biUnion ..
lemma tile_self (S:Finset G)(j:G)(h:j∈ S): X f j⊆ Tiling Y i X S f:= subset_biUnion_of_mem _ h -- tune
-- sheets assembled later
variable (Pq:Montana Y i k X f)
include qM
lemma tileList (L:List I) (h:L.toFinset⊆Q)(U:Finset G)(u:AtJO w L ⊆ U):AtSupport false (Tiling Y i X U f) (L.map M).prod:=by
 induction L with
 | nil=> exact AtSupport.oneM _
 | cons j l ih=>
    rw [List.map_cons,List.prod_cons]; have hp:l.toFinset⊆Q:=Finset.Subset.trans (by simp :l.toFinset⊆(j::l).toFinset) h; refine ((qM j (h (by simp))).mono (tile_self Y i X U (w j) (u (by simp [AtJO])))).mulM (ih hp (Finset.Subset.trans ?_ u)); simp [AtJO]
include Pq p
lemma altarList (L:List I)(h:L.toFinset⊆Q)(v0:(L.map w).Nodup): convoy Y i k t (L.map M).prod=(L.map (ƒ ∘ M)).prod:=by
 induction L with
 | nil => exact convoy_one _ _ _ p t le_rfl
 | cons j l ih=>
    obtain ⟨g₀,e⟩:= List.nodup_cons.mp v0; let T:= AtJO w l; have he:l.toFinset⊆Q:= Finset.Subset.trans (by simp:l.toFinset⊆(j::l).toFinset) h
    have v : Disjoint ({w j}:Finset G) T:= disjoint_singleton_left.mpr (by exact fun p=>g₀ (List.mem_toFinset.mp p)) -- tune
    rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons]; rw [turnU Y i k p _ _ Pq (M j) (show AtSupport false (Tiling Y i X {w j} f) (M j) from ?_) t le_rfl T _ v (tileList Y i w X Q M qM l he T (Subset.refl _)), ih he e] -- tune order
    rfl
    rw [tilesOne]; exact qM _ (h (by simp))
omit qM Pq p
lemma region_coast (A B:Mark N)(U X:Finset (Seat N))(p:PostSupport false U A)(q:PostSupport false X B)(x:Disjoint U X): Commute A B:=by
 unfold Commute SemiconjBy; funext z; exact Cin.evenc (p.trade z) (q.trade z) (Finset.disjoint_left.mpr (fun {i} H F=> disjoint_left.mp x ((modes_at ..).mp H) ((modes_at ..).mp F))) -- Finset i binder implicit. tune
include Pq
lemma region_meet (A B:Mark (side Y i v))(u:v≤ν)(h:f≤v)(j l:G)(hv:j≠l)(x:PostSupport false (X v j) A)(y:PostSupport false (X v l) B): Commute A B:= region_coast A B _ _ x y (Finset.disjoint_left.mpr (fun {x0} f g=>not_lt_of_ge (by rw [separation_self]; exact Nat.zero_le _) (Pq.gap v h u _ _ hv _ f _ g))) -- tune
include qM p
local notation "Qm"=> ƒ ∘ M
lemma plot_U (j)(p':j∈ Q): AtSupport false (X ν (w j)) (Qm j):=by
 rw [← tilesOne Y i X (w j)]; apply courier Y i k p X _ Pq _ _ t le_rfl; rw[tilesOne]; exact qM _ p'
lemma stone_Z (T S:List I)(g:S.toFinset⊆Q)(η:S.Perm T)(v:(S.map w).Nodup): (S.map Qm).prod= (T.map Qm).prod:=by
 apply List.Perm.prod_eq' (η.map Qm); rw [List.pairwise_map]; exact (List.pairwise_map.mp v).imp_of_mem (fun {a b} ua ub hx=> region_meet _ _ _ X Pq _ _ le_rfl t _ _ hx (PostSupport.of (plot_U Y i k p w X t Q M qM Pq _ (g (List.mem_toFinset.mpr ua)))) (PostSupport.of (plot_U Y i k p w X t Q M qM Pq _ (g (List.mem_toFinset.mpr ub))))) -- order tune
abbrev pepperJ {E:Type*}(Y F:I→ E) :I→E:=fun i=>if i∈Q then F i else Y i
variable (U:Listos Y i w X K (Y.uv k) A)(hK:FarLedge K w)
include U hK
lemma returnJ_list (L:List I)(v:galaJ w L): (L.map (pepperJ Q A Qm)).prod=((Roots.wingX L Q).map Qm).prod * ((wingR L Q).map A).prod:=by
 induction L with
 | nil=> simp[Roots.wingX, Roots.wingR]
 | cons a l ih=>
    obtain ⟨b,w'⟩:=List.pairwise_cons.mp v; let V:= Roots.wingX l Q; let Z:=Roots.wingR l Q
    have e(x)(u:x∈l) : w a < w x:= b (w x) (List.mem_map_of_mem u)
    by_cases h : a∈Q
    · rw [List.map_cons,List.prod_cons,pepperJ,if_pos h,ih w',show Roots.wingX (a::l) Q=a:: V from (by simp only[V,Roots.wingX,List.filter_cons,h,↓reduceIte,decide_true]),show Roots.wingR (a::l) Q=Z from (by simp [Z,Roots.wingR,Roots.wingX,h])]
      rw[List.map_cons,List.prod_cons, mul_assoc]
    rw [List.map_cons,List.prod_cons,pepperJ,if_neg h,ih w',show Roots.wingX (a::l) Q=V from (by simp [V,Roots.wingX,h]), show wingR (a::l) Q=a::Z from (by simp [Z, Roots.wingR, Roots.wingX,h]),List.map_cons,List.prod_cons]
    change A a*((V.map Qm).prod*(Z.map A).prod)=(V.map Qm).prod* _; rw [←mul_assoc,←mul_assoc]; congr 1
    show A a*(V.map Qm).prod = (V.map Qm).prod* A a
    apply Commute.list_prod_right
    intro x u; obtain ⟨j,l,rfl⟩:=List.mem_map.mp u; obtain ⟨p',u⟩:= List.mem_filter.mp l; exact region_meet Y i k X Pq _ _ le_rfl t _ _ (ne_of_lt (e _ p')) (U.slit _ (hK _ _ (e _ p'))) (PostSupport.of (plot_U Y i k p w X t Q M qM Pq _ (of_decide_eq_true u)))
#print axioms region_coast
#print axioms stone_Z
#print axioms returnJ_list
#check modes_at
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
