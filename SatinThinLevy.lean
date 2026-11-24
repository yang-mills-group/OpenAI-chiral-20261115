import SatinThinCitizen
import YM.SU5.FiniteGaugeData.Tapestry.Levels
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
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v t m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "K"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
-- fatAt including clasp (radius can be different across lifts).
def Levy (P:Preparation)(ℓ:ℕ):ℕ:= Advance.gross (aliasLaw P) (distanceLaw ℓ) P.R.J+nearZero (aliasLaw P)+distanceLaw ℓ+reserve P ℓ
abbrev grossAt(P:Preparation)(ℓ:ℕ):= Advance.gross (aliasLaw P) (distanceLaw ℓ) P.R.J
abbrev fatAt {n:Side}(x:Site n)(t: ℕ): Support (More n):=Lattice.halo t {node x}
abbrev grantRadius(P:Preparation)(ℓ:ℕ)(m:ℕ):=P.R.L.val*(m+grossAt P ℓ)
lemma mansion_L (G:Ratio P' V)(h:Odd G.count.val)(x:Site P'): node (heel G x)=(ratio G).embed (node x):=by unfold heel; rw [embed_node G h]; simp
variable (x:Site (side Y i f))(p:Satin.PairIdx Y f i k)
lemma padding : Advance.padded (Gξ f) (fatAt x m) ((L).val*grossAt P ℓ) ⊆ fatAt (Hove.heel (Gξ f) x) (grantRadius P ℓ m):=by
 intro j z; obtain ⟨g,h,t⟩:=halo_spec.mp z; obtain ⟨a,b,rfl⟩:= Finset.mem_image.mp h; let A:= Gξ f; have hx:separation (node x) a ≤ m:=by obtain ⟨a',g,v⟩:=halo_spec.mp b; exact Finset.mem_singleton.mp g ▸ v
 rw [fatAt,mansion_L (Gξ f) P.R.odd_side]; apply halo_spec.mpr; refine ⟨_, Finset.mem_singleton_self _,(separation_triangle _ _ _).trans ((add_le_add ((scaled_root (ratio A) (node x) a).trans (show A.count.val *_ ≤ (L).val*m from Nat.mul_le_mul_left _ hx)) t).trans_eq (Nat.mul_add ..|>.symm))⟩
include p
lemma weight (z: ℕ){X:Mark (side Y i f)}{S:Support (More (side Y i f))}(v:AtSupport false S X): AtSupport false (Advance.padded (Gξ f) S ((L).val*grossAt P ℓ)) (ascender Y f i k X):=by
 have a:= (fullness Y i k p.1).cap_grant; obtain ⟨l'⟩:= a.grant f p.2; obtain ⟨_,_,_,t,_⟩:= l'.cap
 have h:= surround (Gξ f) (patternA Y f i k) D (patternQ Y f i k).val ((((Y.voyage i).X (Y.uv k)).gram (f+1))).J.M P.R.odd_side Chi.canonical P.J.d ((((Y.voyage i).X (Y.uv k)).gram (f+1))).beta _ (Journey.legal P) t.bill (a.branch f p.2) l'.legal.1 l'.legal.2 _ v (Journey.tissue Y i f) (a.aligned f p.2);
 rw [(show (patternA Y f i k).patch.J=P.R.J from a.radius f p.2)] at h; exact h
omit p
lemma weight_all {z:Mark (side Y i f)}(v:AtSupport false univ z)(p:Satin.PairIdx Y f i k): AtSupport false univ (ascender Y f i k z):=(weight Y i k p 0 v).mono (subset_univ _)
variable {I:Type} [DecidableEq I]
def Beyond {n:Side}(P:Preparation)(ℓ:ℕ)(p:I→ Site n)(a:ℕ):Prop:=∀ i j:I,i≠j→2*a+4*Levy P ℓ<separation (node (p i)) (node (p j))
lemma heel_range {o:I→Site (side Y i f)}(v:Beyond P ℓ o a) : Beyond P ℓ (heel (Gξ f) ∘ o) (grantRadius P ℓ a):=by
 intro i j t; simp_rw [Function.comp_apply,mansion_L (Gξ f) P.R.odd_side,Laic.emptio]; apply lt_of_le_of_lt ?_ (show (L).val * _ < (L).val * _ from Nat.mul_lt_mul_of_pos_left (v i j t) (L).property)
 have h:(L).val≥3:=P.R.coarse; have u:Levy P ℓ≥grossAt P ℓ:=by simp only [Levy,grossAt]; omega
 let Dξ:= Levy P ℓ; have he: 2*((L).val*grossAt P ℓ)+4*Dξ≤ (L).val* (4*Dξ):=by
    change _ ≥ _ at u; have hp:2 ≤ (L).val:=by omega
    have hv:(L).val*grossAt P ℓ≤(L).val*Dξ:= Nat.mul_le_mul_left _ u; nlinarith -- maybe
 change 2*((L).val*(a+grossAt P ℓ))+4*Dξ≤_; linarith -- need cast RHS ratio.count adjust
variable {f' : Mark (side Y i f)}
lemma beyond_pay {o:I→Site (side Y i f)}(v:Beyond P ℓ o a)(x y:I)(u:x≠y){i' j: Site (More (side Y i f))}(g:i'∈ fatAt (o x) a)(l:j∈fatAt (o y) a) : 2*(nearZero (aliasLaw P)+ distanceLaw ℓ)< separation i' j:=by
 have ht(T:Site (Ω f))(X): X∈ fatAt T a→ separation (node T) X≤ a:=fun t=>by obtain ⟨z,p,w⟩:=halo_spec.mp t; exact Finset.mem_singleton.mp p ▸ w
 have he:=v x y u; have hk:=ht _ _ g; have hn:=ht _ _ l; have h₁:=separation_triangle (node (o x)) i' j; have h₂:=separation_triangle (node (o x)) j (node (o y)); rw [separation_comm j] at h₂; unfold Levy at he; omega
variable (o:I→Site (side Y i f))(F:I→ Mark (side Y i f))(u:Beyond P ℓ o a)(vF:∀ i,AtSupport false (fatAt (o i) a) (F i))
def locale (l:List I):= l.toFinset.biUnion (fun i=> fatAt (o i) a)
omit [DecidableEq I] in
lemma receipt_word {n:Side}{o:I→Support (More n)}{F:I→Mark n}(p:∀ i,AtSupport false (o i) (F i))(l:List I){S:Support (More n)}(q:∀ i∈l,o i⊆ S) : AtSupport false S (l.map F).prod:=by induction l with |nil=>exact AtSupport.oneM _|cons i l ih=> exact ((p i).mono (q i (List.mem_cons_self ..))).mulM (ih fun j h=> q j (List.mem_cons_of_mem _ h)) -- map cons definal
include vF u p
lemma follow_cost(l:List I)(v:l.Nodup): ascender Y f i k (l.map F).prod = (l.map (ascender Y f i k ∘ F)).prod:=by
 induction l with
 | nil=> exact ascendUnit Y f i k p
 | cons j l ih=> obtain ⟨t,v⟩:=List.nodup_cons.mp v; rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,ascendSep Y f i k p (vF j) (receipt_word vF l (S:=locale Y i o (a:=a) l) (fun i w=>fun x V=> mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr w,V⟩)),ih v]; rfl; intro x h y q; obtain ⟨j',q,h'⟩:=mem_biUnion.mp q; exact beyond_pay Y i u j j' (fun v=>t (v.symm ▸ List.mem_toFinset.mp q)) h h'
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
