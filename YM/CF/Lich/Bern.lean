import YM.CF.Lich.Siren
import YM.CF.Lich.Zee
import YM.CF.Lich.Wash
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
-- Holder Site energy.H.Near owner expanded pd.. optional Path group exact
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
local notation "P₀"=> mid N B
open Font
variable (d k r' b:ℕ)
-- d actual radius blip (variable parent r'), b extent for site, r near cutoff r₁ after L.H.Sem.
abbrev Tee:= ((portA (X:=P) (B:=B) (Stores.till x)):Finset (Support (Domain P B)))ᶜ
def queen (Y':Palot.leaf (Site m)):= Tee (x:=x)|>.filter fun v=> halo k (hatY S v)= Y'.val
lemma queen_non(u:Support m')(v:u∈Tee (x:=x)): u.Nonempty:=by
 apply card_pos.mp; have hp:(Stores.till x)<u.card:=by simpa [Tee,Hest.portA] using v
 omega
def legS(t:Palot.leaf (Site m)) : ℂ := ((massX A U t+shardy A U k t:ℝ):ℂ)+ ∑ i∈queen (x:=x) (S:=S) k t,(A.LawQ i YY- A.LawQ i V)
def legA(t:Palot.leaf (Site m)): Op (Single P₀):= ∑ i∈queen (x:=x) (S:=S) k t,A.Fame i V
def docS(i:Site m):ℂ:= if i∈ U.key.dome r' then 0 else burnS A U V W i
def docA(i:Site m): Op (Single P₀):= if i∈U.key.dome r' then 0 else maskS A V i
variable (r)
def onyx(O:Hos S r):ℂ:= soreG A U O.val + ∑ i∈ O.val.dome r',burnS A U V W i
def hush(O:Hos S r): Op (Single P₀):= ∑ i∈ O.val.dome r',maskS A V i

lemma royalty {E:Type*}[AddCommMonoid E](Rw:Support m'→E): ∑ i:Palot.leaf (Site m),∑ j'∈queen (x:=x) (S:=S) k i,Rw j'= ∑ j'∈Tee (x:=x),Rw j':=by
 unfold queen; simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i p; let f:=halo k (hatY S i); have he:f.Nonempty:= ((queen_non i (x:=x) p).image (S.ratio.parent)).mono (halo_subset ..); rw [sum_eq_single (⟨f,he⟩:Palot.leaf (Site m))]; · exact if_pos rfl
 · intro b _ h; exact if_neg (fun p=> h (Subtype.ext p.symm))
 simp
variable {d}
lemma spoke (p:r'≤r){E:Type*}[AddCommMonoid E](F':Site m→E): (∑ i∈blip S U.key r,∑ j'∈ i.val.dome r',F' j')+(∑ i,if i∈U.key.dome r' then 0 else F' i)= ∑ i,F' i:=by
 have hh: Set.PairwiseDisjoint ((blip S U.key r): Set (Hos S r)) fun i=>i.val.dome r' := fun i z j' v l'=> Disjoint.mono (farther p) (farther p) (stem_d S U.key z v l') -- canonical
 rw [← sum_biUnion hh,← Reine.allP U.key r r',paid_r (U.key.dome r') (fun _=>0) F']; simp only [sum_const_zero,zero_add,sum_add_sum_compl]
lemma highness {C D c E Q D':ℝ}(hp:r'≤r)(ht:(j+104)*radiusB x+10≤r) (h:T.up.Bounds T.high C D c)(hf:T.down.Bounds T.low E Q D')(hr:Ready T x)(hv:1000≤ radiusB x)(z:Portus A U): (∑ i∈blip S U.key r,onyx r A U V W r' i)+ (∑ i: Site m,A.docS U V W r' i)+(∑ i:Palot.leaf (Site m), legS A U V k i)=plaza A U V W r - arcD T x U:=by -- order r r'
 unfold onyx docS legS; rw [grand_g A U V W ht]; rw [sum_add_distrib, sum_add_distrib] -- inspect
 have he:=spoke r U r' hp (burnS A U V W); rw [royalty k, ←he]; have hh: (∑ i:Palot.leaf (Site m), ((massX A U i+shardy A U k i:ℝ):ℂ))=((taxT A U+tollG A U:ℝ):ℂ):=by rw [←Complex.ofReal_sum,sum_add_distrib,summons A U hr hv z,quarry A U k h hf]
 rw [hh, sum_sub_distrib]; unfold posy mintB Tee portA; simp only [Complex.ofReal_add,Complex.ofReal_sum]; abel
lemma laus {a f c:ℝ}{D':nomA N P B → Op (Single (mid N B))}(v:r'≤r)(h: Ind G A.Fame a f c n D') : (∑ i∈blip S U.key r, hush r A V r' i) +(∑ i:Site m,docA A U V r' i)+(∑ i:Palot.leaf (Site m),legA A V k i)= D' V.val:=by
 unfold hush docA; rw [spoke r U r' v,chronological A V]; unfold legA led; rw [royalty k,sum_add_sum_compl,h.meet V] -- tune names order
end Muster
end YM.CF.Lich
