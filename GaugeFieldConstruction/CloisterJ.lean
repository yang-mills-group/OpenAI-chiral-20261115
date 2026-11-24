import GaugeFieldConstruction.BonbonJ
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
local notation "B"=> P.block
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
open XGarden XGarden.Ledger XGarden.Echo XGarden.MastTin XGarden.Shield
open XGarden.MastTin.MintB Taxi
-- sector support top only (two arbitrary modes/wrong-spin echo eligible). never used for ascender. Local both Pane arguments.
variable {R:BudgetPoint}{S:Hubber N}{m h c d:ℝ}{o:Seat N}
def dryHn (M:Torches N): Mark N:=toMark (Ion M)
private lemma marketSafe{U:Paper N}(T:TrackD R S h U c): PostSupport false S (toMark (marketD U)):=by
 let v:= val_T T; obtain ⟨V,p,h⟩:=T; let Y:= modesIn N S
 have ht(t:Wa N){i:Fields N}: Fock.Sector Y false ((U t i.1) • dot_Q t):=by
    by_cases h:DomainP S t; swap; · rw[(p t).2 h]; change Fock.Sector Y false ((0:ℂ) • dot_Q t); rw[zero_smul]; exact Sector.zero _ -- name
    refine Sector.scale ?_ _; cases t with
    | none=> exact .one
    | some a=>
       obtain ⟨p,t,k⟩:=a
       have hv:t∈modesIn N S:= (modes_at ..).mpr h.1; have hx:k∈ modesIn N S:= (modes_at ..).mpr h.2; cases p
       · exact (Sector.down t hv).mul (Sector.up k hx)
       exact (Sector.up t hv).mul (Sector.down k hx)
 exact ⟨Env.along v measurable_fst,fun i j u _=>sum_congr rfl (fun x _=>congrArg (· • dot_Q x) ((p x).1.2.2.1 _ _ u)),fun i=> Sector.sumS (S:=Y) _ _ (fun t _=>ht t)⟩
lemma curtainTopJ {V:Torches N}(p: Inscribe R o h m V c d) (v:∀ i:Hubber N,V.2 i≠0→ i⊆S)(e:Pach o⊆S): PostSupport false S (dryHn V):=by
 obtain ⟨p, V',t,u⟩:=p; let C (i:Hubber N):ℝ:=if V.2 i=0 then 0 else V' i; have hg: TrackD R S h (∑ i:Hubber N, V.2 i) (∑ i:Hubber N,C i):=by
    refine track_sum _ _ _ ?_; intro i _; unfold C; split
    next h=> rw [h]; exact track_zero
    next h=> exact track_o (t i).1 (v _ h)
 exact (marketSafe (track_o p e)).addM (marketSafe hg)
lemma curtainH_J {V:Torches N}(p: Inscribe R o h m V c d): PostSupport false univ (dryHn V):=curtainTopJ p (fun _ _=> subset_univ _) (subset_univ _)
lemma rooflessJ {V:Torches N}(r:ℕ)(p:Inscribe R o h m (trunc_T r V) c d)(e:Lattice.halo r {o} ⊆ S)(x:Pach o⊆ S): PostSupport false S (dryHn (trunc_T r V)):=by
 obtain ⟨T,Q⟩:=p; apply curtainTopJ ⟨T,Q⟩ _ x
 obtain ⟨q,u,b⟩:= Q; intro i v j g
 have ht:i.card≤r:=by change (if i.card≤ r then V.2 i else 0)≠0 at v; by_contra w; rw[if_neg w] at v; exact v rfl
 obtain ⟨iv,t⟩:= (show Dock o i from not_not.mp (fun h=>v ((u i).2 h)))
 apply e; exact halo_spec.mpr ⟨_,mem_singleton_self _,(t.lim _ iv _ g).le.trans ht⟩
#print axioms curtainTopJ
#print axioms rooflessJ
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
