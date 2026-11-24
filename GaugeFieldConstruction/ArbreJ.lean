import GaugeFieldConstruction.SailηJ
import GaugeFieldConstruction.TejasJ
import GaugeFieldConstruction.BanjoθJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.PirangaJ
import GaugeFieldConstruction.PeakJ
import GaugeFieldConstruction.GypA
import GaugeFieldConstruction.StepWorthJ
import GaugeFieldConstruction.OrbisJ
import GaugeFieldConstruction.YieldRampJ
import GaugeFieldConstruction.Budgets
import GaugeFieldConstruction.FairNumJ
import GaugeFieldConstruction.CapriceJ
import GaugeFieldConstruction.NurmaJ
import GaugeFieldConstruction.SamarsJ
import GaugeFieldConstruction.Norwood
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
variable (i k s f j:ℕ) {m n:ℕ}
open Papal AUbard Directory
local notation "η_"=>Y.uv k
local notation "Pq"=>P.R.L
variable (D C t:ℕ→ℝ) (α c τ u0:ℝ)(Nkey:ℕ) -- price scale functions C unused.
open XGarden XGarden.Ledger XGarden.Echo XGarden.MastTin XGarden.Shield XGarden.MastTin.MintB Ing Ing.Iona Ing.Ivey Ing.Ivey.ShoreQ
open Sour Sour.SliceRoof SeasonH Fock.Wosk TableF TableF.Lenten TableF.Lenten.Layout
open Oath Wray
local notation "µs" s:max=> Papal.gram Y s i k
variable (K :ℕ→ℝ)
local notation "NY_" s:max=> Papal.count Y s i
local notation "Zmat" s:max=> KeyUp ((Papal.gram Y s i k).p)
local notation "Γω" s:max=> (PlaceOf Y i k s).step P.V
local notation "Φ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "δp"=> P.R.L
local notation "ρp" => reserve P ℓ
local notation "Tq" s:max=> Papal.count Y s i
open Riant Onwards WorldJ
section kit
variable (θ:BandS→ℕ){X Z: Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable (e:X↪Z)
open Argos
section enroll
local notation "eι"=> OrbitSailJ θ e
variable (f:List X)(g:List Z)
lemma πslot (u:X): Piκ θ (e u)=(Piκ θ u).map (eι):=by unfold Piκ; simp only [List.map_map]; rfl
lemma mastSub (p:(f.map e).Sublist g): ((Masterκ θ f).map eι).Sublist (Masterκ θ g):=by
 have he : Masterκ θ (f.map e)=(Masterκ θ f).map eι:=by clear p; induction f with
                                                                      | nil=>rfl
                                                                      | cons i l ih=> simp only [List.map_cons]; unfold Masterκ; rw[List.flatMap_cons,List.flatMap_cons,List.map_append,πslot]; congr 1; -- ih scope p? dependent
 rw[←he]; exact p.flatMap _
-- get Sublist by sorted≥ & nodup
lemma Esorts (v: StrictMono e): ((HallJ X).map e).Sublist (HallJ Z):=by
 refine List.sublist_of_subperm_of_pairwise (List.Nodup.subperm ((sort_nodup univ (· ≤ ·)).map e.injective) ?_) (List.pairwise_map.mpr (List.Pairwise.imp (fun a=> v.monotone a) (pairwise_sort _ _))) (pairwise_sort univ (· ≤ ·))
 intro i p; simp [HallJ]
#check sort_nodup
#check pairwise_sort
lemma FoΚ (v: StrictMono e)(Θ:Finset (SailκJ X θ)): FilJ (OrbitSailJ θ e) Θ (SeamJ X θ) (SeamJ Z θ):=by
 let X':= SeamJ X θ; let Y:= SeamJ Z θ
 let E:= OrbitSailJ θ e; have hp: (X'.map E).Sublist Y:= mastSub θ e _ _ (Esorts e v) -- tune
 let Ξ:=Θ.image E; let V:= X'.filter (·∈Θ); let W:= Y.filter (·∈Ξ); change V.map E=W
 have ht:(V.map E) = (X'.map E).filter (·∈Ξ):=by unfold V; rw[List.filter_map]; congr 2; funext i; simp [Ξ]
 rw[ht]; unfold W; apply (hp.filter _).eq_of_length; apply List.Perm.length_eq
 apply (List.perm_ext_iff_of_nodup ((List.Nodup.filter _) ((Seam_No (X:=X) θ).map E.injective)) ((List.Nodup.filter _) (Seam_No (X:=Z) θ))).mpr; intro i; simp only[List.mem_filter,List.mem_map,decide_eq_true_eq]; constructor
 · exact fun w=>⟨Seam_All θ i,w.2⟩
 rintro ⟨_,t⟩; obtain ⟨j,p,rfl⟩:= mem_image.mp t; exact ⟨⟨j, Seam_All θ j,rfl⟩, t⟩
lemma FtPodJ (v: StrictMono e) (l:List (SailκJ X θ)) : skimT _ (SeamJ Z θ) (l.map (OrbitSailJ θ e))=(skimT _ (SeamJ X θ) l).map (OrbitSailJ θ e):=by
 unfold skimT; simp_rw [← List.mem_toFinset, show (l.map (OrbitSailJ θ e)).toFinset=l.toFinset.image (OrbitSailJ θ e) from (by ext i; simp)]; exact (FoΚ θ e v l.toFinset).symm -- tune decidable filter
-- charges cardinal per location
abbrev ωWcap (θ:BandS→ℕ): ℕ:= Fintype.card (Σ i:BandS, Fin (θ i) × Fin 6)
lemma νLoka (X:Type)[Fintype X][LinearOrder X](t:X): (univ.filter fun a:SailκJ X θ=> TolHouseJ _ a=t).card ≤ ωWcap θ:=by
 refine le_trans ?_ (show _ ≤ ωWcap θ from card_univ.le); apply card_le_card_of_injOn (TolTileJ θ) (fun _ _=> mem_univ _) -- tune
 exact fun a p b q x=> Prod.ext (((mem_filter.mp p).2).trans ((mem_filter.mp q).2).symm) x
-- filtration. single date per gap.Surge: Lane color 0 means blank event; issue always full pc group.
abbrev BoardDate (X:Type):= ℕ → Netκ X→ Fin 6
def χBty (B:BoardDate X)(s:ℕ)(u:SailκJ X θ):Prop:= (TolTileJ _ u).2.2=B s ((TolJ X θ).own u) ∧ B s ((TolJ X θ).own u) ≠0
noncomputable def BoltDate (B:BoardDate X)(s:ℕ):List (SailκJ X θ):= (SeamJ X θ).filter fun i=>χBty θ B s i
lemma voJ (B:BoardDate X)(s:ℕ)(u:SailκJ X θ):u ∈ (BoltDate θ B s).toFinset ↔ χBty θ B s u:= by simp only[List.mem_toFinset,BoltDate,List.mem_filter,Seam_All,and_self,decide_eq_true_eq,true_and]
def KtpJ (p:SailκJ X θ):SailκJ X θ:= Bootκ θ ((TolJ X θ).own p) (TolTileJ _ p).2.1 0
lemma KTpt (x:Netκ X)(w:Fin (θ x.2))(j:Fin 6):KtpJ θ (Bootκ θ x w j)= Bootκ θ x w 0:=rfl
lemma TkTroop (B:BoardDate X)(s:ℕ)(q:ℕ):Troop (BoltDate θ B s).toFinset (KtpJ θ) (TolJ X θ):=by
 constructor
 · intro i h; obtain ⟨p,h⟩:= (voJ ..).1 h; exact (show decide ((TolTileJ θ i).2.2=0)=false from decide_eq_false (p ▸ h))
 · intro p _; rw [show KtpJ θ p= _ from rfl]; exact (HelmJ θ _ (show Fin (θ ((TolJ X θ).own p).2) from (TolTileJ _ p).2.1)).property.2
 · intro i h; exact φζJ ..
 intro i p j h y
 obtain ⟨a,p⟩:= (voJ ..).1 p; obtain ⟨b,h⟩:= (voJ ..).1 h
 have o: (TolJ X θ).own i=(TolJ X θ).own j:=by rw [show (TolJ X θ).own i= (TolJ X θ).own (KtpJ θ i) from rfl, show (TolJ X θ).own j= (TolJ X θ).own (KtpJ θ j) from rfl,y]
 let Q:SailκJ X θ→ Fin 6→ SailκJ X θ:= fun i j=> TofJ θ X (TolHouseJ _ i) _ (TolTileJ _ i).2.1 j
 change Q (KtpJ θ i) ((TolTileJ _ i).2.2)= Q (KtpJ θ j) ((TolTileJ _ j).2.2)
 rw [a,b,y,o]
#print axioms TkTroop
end enroll
end kit
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
