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
abbrev BandS:= Fin 3
variable (θ: BandS→ℕ)
abbrev GlyphKJ:= BandS→ℕ
-- separable set of locations; all query equipment stable.
def SailκJ(B:Type)(θ: BandS→ℕ):Type:= B × Σ j:BandS, Fin (θ j) × Fin 6
abbrev Netκ (B:Type):= B×BandS
local notation "Sail" T:max=> SailκJ T θ
variable {X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
instance PiltJ: Fintype (SailκJ X θ):=by unfold SailκJ; infer_instance
noncomputable instance ψPiltJ:LinearOrder (SailκJ X θ):= LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _) -- name tune [DecEq] coherence
-- REWRITE avoid θ not binding via notation!
def TolHouseJ (W:SailκJ X θ):X:= @Prod.fst X (Σ j:BandS, Fin (θ j) × Fin 6) W
abbrev TolTileJ(W:SailκJ X θ):Σ j:BandS, Fin (θ j) × Fin 6:= @Prod.snd X (Σ j:BandS, Fin (θ j) × Fin 6) W
abbrev TolJ(B:Type)(θ:BandS→ℕ): Directory (SailκJ B θ) (Netκ B):= ⟨fun i=>(TolHouseJ _ i,(TolTileJ _ i).1),fun i=> decide ((TolTileJ _ i).2.2=0),fun i=>i.2.val⟩
-- maybe DecidableEq Net uses BandS DecEq ok
abbrev TofJ (X:Type) (x:X)(j:BandS)(k:Fin (θ j))(u:Fin 6):SailκJ X θ:= @Prod.mk X (Σ j:BandS, Fin (θ j) × Fin 6) x ⟨j,k,u⟩
variable (x0:X) (W:Netκ X)
local notation "T1"=> TolJ X θ
#check TolHouseJ
lemma TofJ_out (d:BandS)(k:Fin (θ d))(u:Fin 6): TofJ θ X x0 d k u= TofJ θ X x0 d k u:=rfl -- tune args
@[simp] lemma Tol_H (d:BandS)(k:Fin (θ d))(u:Fin 6): TolHouseJ _ (TofJ θ X x0 d k u)= x0:=rfl
@[simp] lemma Tol_T (d:BandS)(k:Fin (θ d))(u:Fin 6): TolTileJ _ (TofJ θ X x0 d k u) =⟨d,k,u⟩:=rfl
def OrbitSailJ (v:X↪Z):SailκJ X θ ↪ SailκJ Z θ where
  toFun i:= TofJ _ Z (v (TolHouseJ θ i)) (TolTileJ _ i).1 (TolTileJ _ i).2.1 (TolTileJ _ i).2.2
  inj' p q h:=by
    have e:v (TolHouseJ θ p)= v (TolHouseJ θ q):=congrArg (TolHouseJ θ) h
    have H: TolTileJ θ p= TolTileJ θ q:= by exact congrArg (TolTileJ θ (X:=Z)) h
    exact Prod.ext (v.injective e) H
def KernelSailJ (u:X↪Z):Netκ X↪ Netκ Z:= Embedding.prodMap u (.refl _)
lemma EmbassyJ_sail (u:X↪Z):Embassy (TolJ X θ) (TolJ Z θ) (OrbitSailJ θ u) (KernelSailJ u):=⟨fun i=>rfl,fun i=>rfl,fun i=>rfl⟩
-- canonical slots
abbrev Bootκ (x:Netκ X)(k:Fin (θ x.2))(j:Fin 6) := TofJ θ _ x.1 x.2 k j
lemma φζJ (k:Fin (θ W.2))(j:Fin 6):(TolJ X θ).own (Bootκ θ W k j)=W:=rfl
def HelmJ (k:Fin (θ W.2)): (TolJ X θ).Pname W:=⟨Bootκ θ W k 0,rfl,by unfold TolJ Bootκ; dsimp; simp⟩ -- tune
abbrev ArmatureX (k:Fin (θ W.2))(j:Fin 6)(q:j≠0):(TolJ X θ).Vname W:=⟨Bootκ θ W k j,rfl,show decide (j=0) = false from decide_eq_false q⟩
private lemma helmPlug (W:Netκ X): Injective (HelmJ θ W):=by intro i j p; have h:= congrArg (TolTileJ θ∘Subtype.val) p; change (@Sigma.mk BandS (fun x=> Fin (θ x) × Fin 6) W.2 (i,0))=(@Sigma.mk BandS (fun x=> Fin (θ x) × Fin 6) W.2 (j,0)) at h; exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h).2) -- tune
lemma helmLoop (W:Netκ X): Surjective (HelmJ θ W):=by
 rintro ⟨p,h,e⟩; subst W; change decide ((TolTileJ θ p).2.2=0)=true at e
 refine ⟨ (TolTileJ θ p).2.1,Subtype.ext ?_⟩; change TofJ θ X (TolHouseJ θ p) _ (TolTileJ θ p).2.1 0=p; rw [← of_decide_eq_true e]; rfl -- orientation
noncomputable def Facingκ (W:Netκ X) : Fin (θ W.2) ≃ (TolJ X θ).Pname W:= Equiv.ofBijective _ ⟨helmPlug _ _,helmLoop _ _⟩
theorem facing_val (p:Fin (θ W.2)):(Facingκ θ W p).val = Bootκ θ W p 0:=rfl
variable (B0:BandS→ℕ)
-- Master & order proofs.
local notation "D1"=> Σ j:BandS, Fin (θ j) × Fin 6
abbrev Piκ (x:X): List (SailκJ X θ):= (Finset.univ.toList (α:=Σ j:BandS, Fin (θ j)×Fin 6)).map (fun i=> TofJ θ X x i.1 i.2.1 i.2.2)
abbrev Masterκ (u:List X): List (SailκJ X θ):= u.flatMap (Piκ θ)
lemma AtSlotκ (u:SailκJ X θ) : u∈ Piκ θ (TolHouseJ _ u):= List.mem_map.mpr ⟨ TolTileJ _ u, mem_toList.mpr (mem_univ _), rfl⟩
lemma Atκ (u:SailκJ X θ)(v:X)(p:u∈ Piκ θ v): TolHouseJ _ u =v:=by obtain ⟨W,p,rfl⟩:= List.mem_map.mp p; rfl
lemma Master_No (u:List X)(p:u.Nodup): (Masterκ θ u).Nodup:=by -- tune
 unfold Masterκ; apply List.nodup_flatMap.mpr
 constructor
 · intro i h; refine List.Nodup.map ?_ (Finset.nodup_toList _)
   exact fun a b h=> (congrArg (TolTileJ _) h)
 · exact List.Pairwise.imp (by intro a b p x h y; apply p; exact ((Atκ θ x a h).symm.trans (Atκ θ x b y))) p
abbrev HallJ (X:Type)[Fintype X][LinearOrder X]: List X:= univ.sort (· ≤ ·)
def SeamJ (X:Type)[Fintype X][LinearOrder X](θ:BandS→ℕ): List (SailκJ X θ) := Masterκ θ (HallJ X)
lemma Seam_No : ∀ (θ:BandS→ℕ), (SeamJ X θ).Nodup:= fun _ => Master_No _ _ (sort_nodup _ _) -- order
lemma Seam_All (p:SailκJ X θ):p∈ SeamJ X θ:=List.mem_flatMap.mpr ⟨ TolHouseJ θ p, by simp [HallJ], AtSlotκ _ _⟩
lemma Seam_Ord : ∀ (θ:BandS→ℕ), ((SeamJ X θ).map (TolHouseJ θ)).Pairwise (· ≤ ·) :=by -- tune
 intro θ; rw[List.pairwise_map]; apply List.pairwise_flatMap.mpr; constructor
 · intro i b; unfold Piκ; rw [List.pairwise_map]; exact List.pairwise_of_forall (fun _ _=>le_refl i)
 · exact List.Pairwise.imp (by intro i j h u p v q; rw [Atκ _ u i p,Atκ _ v j q]; exact h) (pairwise_sort _ _)
#print axioms Seam_All
#print axioms Seam_No
end kit
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
