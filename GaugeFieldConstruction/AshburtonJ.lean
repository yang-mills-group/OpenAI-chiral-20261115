import GaugeFieldConstruction.Trimbo4
import GaugeFieldConstruction.AracoJ
import GaugeFieldConstruction.SpursJ5
import GaugeFieldConstruction.Trimbo4
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
open Mew Roots Roots.Connect Ing Ing.Iona CoeffArc Frugal
section
variable {m B:Side}{I J A C:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]
variable [Fintype A][Fintype C][DecidableEq A][DecidableEq C]
namespace CoeffArc.Directory
-- induce from finite coordinate declarations. Naming scopes.Color generation.Needs $Full$ on all Principals of source. don't require image.F.P coherence if T0 differs.
variable (D:Directory I A)(H:Directory J C)(e:I↪J)(g:A↪C)(T:Sweep (mid m B))
open Ing Ing.Iona Roots GJ Ione QuadClock TableF.Lenten.Layout
variable (X:Finset I)(σ:I→Seat (mid m B))(σ':J→Seat (mid m B))(hS:∀ i∈X,σ' (e i)=sh T (σ i))
local notation "ΩS"=> (realm_C σ).filter (·⊆X)
local notation "w0"=>Λpay (N:=m) (B:=B) T
variable (x:Key I)(F:Finset I→RegBudget (mid m B))(Q:Finset J→RegBudget (mid m B))(hx:Sigt X x)
include hS
lemma PathJ (L:Finset I)(q:L⊆X): (L.image e)∈realm_C σ' ↔ L∈realm_C σ:=by
 rw [realm_C,realm_C,mem_filter,mem_filter]; simp only [mem_univ,true_and]; constructor
 · intro h i u j v t; apply e.injective; apply h (mem_image_of_mem e u) (mem_image_of_mem e v); rw [hS i (q u),hS j (q v),t]
 intro h i u j v t; obtain ⟨i,p,rfl⟩:=mem_image.mp u; obtain ⟨j,g,rfl⟩:=mem_image.mp v; rw[hS i (q p),hS j (q g)] at t; exact congrArg e (h p g ((boxA T).symm.injective t))
local notation "x'"=> Mantle (B:=B) (m:=m) e T x
include hx
lemma BothJ {E:Type}[AddCommMonoid E][Module ℂ E](F:Finset I→ E)(Q:Finset J→E): WritV σ F x=∑ i∈ΩS,pine i x • F i ∧ WritV σ' Q x'=∑ i∈ΩS,w0 (pine i x) • Q (i.image e):=by -- tune universe
 constructor
 · apply Eq.symm; refine sum_subset (s₁:=ΩS) (filter_subset ..) ?_; intro k v q
   have h:¬ k⊆ X:=fun h=>q (mem_filter.mpr ⟨v,h⟩); obtain ⟨j,p,g⟩:=not_subset.mp h; rw [show pine k x=0 from prod_eq_zero p (hx _ g),zero_smul]
 let G:= Finset.image (fun i:Finset I=>i.image e) ΩS; let Z:= x'; have hp : G⊆ realm_C σ':=by intro i k; obtain ⟨j,p,rfl⟩:= mem_image.mp k; obtain ⟨a,b⟩:= mem_filter.mp p; exact (PathJ e T X σ σ' hS j b).mpr a
 have hv:WritV σ' Q x'= ∑ i∈G,pine i Z • Q i:=Eq.symm (sum_subset hp (by
    intro i v q; by_cases h: i⊆X.image e
    · exfalso; let S:= X.filter (fun j=>e j∈ i); have E:S.image e=i:=by
         ext a; refine ⟨?_,?_⟩; · rintro u; obtain ⟨j,p,rfl⟩:= mem_image.mp u; exact (mem_filter.mp p).2
         intro u; obtain ⟨j,p,rfl⟩:=mem_image.mp (h u); exact mem_image.mpr ⟨j,mem_filter.mpr ⟨p,u⟩,rfl⟩
      exact q (mem_image.mpr ⟨S,mem_filter.mpr ⟨(PathJ e T X σ σ' hS S (filter_subset ..)).mp (E.symm ▸ v),filter_subset ..⟩,E⟩)
    obtain ⟨k,u,w⟩:=not_subset.mp h; rw [show pine i Z=0 from ?_,zero_smul]; apply prod_eq_zero u; change happyQ _ _ _= _; by_cases p:k∈ Set.range e
    · obtain ⟨j,rfl⟩:=p; rw[etaμ, comp_apply,hx _ (fun h=> w (mem_image_of_mem e h)),map_zero]
    exact outsideμ _ _ _ p )) -- tune indent
 rw [hv]; unfold G; rw [sum_image]; refine sum_congr rfl ?_; intro i K; rw [show pine (i.image e) Z= _ from pine_R e i _]; simp [Mew.pine,map_prod]
 exact Imageσ e _
lemma LinkQ (p:∀ L∈realm_C σ,L ⊆ X→ passingR (mid m B) T (F L) (Q (L.image e))): passingR _ T (WritV σ F x) (WritV σ' Q x') :=by
 obtain ⟨h,y⟩:= BothJ e T X σ σ' hS x hx F Q; rw [h,y]; intro j V; -- use inkC
 rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; refine sum_congr rfl fun i t=>?_; obtain ⟨u,v⟩:=mem_filter.mp t; exact (congrArg (w0 (pine i x) • ·) (p _ u v j V)).trans (inkC T _ _).symm
#print axioms LinkQ
end CoeffArc.Directory
-- tune sections
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
