import GaugeFieldConstruction.AracoJ
import GaugeFieldConstruction.SelvaR3
import GaugeFieldConstruction.DustJ
import GaugeFieldConstruction.CannonJ
import GaugeFieldConstruction.EraJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.OromoJ
import GaugeFieldConstruction.FrijaJ
import GaugeFieldConstruction.Gloss
import GaugeFieldConstruction.QuishJ
import GaugeFieldConstruction.NorasJ
import GaugeFieldConstruction.TributoJ
import GaugeFieldConstruction.AmusaJ
import GaugeFieldConstruction.SpursJ5
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
set_option maxHeartbeats 290000
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
section
open Mew Roots Connect Ing Ing.Iona CoeffArc Frugal
variable {I O A Y:Type}[Fintype I][LinearOrder I][Fintype O][LinearOrder O][DecidableEq A][Fintype A][DecidableEq Y][Fintype Y]
variable {L: Side}{K:Teller SU.group}{R:Patch}{N m n B:Side}{d vH x:ℝ}
variable {c:ChartRatio SU.group}
open Directory
namespace Onwards
open Larch Roots.GJ Ing Ing.Iona
variable {m B:Side}(Nkey:ℕ)(C:ℝ) {p:BudgetPoint}(σ:I→Seat N)(A:Finset I)
variable (w:I→I) (v:∀ i∈A,σ (w i)=σ i) (q:Set.InjOn w (A:Set I)) (s: ∀ i∈A,w i∉ A)
open Ione QuadClock TableF.Lenten.Bank Riant
section
open Ing Ing.Iona Ing.Ivey Ing.Ivey.ShoreQ Argos
variable {B₁:Type}[DecidableEq B₁]
variable {J A':Type}[Fintype J][LinearOrder J][DecidableEq A']
variable (D:Directory I B₁)(H:Directory J A')(σ:I→Seat (mid m B))(Φ:J→Seat (mid m B))(S:Sweep (mid m B))(e:I↪J)(g:B₁↪ A')(t:Embassy D H e g)
variable (k:Set I)(Θ:Finset I)(B':Finset J)(w:I→I)(wB:J→J)(A:Finset I)
variable (hx:Troop A w D)(hy:Troop B' wB H)
local notation "CΩ"=> Directory.Mantle e S
local notation "M4"=>mid m B
variable (hs:∀ i∈Θ,e i∈B'↔i∈ A)(hb:∀ i∈Θ,Φ (e i)=sh S (σ i))(w0:∀ i∈Θ, i∈ A→ wB (e i)=e (w i))(u:Rn D Θ)
variable (x:Key I)(px:Sigt Θ x)

lemma Lauren (i:I): CΩ x (e i)=Spire.payZ S (x i):=(etaμ _ _ _).trans (inkPay ..)

include px hs
lemma ControlJ: Sigt Θ (veilJ A x)∧ veilJ B' (CΩ x)= CΩ (veilJ A x):=by
 have he(i):veilJ B' (CΩ x) (e i)=CΩ (veilJ A x) (e i):=by
    unfold veilJ; by_cases h:i∈Θ; · rw[Lauren, show CΩ _ (e i)= _ from Lauren S e _ i]; simp only [hs i h,←inkPay]; split_ifs; rw [map_zero]; rfl
    rw[Lauren,show CΩ _ (e i)= _ from Lauren S e _ i, px i h]; split_ifs<;> simp only[← inkPay, map_zero]
 refine ⟨fun i h=> (by unfold veilJ; split; rfl; exact px i h),?_⟩
 funext i; by_cases t:i∈Set.range e; · obtain ⟨q,rfl⟩:=t; exact he _
 unfold veilJ Directory.Mantle; split_ifs; · rw[outsideμ _ _ _ t]
 rw[outsideμ _ _ _ t,outsideμ _ _ _ t]
section
include u hx hy hs hb w0 px
-- footprint qualification per-balance.Autom same inside worker assignments? require v and v'
variable (v1:∀ i∈A, σ (w i)=σ i)(v2:∀ i∈B', Φ (wB i)=Φ i)
include v1 v2
local notation "M_X" => toV_C σ (reflux A w) x
local notation "M_Y" => toV_C Φ (reflux B' wB) (CΩ x)
lemma crestJ: Sigt Θ M_X ∧ M_Y=CΩ M_X:=by
 let K:=Λpay S
 constructor; · intro i h; rw [Χpose σ A w v1]; -- tune
                rw [px i h,sum_eq_zero,sub_zero]; intro j t; by_cases v:j∈Θ; swap; · exact px _ v
                obtain ⟨p,rfl⟩:=mem_filter.mp t; exact (h (u _ (hx.τpos _ p))).elim -- provide p1.
 funext j; rw [Χpose Φ B' wB v2]; by_cases t:j∈Set.range e
 · obtain ⟨i,rfl⟩:=t
   change Directory.Mantle _ _ x _-_= _; rw [Lauren,show CΩ _ (e i)= _ from Lauren S e _ i, Χpose σ A w v1,←inkPay,←inkPay,map_sub] -- rewrite Lauren order
   have hz: K (∑ j∈ Stoop A w i,x j)=∑ j∈ Stoop B' wB (e i),CΩ x j:=by
     let D₀:= (Stoop A w i).filter fun j=> j∈Θ
     have hc:D₀.image e⊆ Stoop B' wB (e i):=by
        intro l h; obtain ⟨j,hb,xL⟩:=mem_image.mp h; subst l; obtain ⟨a,p⟩:=mem_filter.mp hb; obtain ⟨t,d⟩:= mem_filter.mp a; exact mem_filter.mpr ⟨(hs j p).mpr t, (congrArg _ d).trans (w0 _ p t).symm⟩
     rw [← sum_subset (s₁:=D₀) (filter_subset ..) ?_, ←sum_subset hc ?_, map_sum,sum_image]; · exact sum_congr rfl fun i _=>(etaμ e i (K ∘ x)).symm
     · exact e.injective.injOn
     · intro j hj x'; by_cases t:j∈Set.range e; swap; · exact outsideμ _ _ _ t
       obtain ⟨j,rfl⟩:=t; obtain ⟨a,h₁⟩:=mem_filter.mp hj; by_cases p:j∈Θ; swap; · rw [Lauren,px _ p,←inkPay,map_zero]
       let t:=(hs _ p).mp a; exact (x' (mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_filter.mpr ⟨t,e.injective (h₁.trans (w0 _ p t))⟩,p⟩,rfl⟩)).elim
     intro j p h; exact px _ (fun v=>h (mem_filter.mpr ⟨p,v⟩))
   exact congrArg _ hz.symm -- lane
 unfold Directory.Mantle; rw[outsideμ _ _ _ t,outsideμ _ _ _ t,sum_eq_zero,sub_zero]
 intro i x'; by_cases v:i∈Set.range e; swap; · exact outsideμ _ _ _ v
 obtain ⟨i,rfl⟩:=v; obtain ⟨a,h₀⟩:=mem_filter.mp x'; by_cases p:i∈Θ; swap; · rw[etaμ,comp_apply,px _ p,map_zero]
 exact (t ⟨w i,(h₀.trans (w0 _ p ((hs i p).mp a))).symm⟩).elim
end
section
variable {G:Type}[Fintype G][LinearOrder G]
omit hs
include hb px
lemma groundJ (f: Seat (mid m B)→G)(v:Key G):Sigt Θ (West3 S σ f x v)∧ East3 Φ f (CΩ x) v= CΩ (West3 S σ f x v):=by
 constructor; · intro i h; unfold West3 Reflect3; rw[px _ h,zero_mul]
 funext i; unfold East3 Reflect3; by_cases h:i∈Set.range e
 · obtain ⟨j,rfl⟩:=h; rw [Lauren, Lauren]; unfold West3 Reflect3; by_cases p:j∈Θ; swap; · rw[px _ p,zero_mul,←inkPay,map_zero,zero_mul]
   rw [←inkPay,←inkPay,map_mul,hb _ p]; -- Reflect3
   have ht(a:ℂ): Λpay S (cSignX (flipΘ S) a)=a:=by rw[inkPay]; change cSignX (flipΘ S) (cSignX (flipΘ S) a)=a; unfold cSignX; split_ifs; simp; rfl
   rw[ht]; rfl -- tune
 unfold Directory.Mantle; rw[outsideμ _ _ _ h,outsideμ _ _ _ h,zero_mul]
end
#print axioms crestJ
end
end Onwards
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
