import GaugeFieldConstruction.AshburtonJ
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
lemma LinkKQ (Z:Finset I→ForceBudget (mid m B))(Z':Finset J→ForceBudget (mid m B))(u:∀ L∈realm_C σ,L⊆X→passingF _ T (Z L) (Z' (L.image e)))(p:Sigt X x): passingF _ T (WritV σ Z x) (WritV σ' Z' (Mantle (m:=m) (B:=B) e T x)):=by
 obtain ⟨h,y⟩:= BothJ e T X σ σ' hS x p Z Z'; rw [h,y]; intro j V h -- shadow
 rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; refine sum_congr rfl fun i t=>?_; obtain ⟨s,v⟩:=mem_filter.mp t; exact (congrArg (w0 (pine i x) • ·) (u _ s v j V h)).trans (inkC T _ _).symm
omit hS
-- coefficient detection by inclusion finite.
private lemma RadarQ (S:Finset I)(j:S∈ realm_C σ)(R:Finset I)(v:R⊆ S): R∈realm_C σ:= mem_filter.mpr ⟨mem_univ _,fun _ a _ b t=>(show Set.InjOn σ S from (mem_filter.mp j).2) (v a) (v b) t⟩ -- tune
variable (L:Finset I) (pL:L∈realm_C σ)(u:L⊆ X)
private lemma hallM_O (R:Finset I)(p:R∈ realm_C σ): (realm_C σ).filter (·⊆R)= R.powerset:=by ext i; rw[mem_filter,mem_powerset]; exact and_iff_right_of_imp (RadarQ σ R p i) -- tune
abbrev chainγ (σ:I→Seat (mid m B)):=(WritV σ F)
private abbrev leaf (S:Finset I)(i:I):ℂ:= if i∈ S then 1 else 0
lemma Sigt_leaf {S:Finset I}(p:S⊆ X): Sigt X (leaf S):= fun _ x=> if_neg (fun v=>x (p v))
private lemma GatherQ {E:Type}[AddCommGroup E](L:Finset I)(F Q:Finset I→E)(p:∀ i:Finset I,i⊆L→∑ k∈i.powerset,F k=∑ k∈i.powerset,Q k): F L=Q L:=by
 induction h:L.card using Nat.strong_induction_on generalizing L with
 | h l ih=>
    have g := p L (Subset.refl _); let A:=L.powerset
    have v:L ∈ A:= mem_powerset.mpr (Subset.refl _); let U:=A.erase L; have e: ∑ j∈ U,F j=∑ j∈U,Q j:=by
       apply Finset.sum_congr rfl; intro j p'; obtain ⟨pJ,p'⟩:= mem_erase.mp p'; have ht:j ⊂ L:=Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp p',pJ⟩ -- tune
       exact ih _ (h ▸ card_lt_card ht) j (fun i t=>p i (t.trans ht.le)) rfl
    have H: F L+∑ j∈ U,F j=Q L+∑ j∈U,Q j:=by rw[add_sum_erase _ _ v,add_sum_erase _ _ v,g] -- parse
    rw [e] at H; exact add_right_cancel H
include hS pL u
lemma Power_KQ (Z:Finset I→ForceBudget (mid m B))(Z':Finset J→ForceBudget (mid m B))(k:∀ x:Key I,Sigt X x→ passingF _ T (WritV σ Z x) (WritV σ' Z' (Mantle (m:=m) (B:=B) e T x))):passingF _ T (Z L) (Z' (L.image e)):=by
 intro j V v; apply GatherQ L (fun L=> Z' (L.image e) _ _) (fun L=> suit_Y T (Z L j V))
 intro K c; let z:= leaf K; have hc: Sigt X z:=Sigt_leaf X (c.trans u)
 have h:= k z hc j V v; obtain ⟨p,y⟩:= BothJ e T K σ σ' (fun i t=>hS _ (u (c t))) z (Sigt_leaf K (Subset.refl _)) Z Z' -- order
 have g(j:Finset I)(p:j∈K.powerset): pine j z=1:=Finset.prod_eq_one (fun i t=> if_pos ((mem_powerset.mp p) t))
 have v':= hallM_O σ K (RadarQ σ _ pL _ c); rw [v'] at p y; rw[p,y, Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum] at h
 refine Eq.trans ?_ (h.trans ?_) -- tune
 · apply sum_congr rfl; intro i h; rw [g _ h,map_one,one_smul]
 apply sum_congr rfl; intro i h; rw[g _ h,one_smul]
lemma Power_RQ (Z:Finset I→RegBudget (mid m B))(Z':Finset J→RegBudget (mid m B))(k:∀ x:Key I,Sigt X x→ passingR _ T (WritV σ Z x) (WritV σ' Z' (Mantle (m:=m) (B:=B) e T x))):passingR _ T (Z L) (Z' (L.image e)):=by
 intro j V; apply GatherQ L (fun L=> Z' (L.image e) _ _) (fun L=> suit_Y T (Z L j V))
 intro K c; let z:= leaf K; have hc: Sigt X z:=Sigt_leaf X (c.trans u)
 have h:= k z hc j V; obtain ⟨p,y⟩:= BothJ e T K σ σ' (fun i t=>hS _ (u (c t))) z (Sigt_leaf K (Subset.refl _)) Z Z' -- order
 have g(j:Finset I)(p:j∈K.powerset): pine j z=1:=Finset.prod_eq_one (fun i t=> if_pos ((mem_powerset.mp p) t))
 have v':= hallM_O σ K (RadarQ σ _ pL _ c); rw [v'] at p y; rw[p,y, Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum] at h
 refine Eq.trans ?_ (h.trans ?_) -- tune
 · apply sum_congr rfl; intro i h; rw [g _ h,map_one,one_smul]
 apply sum_congr rfl; intro i h; rw[g _ h,one_smul]
#print axioms Power_KQ
end CoeffArc.Directory
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
