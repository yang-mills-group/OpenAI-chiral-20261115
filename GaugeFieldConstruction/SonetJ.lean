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
variable {L: Side}{K:Teller SU.group}{R:Patch}{N m n B:Side}{d v x:ℝ}
variable {c:ChartRatio SU.group}
open Directory
namespace Onwards
variable (σ:I→Site N)(C:I→I→ℂ)
section
variable {K:Type}[AddCommMonoid K][Module ℂ K](U:Finset I→K)(B A:Finset I)
abbrev Duty (T:Finset I):= (i:T)→pipe_ζ σ i.val
abbrev FerryZ (x:Duty σ A):Finset I:= univ.image fun i:A=> (x i).val
abbrev Dl (x: Duty σ A):ℂ:=∏ i:A,C i.val (x i).val
lemma Dscale (x: Duty σ A)(h:A∈realm_C σ): Function.Injective (fun i:A=> (x i).val):=by
 intro i j p; refine Subtype.ext ((mem_filter.mp h).2 i.property j.property ?_); exact ((mem_filter.mp (x i).property).2.symm.trans ((congrArg σ p).trans (mem_filter.mp (x j).property).2)) -- tune
lemma Dsize (x:Duty σ A)(h:A∈realm_C σ):(FerryZ σ A x).card=A.card:= by rw[FerryZ,card_image_of_injective _ (Dscale _ _ x h), card_univ,Fintype.card_coe]
lemma D_σ (x:Duty σ A)(a:I)(t:a∈ FerryZ σ A x): σ a∈ A.image σ:=by obtain ⟨i,_,rfl⟩:=mem_image.mp t; rw[(mem_filter.mp (x i).property).2]; exact mem_image_of_mem σ i.property
lemma Dr_C (x:Duty σ A)(t:A∈realm_C σ):FerryZ σ A x∈ realm_C σ:=by
 refine mem_filter.mpr ⟨mem_univ _,fun i p j q w=>?_⟩
 obtain ⟨i,_,rfl⟩:=mem_image.mp p; obtain ⟨j,_,rfl⟩:=mem_image.mp q
 have hz: i=j:=Subtype.ext ((mem_filter.mp t).2 i.property j.property ((mem_filter.mp (x i).property).2.symm.trans (w.trans (mem_filter.mp (x j).property).2))); rw [hz]
def Verdante (b:Finset I):K:= ∑ a∈ realm_C σ,∑ x:Duty σ a, if FerryZ σ a x=b then Dl σ C a x • U a else 0
abbrev tip_f (u:Key I)(x:I):=∑ i:pipe_ζ σ x,C x (i.val)*u i.val
lemma Tributes (u:Key I): tip_f σ C u= toV_C σ C u:=by funext i; unfold tip_f toV_C; exact Finset.sum_coe_sort (pipe_ζ σ i) (fun j=> C i j * u j) -- orientation? toV_C σ C u i is sum C i j
lemma gem_P (u:Key I)(a:Finset I)(h:a∈realm_C σ):Mew.pine a (toV_C σ C u)=∑ x: Duty σ a,Mew.pine (FerryZ σ a x) u*Dl σ C a x:=by
 rw [← Tributes, Mew.pine, ←Finset.prod_coe_sort]
 change (∏ i:a,∑ j:pipe_ζ σ i.val,C i j*u j.val)=_
 rw [Fintype.prod_sum] -- tune sum.
 refine sum_congr rfl fun i _=>?_; rw [Mew.pine,FerryZ,Finset.prod_image (fun y _ z _ h'=>Dscale _ _ _ h h'),Dl,←prod_mul_distrib]; exact prod_congr rfl fun _ _=>mul_comm ..
lemma TellerJ (u:Key I): WritV σ (Verdante σ C U) u=WritV σ U (toV_C σ C u):=by
 unfold WritV Verdante; simp_rw [Finset.smul_sum]; rw[sum_comm]; apply sum_congr rfl; intro i p; rw [gem_P σ C _ _ p,Finset.sum_smul,sum_comm]; refine sum_congr rfl fun j _=>?_; rw [sum_eq_single_of_mem (FerryZ σ i j) (Dr_C _ _ j p)]; · rw[if_pos rfl,mul_smul]
 intro z _ t; rw[if_neg (Ne.symm t),smul_zero] -- smul if?
lemma Eleven : Verdante σ C U ∅=U ∅:=by
 rw [←ArcU_value σ (Verdante σ C U),TellerJ,show toV_C σ C 0=0 from (by unfold toV_C; simp only [Pi.zero_apply,mul_zero,sum_const_zero]; rfl),ArcU_value]
lemma Vout (x:Finset I)(h:x∉ realm_C σ):Verdante σ C U x=0:=by apply sum_eq_zero; intro i p; apply sum_eq_zero; intro j _; exact if_neg (fun t:FerryZ σ i j=x=>h (t ▸ Dr_C σ i j p))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
-- streamArc distribution equals Tip Roots.snow comparison using `TellerJ`. Out matches tilt. derive Law_C
lemma VLaw (G:Finset I→ E)(l:List I)(h:ψS σ l):Law_C σ C l (WritV σ G) (WritV σ (Verdante σ C G)):=by
 let F:= Fluid σ G
 have ht: River (WritV σ G):=(tip_bank _ _ fun i _=>lift_b i (G i)).1
 have hu:River (WritV σ (Verdante σ C G)):=(tip_bank _ _ fun i _=>lift_b i (Verdante σ C G i)).1
 have he :palm_R (WritV σ G) σ = WritV σ G:=by
    funext y; unfold palm_R WritV; refine sum_congr rfl fun i h=>?_ ; refine congrArg (Mew.pine i y • ·) ?_; exact (Fluid_p σ G (s:=Mew.Cue I i) (Ūm σ h)).trans (congrArg G (by simp [Mew.Cue])) -- rune
 have hw:= (κEmit σ C ht h).2 -- order
 refine ⟨ht,hu,?_⟩; intro i p; have hv:= hw i p; rw [he] at hv; rw [show WritV σ G∘ toV_C σ C=WritV σ (Verdante σ C G) from funext fun v=> (TellerJ σ C G v).symm] at hv; exact hv
lemma aloneX (F:Finset I→ E)(i:I): Verdante σ C F {i}=∑ j∈ Roots.pipe_ζ σ i,C j i • F {j}:=by
 have hv:= VLaw σ C F [i] (by simp [ψS]); have he:= hv.2.2 [i] (List.Sublist.refl _); have hp(E:Finset I→ E)(j:I): tipI (WritV σ E) [j]= E {j}:= (Fluid_p σ E (s:=[j]) (by simp [ψS])).trans (congrArg E (by simp))
 unfold fuelΦ at he; rw [hp,Roots.snow] at he; simp_rw [Roots.snow,hp] at he; exact he
end
end Onwards
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
