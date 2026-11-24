import YM.CF.Facet.Sole
import YM.CF.Facet.North
import YM.CF.Facet.Gust
import YM.CF.Facet.Law
import YM.CF.Facet.Arc
import YM.CF.Facet.Hemp
import YM.CF.Facet.Horn
import YM.CF.Cour.Culm
import YM.CF.Tarn.Sold
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Facet
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff  InnerProductSpace
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
local notation "G₅"=> SU.group
open Cube Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec
variable {n B m X: Side}{T: Roam m X B}{G: Ratio (CSide m B) (CSide X B)}{p:Tube G₅ T}
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{A:Finset (Site f)}{o:Site c}{s:Signed}{b:Site c}{x e d β a r σ w:ℝ}{l k:ℕ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {F:Tab T}{C V R Z η:ℝ}{Q: Msca m X B G e}{Φ:nomA m X B→ ℂ}{i:Site (More (CSide m B))}
variable{U U':Config G₅ (More (CSide m B))}{t:ℕ}
open Levier
variable{u:ℝ}{q:Chi}{h:0<e}
open Stationary Push.Loops
open Stationary Push.Loops
variable{α:ℝ}{J:ChartRatio G₅}
def snowG(G:Ratio (CSide m B) (CSide X B))(p:Pressure.Tube G₅ T)(q:Chi)(x u α d:ℝ)(l:ℕ)(Q:Msca m X B G e)(h:0<e) (F:Tab T):FileM (More (CSide m B)) G₅:= franc p x q d u l Q h F+tripK p q x α d l F
variable (H:Thu p x u l Q h K k η C a Z V R Φ)
include H
lemma snore : let f:= snowG G p q x u α d l Q h; let U:=fun i=>Arena.aria fun P=> f P i; LayerP (CSide m B) U ∧ Head (More (CSide m B)) Reef.frolic U:=by
 intro f' U; let V := tripK p q x α d l; let R(i):= Arena.aria fun P=>V P i; let Z(i):= Arena.aria fun F=>franc p x q d u l Q h F i
 -- pointwise
 have hU: U= Z+R:=by funext i v; simp only [U,Z,R,f',snowG,Pi.smul_apply,Finset.sum_apply,Pi.add_apply,Arena.aria,Finset.sum_add_distrib,smul_add]; rfl
 have hz:LayerP _ Z:=layer_k H; have hZ: Head _ Reef.frolic Z:= heads H (Classical.choice (show Nonempty (Tab T) from ⟨Classical.choice (Tree.select _ T.patch.odd_side),Classical.ofNonempty⟩)) -- Nonempty pair angle
 have hR(i:Site (More (CSide m B)))(W:Config G₅ (More (CSide m B))):star (R i W)= R i W:=by
    unfold R Arena.aria; simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,star_mul,star_inv₀,star_natCast, star_sum,V,colt_p]; ring
 have hh (s:Signed)(b:Site (More (CSide m B)))(i:Site _)(y): R i (pull s b y)= R (affine s b i) y:=by
    unfold R Arena.aria; simp only [Pi.smul_apply, Finset.sum_apply]; apply congrArg; let T':= Arena.spun T s b; rw [← Equiv.sum_comp T' (fun p=> V p i (pull s b y))]; exact Finset.sum_congr rfl fun j _=> rock_p p q x α d l y i j H.funds s b
 rw [hU]; refine ⟨fun i j=>?_,fun i=>?_,fun i j=>?_⟩
 · funext y; let b:=(assembly (CSide m B)).embed j; change Z _ _+ R (i+b) y=Z i _+R i (Lattice.translate b y); refine congrArg₂ (·+·) (congr_fun (hz i j) y) ?_; have he:= hh 1 b i y; simpa only [pull_one,affine,Signed.act_one] using he.symm
 · filter_upwards [hZ.1 i] with y hy; simp only [satX,Function.comp_apply, Pi.add_apply,star_add]; unfold satX Function.comp at hy; rw [hy,hR,show represent (Vsail Reef.frolic y)=Reef.echo (represent y) from Reef.repr_c y]
   unfold R Arena.aria; simp only [Pi.smul_apply,Finset.sum_apply,V,spine_t]
 filter_upwards [hZ.2 i j] with y hy; let a:=Signed.mirror j; change _+R i _=star (_+_); rw [star_add]; refine congrArg₂ (·+·) hy ?_; change R i _=star (R (a.act i) (represent y)); rw [hR]; have he:=hh a 0 i (represent y); simpa only [affine,add_zero] using he
end YM.CF.Facet
