import GaugeFieldConstruction.BuonaVistaNX
import GaugeFieldConstruction.EpochυFe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
variable (P:Spine)(Z:Lead.Clan){n n0:ℕ}(i:Axis) (x:P.VMark)
abbrev NarcNX (Z:Lead.Clan):VFlavorNX:= (Z.2,Z.1,Z.1)
lemma NarcBillNX : bookColorNX (NarcNX Z)= cutM (colors Z):=by
   ext x y
   rw [bookColorNX,YM.GaugeFieldConstruction.Flavor.wear]
   by_cases h:x=y
   · subst y; rw [cutM,Matrix.diagonal_apply_eq,if_pos rfl, ←familySNX x]
     have hf: (family x)=Z ↔ ((family x).2,x.1,x.1)=(NarcNX Z):=by constructor; intro w; exact Prod.ext (congrArg Prod.snd w) (Prod.ext (show x.1=Z.1 from congrArg Prod.fst w) (show x.1=Z.1 from congrArg Prod.fst w)); exact fun h=>Prod.ext (congrArg (fun p:VFlavorNX=>p.2.1) h) (congrArg Prod.fst h)
     by_cases t:x∈colors Z; · have ht:= hf.1 (mem_filter.mp t).2; rw[if_pos t,ht, Pi.single_eq_same] -- tune
     rw [if_neg t,Pi.single_eq_of_ne (fun v=> t (mem_filter.mpr ⟨mem_univ _, hf.2 v⟩))]
   rw [cutM,Matrix.diagonal_apply_ne _ h]
   split
   next e=> rw[Pi.single_eq_of_ne (show (YM.GaugeFieldConstruction.Flavor.tagged x.2,x.1,y.1)≠ NarcNX Z from fun v=> h (Prod.ext (show x.1=y.1 from (show x.1=Z.1 from congrArg (fun p:VFlavorNX=>p.2.1) v)|>.trans (show y.1=Z.1 from congrArg (fun p:VFlavorNX=>p.2.2) v).symm) e))]
   exact rfl
lemma circularOldNX {A:Lead n}: P.stockS Z A = (-Lead.sing n A.wave) • P.dressPuffNX A (NarcNX Z) A.slot A.slot:=by
 apply Subtype.ext; funext m X
 change Lead.sing n A.wave • _= (-Lead.sing n A.wave) • A.rollNX _ _ _ _ X
 rw [bookFlareNX]; rw [neg_smul,smul_neg,neg_neg]; refine congrArg (fun v:FC (Single (P.calibration.c m))=> _ • v) ?_; refine sum_congr rfl ?_
 intro i h; refine sum_congr rfl ?_
 intro j g; unfold integralPostNX VLeadNX; rw[NarcBillNX,cutM,Matrix.diagonal_mul,if_pos h,one_mul]; rfl
abbrev PillNX(P:Spine) (n:ℕ) (Z:Lead.Clan):BeaconNX n:= (P.flash n,NarcNX Z,0,0)
abbrev numeralNX (n:ℕ):ℂ:=(n:ℂ)^3/5
lemma purchaseStampNX : P.frontMat Z n= numeralNX n • P.plaqueStakeNX (P.PillNX n Z) :=by
 unfold frontMat; rw [circularOldNX P Z (A:=P.flash n)]; have he:-Lead.sing n (P.flash n).wave=numeralNX n:=by unfold Lead.sing numeralNX; change -(-( _ / _) *(phaseF false:ℂ))=_; simp [phaseF] -- tune
 rw[he]; rfl
lemma polarityAccNX (v:Lead n) (p:v.wave=false): quoteP_NX (v,NarcNX Z,(0:Fin 2),(0:Fin 2)) κF=(↑(Window.dimf Z):ℂ)* RomT (direction (n:ℤ)) 0 0:=by
 unfold quoteP_NX; let f:=RomT (direction ↑n) 0 0
 have he:v.death-v.birth= direction ↑n:=by rw [v.aligns,p]; unfold Ballad.sail; simp
 rw [Fintype.sum_prod_type]
 let Y:BeaconNX n:=(v,NarcNX Z,0,0)
 have hz(i:SU.Slot):∑ j:SU.Slot,stapleBNX Y (i,j)*κF (poleBNX Y i) (poleDNX Y j) = if i∈colors Z then f else 0:=by
    rw [sum_eq_single i]; swap
    · intro j u h; unfold stapleBNX; dsimp only [Y]; rw [NarcBillNX,cutM,Matrix.diagonal_apply_ne _ (Ne.symm h),zero_mul]
    swap; · simp
    unfold stapleBNX; dsimp only [Y]; rw [NarcBillNX,cutM,Matrix.diagonal_apply_eq]; change (if i∈colors Z then _ else _) * κF _ _= _; unfold f; split
    · rw [one_mul]; unfold κF poleBNX poleDNX; dsimp only; rw [if_pos rfl,he]
    rw[zero_mul]
 change ∑ i:SU.Slot, ∑ j:SU.Slot,_= _
 have hu: ∑ i:SU.Slot,(if i∈colors Z then f else 0)= ∑ i∈colors Z,f:=by rw[←sum_filter]; simp -- tune
 exact (sum_congr rfl (fun i _=> hz i)).trans (hu.trans (by rw [sum_const, colors_card,nsmul_eq_mul]))
#print axioms purchaseStampNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
