import GaugeFieldConstruction.ExalterNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
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
variable (P:Spine){n:ℕ}(A B:BeaconNX n)(i:ℤ)
abbrev CnPadNX (A B:BeaconNX n) :ℂ:= quadP_NX A B κF- quoteP_NX A κF*quoteP_NX B κF
local notation "τv"=> SU.Slot× SU.Slot
abbrev InBeatNX (x y:SU.Slot)(k:VFlavorNX): Prop:= x.2=y.2∧ (YM.GaugeFieldConstruction.Flavor.tagged x.2,x.1,y.1)=k
def SieveColNX (k:VFlavorNX): Finset (SU.Slot × SU.Slot):=Finset.univ.filter fun v:SU.Slot × SU.Slot=> InBeatNX v.2 v.1 k -- reverse order of first Flipped
lemma BlendRayNX(k:VFlavorNX)(t w: SU.Slot): bookColorNX k t w=if (w,t)∈SieveColNX k then 1 else 0:=by
 rw[bookColorNX,YM.GaugeFieldConstruction.Flavor.wear]
 by_cases h:t.2=w.2
 · rw [if_pos h]; by_cases p:(w,t)∈SieveColNX k
   · rw [if_pos p,show (YM.GaugeFieldConstruction.Flavor.tagged t.2,t.1,w.1)=k from (mem_filter.mp p).2.2,Pi.single_eq_same]
   rw [if_neg p,Pi.single_eq_of_ne (fun q=>p (mem_filter.mpr ⟨mem_univ _,h,q⟩))]
 rw[if_neg h,if_neg (fun u=>h (mem_filter.mp u).2.1)]
lemma BeamCardNX (k:VFlavorNX):(SieveColNX k).card=Window.dimf (k.2.1,k.1):=by
 rw [← colors_card]
 let S:=SieveColNX k
 have t(x:SU.Slot)(p:x∈ colors (k.2.1,k.1)):x.1=k.2.1 ∧ YM.GaugeFieldConstruction.Flavor.tagged x.2=k.1:=⟨congrArg Prod.fst (mem_filter.mp p).2, (familySNX _).symm.trans (congrArg Prod.snd (mem_filter.mp p).2)⟩
 symm
 refine card_bij (fun x _=> ((k.2.2,x.2),x)) (fun x e=> mem_filter.mpr ⟨mem_univ _,rfl,Prod.ext (t x e).2 (Prod.ext (t x e).1 rfl)⟩) (fun u _ v _ H=> congrArg Prod.snd H) ?_ -- tune NS
 intro v u
 let x:=v.2; let q:=v.1; have hl:x.2=q.2 ∧ (YM.GaugeFieldConstruction.Flavor.tagged x.2,x.1,q.1)=k:= (mem_filter.mp u).2
 refine ⟨x,mem_filter.mpr ⟨mem_univ _,Prod.ext (congrArg (fun k:VFlavorNX=>k.2.1) hl.2) ((familySNX _).trans (congrArg Prod.fst hl.2))⟩, Prod.ext (Prod.ext (congrArg (fun k:VFlavorNX=>k.2.2) hl.2).symm hl.1) rfl⟩
abbrev NumberSpinNX (A:BeaconNX n):ℝ:=Window.dimf (A.2.1.2.1,A.2.1.1)
lemma NumSPposNX:0<NumberSpinNX A:=by unfold NumberSpinNX Window.dimf; split <;> norm_num
abbrev ArmΔScanNX (A B:BeaconNX n) :ℂ:= if A.2=B.2 then ((NumberSpinNX A):ℂ)*kBlendNX*kBlendNX else 0
abbrev BitFluxNX (A B:BeaconNX n)(v w:τv):ℂ := -(bookColorNX (reverseRackNX A.2.1) v.1 v.2* bookColorNX B.2.1 w.1 w.2*((if w.2=v.1 ∧ A.2.2.2=B.2.2.2 then kBlendNX else 0)*(-(if v.2=w.1∧ B.2.2.1=A.2.2.1 then kBlendNX else 0))))
lemma PivotPointNX: (∑ v:τv,∑ w:τv,BitFluxNX A B v w)= ArmΔScanNX A B:=by
 have he(v:τv) : ∑ w:τv,BitFluxNX A B v w= BitFluxNX A B v v.swap:=by
   rw[sum_eq_single v.swap]
   · intro w _ h; unfold BitFluxNX; split; swap; · simp
     next p=>split; swap; · simp
             next t=> exact (h (Prod.ext t.1.symm p.1)).elim -- syntax
   simp
 simp_rw [he]; unfold ArmΔScanNX
 have hx(v:τv) (p:A.2=B.2): BitFluxNX A B v v.swap= if v∈SieveColNX A.2.1 then kBlendNX*kBlendNX else 0:=by
   unfold BitFluxNX; rw[←p]; simp only [Prod.fst_swap, Prod.snd_swap, and_self,↓reduceIte]; rw[rotColorNX,Matrix.star_apply,BlendRayNX]; by_cases t:v∈SieveColNX A.2.1 <;> simp [t] -- tune
 split
 next p=>
   simp_rw [hx _ p, ←sum_filter, NumberSpinNX,←BeamCardNX]; simp [nsmul_eq_mul,mul_assoc]
 next u=>
   refine sum_eq_zero fun v _=>?_
   unfold BitFluxNX; simp only [Prod.fst_swap,Prod.snd_swap,true_and]; split; swap; · simp
   next p=> split; swap; · simp
            next q=>
              rw[rotColorNX,Matrix.star_apply,BlendRayNX,BlendRayNX]
              split; swap; · simp
              next h=> rw [if_neg (show ¬ _ from fun v=> u (Prod.ext ((mem_filter.mp h).2.2.symm.trans (mem_filter.mp v).2.2) (Prod.ext q.symm p)))]; simp
variable {f:ℕ→ℝ}(h:Tendsto f atTop (𝓝 0))(u:∀ᶠ i:ℕ in atTop,0<f i)
variable (J:ℕ→ℤ)(p:Tendsto (fun i:ℕ=> f i*↑(ruler P.calibration.B*J i:ℤ)) atTop (𝓝 (1/2)))
include p h u
lemma QuintAxisNX : Tendsto (fun i=> CnPadNX (P.anteBNX A (J i)) (P.postNowNX B (J i))/(f i:ℂ)^6) atTop (𝓝 (ArmΔScanNX A B)):=by
 let X i:=P.anteBNX A (J i); let Y i:=P.postNowNX B (J i); let F(v w: τv)(i:ℕ):ℂ:= -(stapleBNX (X i) v*stapleBNX (Y i) w*((κF (poleBNX (X i) v.1) (poleDNX (Y i) w.2)/(f i:ℂ)^3)*(κF (poleBNX (Y i) w.1) (poleDNX (X i) v.2)/(f i:ℂ)^3)))
 have ht(v w:τv):Tendsto (F v w) atTop (𝓝 (BitFluxNX A B v w)):= by
   have hp:∀ i:ℕ,w=w:=fun _=>rfl
   exact ((((P.c1passNX A B h u J p v.1 w.2).mul (P.c2passNX A B h u J p w.1 v.2)).const_mul _).neg)
 rw [←PivotPointNX]; refine (tendsto_finsetSum Finset.univ fun i _=>tendsto_finsetSum Finset.univ fun j _=> ht i j).congr fun i=> ?_
 unfold CnPadNX quadP_NX quoteP_NX; rw [sum_mul]; simp_rw [mul_sum]; rw[← sum_sub_distrib,sum_div]; apply sum_congr rfl; intro v _; rw[← sum_sub_distrib,sum_div]; apply sum_congr rfl; intro w _; let g:=(f i:ℂ); rw [show g^6=g^3*g^3 from by ring]; unfold F X Y; simp only [←mul_div_mul_comm] -- tune
 ring
#print axioms QuintAxisNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
