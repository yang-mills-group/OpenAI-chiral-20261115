import GaugeFieldConstruction.SelenographNX
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
abbrev postNowNX (P:Spine)(A:BeaconNX n)(i:ℤ):BeaconNX n:=P.runBeaconNX A 3 i
abbrev anteBNX (P:Spine)(A:BeaconNX n)(i:ℤ):BeaconNX n:= flipBeaconNX (P.postNowNX A i) 3 0
lemma marchAstNX : (P.postNowNX A i).1.birth=A.1.birth+direction (P.crewB i)∧(P.postNowNX A i).1.death=A.1.death+direction (P.crewB i):=⟨Designs.proceeds ..,track_cost ..⟩
lemma bioAntsNX : (P.anteBNX A i).1.birth=(A.1.mirror 3 0).birth-direction (P.crewB i)∧(P.anteBNX A i).1.death=(A.1.mirror 3 0).death-direction (P.crewB i):=by
 have h(x t):(plane 3 0).flee (x+direction t)= (plane 3 0).flee x- direction t:=by
   rw[Shape.flee_p,show (plane 3 0).s=Signed.mirror 3 from rfl,mirror_direction]; simp [sub_eq_add_neg,direction]
 change (plane 3 0).flee (P.postNowNX A i).1.death=_ ∧ (plane 3 0).flee (P.postNowNX A i).1.birth=_
 rw [(P.marchAstNX A i).1,(P.marchAstNX A i).2,h,h]; exact ⟨rfl,rfl⟩
lemma clrSpinNX (i:Fin 2): shuffle 3 i=i:=by fin_cases i <;> rfl
lemma thetaStrokeNX (a b:Fin 2) : rotorCostNX 3 a b=1:=by
 have h(c:Fin 2):bkNX_scaledn 3 c=bkNX_scaledn 3 0:=by
    fin_cases c
    · rfl
    · norm_num [pin,bkNX_scaledn,clrSpinNX,show upSpin 0=0 from rfl,show upSpin 1=1 from rfl,show dnSpin 0=2 from rfl,show dnSpin 1=3 from rfl,Axis,gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
      all_goals simp only [show (2:Fin 4)= Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ,show Fin.addNat (0:Fin 2) 2=(2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2=(3: Fin 4) from rfl]; norm_num -- tune
      all_goals rfl
 rw [rotorCostNX,h b, ←h a,bkNX_paid,if_pos rfl]
lemma triplePlanNX : P.reflectTest 3 (P.shifts 3 i (P.plaqueStakeNX A))=P.plaqueStakeNX (P.anteBNX A i):=by rw [practiceBNX,gestureNX,thetaStrokeNX,one_smul]
open YM.GaugeFieldConstruction
variable {f:ℕ→ℝ}(h:Tendsto f atTop (𝓝 0))(u:∀ᶠ i:ℕ in atTop,0<f i)
variable (J:ℕ→ℤ)(p:Tendsto (fun i:ℕ=> f i*↑(ruler P.calibration.B*J i:ℤ)) atTop (𝓝 (1/2))) -- f unit.T
open StressFHeat
local notation "dΔ" i:max => direction (P.crewB (J i))
include p h
lemma scaledNX (x:Cover): Tendsto (fun i=> f i • ((2:ℝ) • off (x+dΔ i+dΔ i))) atTop (𝓝 YM.GaugeFieldConstruction.Wick.apex):=by

 have W (F:ℕ→E4)(x:E4)(p:∀ i:Axis,Tendsto (fun n=>F n i) atTop (𝓝 (x i))):Tendsto F atTop (𝓝 x):=(show Continuous (fun p:Axis→ℝ=> (WithLp.toLp 2 p:E4)) by fun_prop).continuousAt.tendsto.comp (show Tendsto (fun i=>(F i).ofLp) atTop (𝓝 x.ofLp) from tendsto_pi_nhds.mpr p)
 apply W; intro j -- E4 Euclidean use
 have he(i:ℕ): (2:ℝ)*↑(P.crewB (J i))=↑(ruler P.calibration.B*J i:ℤ):=by exact_mod_cast (ruler_offset P.calibration (J i))
 have hK: Tendsto (fun i=> f i*(2*(x j:ℝ))) atTop (𝓝 0):=by simpa only [zero_mul] using h.mul_const (2*(x j:ℝ))
 by_cases q:j=3
 · subst j; have ht:=hK.add (p.add p); rw [show (0:ℝ)+(1/2+1/2)=1 from by norm_num] at ht
   rw [show Wick.apex 3=1 from rfl]; refine ht.congr fun i=>?_
   change _=f i*(2* ((↑((x+dΔ i+dΔ i) 3)):ℝ))
   simp only [← he,Pi.add_apply,show ∀ h:ℤ,direction h 3=h from fun h=>by simp [direction],Int.cast_add]; ring -- tune
 rw [show Wick.apex j=0 from by simp [Wick.apex,q]]
 refine hK.congr fun i=>?_ ; change _=f i*(2*((↑((x+dΔ i+dΔ i) j)):ℝ))
 simp [direction,q,Ne.symm q]
lemma scaledColdNX (x:Cover): Tendsto (fun i=> f i • ((2:ℝ) • off (x-dΔ i-dΔ i))) atTop (𝓝 (-YM.GaugeFieldConstruction.Wick.apex)):=by
 refine (P.scaledNX h J p (-x)).neg.congr fun i=>?_
 rw [← smul_neg,← smul_neg]; congr 2; ext j; change -(↑((-x+dΔ i+dΔ i) j):ℝ)= ↑((x-dΔ i-dΔ i) j); simp only [off,Pi.neg_apply,Pi.sub_apply,Pi.add_apply,Int.cast_add,Int.cast_neg,Int.cast_sub]; abel -- tune
omit p h
abbrev kBlendNX :ℂ:= 32*(YM.Maxwell.normal:ℂ)
open YM.GaugeFieldConstruction
lemma minusSearnNX (x y:Cauchy.Spin): Gap.eye (-Wick.apex) (Wick.blend x y)= -(if x=y then kBlendNX else 0):=by
 let v:SU.Slot:=Classical.arbitrary _
 convert Invoice.curvΝ.LeftVU.MinusS_bvu v v x y using 1 <;> simp only[Wick.Yacht.portF,ite_true,Wick.thread_un,true_and,kBlendNX]
include p h u
variable (t w:SU.Slot)
lemma c1passNX : Tendsto (fun i=>κF (poleBNX (P.anteBNX A (J i)) t) (poleDNX (P.postNowNX B (J i)) w)/(f i:ℂ)^3) atTop
 (𝓝 (if w=t ∧ A.2.2.2=B.2.2.2 then kBlendNX else 0)):=by
 by_cases r:w=t
 · simp only [r,true_and] -- maybe
   let D(i:ℕ):Cover:=(P.postNowNX B (J i)).1.death-(P.anteBNX A (J i)).1.birth
   have hz:=gliderRomNX D h u Wick.exposed (p:=by refine (P.scaledNX h J p (B.1.death-(A.1.mirror 3 0).birth)).congr fun i=>?_ ; unfold D; rw [(P.marchAstNX ..).2,(P.bioAntsNX ..).1]; congr 3; abel) A.2.2.2 B.2.2.2
   rw [show Gap.eye _ _ =_ from Invoice.curvΝ.LeftVU.luminate ..] at hz
   refine hz.congr fun i=>?_; simp only [κF, poleBNX, poleDNX,anteBNX,flipBeaconNX,postNowNX,runBeaconNX,if_pos r,clrSpinNX]; rfl
 simp[r, κF,poleBNX,poleDNX]
lemma c2passNX : Tendsto (fun i=>κF (poleBNX (P.postNowNX B (J i)) t) (poleDNX (P.anteBNX A (J i)) w)/(f i:ℂ)^3) atTop
 (𝓝 (-(if w=t ∧ B.2.2.1=A.2.2.1 then kBlendNX else 0))):=by
 by_cases r:w=t
 · simp only [r,true_and] -- maybe
   let D(i:ℕ):Cover:=(P.anteBNX A (J i)).1.death-(P.postNowNX B (J i)).1.birth
   have hz:=gliderRomNX D h u (neg_ne_zero.mpr Wick.exposed) (p:=by refine (P.scaledColdNX h J p ((A.1.mirror 3 0).death-B.1.birth)).congr fun i=>?_ ; unfold D; rw [(P.marchAstNX ..).1,(P.bioAntsNX ..).2]; congr 3; abel) B.2.2.1 A.2.2.1
   rw [show Gap.eye _ _ =_ from minusSearnNX ..] at hz
   refine hz.congr fun i=>?_; simp only [κF, poleBNX, poleDNX,anteBNX,flipBeaconNX,postNowNX,runBeaconNX,if_pos r,clrSpinNX]; rfl
 simp[r, κF,poleBNX,poleDNX]
#print axioms c2passNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
