import GaugeFieldConstruction.SurfBrigR
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
variable {I:Type}[Fintype I][DecidableEq I]{cost:ℕ→P.Test→ℂ}(C: ∀ j:Axis, Porch P cost j)
variable (j:Axis)(σ:I→PermWallJ P)(x:I→P.VMark)
local notation "Ξ"=> C j
local notation "ζ"=> (C j).ρ
local notation "η"=> (C j).Ω
local notation "κω" A:max=> StageR σ (C j) A
local notation "θ"=> AskR P x
local notation "U" i:max => P.transitTile j (x i)
-- raw full clock. Already posed at x. Norm witness. 
noncomputable def SweepR (L:List I)(b:Option ℝ)(A:I→P.Slabs j): P.Slabs j:=match L with
 | []=>1
 | i::l=> let B:= StageR σ (P.publicH j) A; P.Eucl j (B.sep b i (AskR P x i)) * A i * SweepR l (some (B.endline (AskR P x i) i)) A
variable (L:List I)(b:Option ℝ)(A:I→P.Slabs j)
abbrev legR (j:Axis)(x:I→P.VMark)(A:I→P.Slabs j)(i:I): P.Slabs j:= P.ambientTurn j (x i) (A i)
local notation "ν"=> legR j x A
local notation "Ws"=> SweepR j σ x
lemma WandO_R (F:P.Slabs j)(i:I):ζ (P.ambientTurn j (x i) F)= visiting (κω A) (ζ F) (x i):=by
 unfold ambientTurn; rw[map_mul,map_mul,(Ξ).transitReceipt,(Ξ).transitReceipt]; simp only [mul_assoc]; rfl
lemma rank_wR : (κω A).stageList L x [] b= ζ (Ws L b (legR j x A)) η :=by
 induction L generalizing b with
 | nil=> rw [SweepR,map_one]; rfl
 | cons i L ih=>
    rw[SweepR,stageList,ih,map_mul,map_mul]; unfold legR; rw [WandO_R C j σ x A (A i) i]; let T:= StageR σ (P.publicH j) (ν)
    rw [←(Ξ).heat]; rfl
lemma rankTankR : (κω A).ranking L x []= VirtueJ C j (Ws L none (legR j x A)):=by unfold VirtueJ ranking; rw [rank_wR]; rfl
lemma S_rawMeshR (F:I→ScreensJ P)(q:∀ i, AttainedR 0 (F i))(p:PolesR L)(t:AskR P x∈OpenR j σ L)(s:AskR P x∈ MasksR I): SπR C F (AskR P x)=VirtueJ C j (Ws L none (legR j x (BodyΘ P F j σ))):=(PlotBillR C L F q j σ x p t s).trans (rankTankR ..)
lemma priceρR : Continuous (fun F=>SweepR j σ x L b F) :=by
 induction L generalizing b with
 | nil=>exact continuous_const
 | cons i L ih=>
    let Y:= StageR σ (P.publicH j) (fun _=>0); let b':=some (Y.endline (AskR P x i) i)
    change Continuous (fun A:I→P.Slabs j=> (P.Eucl j (Y.sep b i (θ i))) * A i * Ws L b' A) -- metavariable heat
    exact (continuous_const.mul (show Continuous (fun A:I→P.Slabs j=> A i) from continuous_apply _)).mul (ih b') -- tune A implicit maybe missing
noncomputable abbrev PorchTax_R (r:ℕ)(F:I→P.Test): ℂ:= cost r (L.map F).prod
variable {a:I→ℤ}{h:I→ℕ}{t:ℕ}{F:I→P.Test}
abbrev WindowX_R (P:Spine)(σ:I→PermWallJ P)(x:I→P.VMark)(j:Axis)(A:I→P.Slabs j)(r:ℕ)(F:I→P.Test)(i:I): Prop:=P.HabitLevel j (F i) r (x i j-(σ i).val) (x i j + (σ i).val) (A i) r
lemma PlotAccessR (g:∀ i:I, WindowX_R P σ x j A t F i)(p:AskR P x∈ OpenR j σ L): VirtueJ C j (Ws L none A)= cost t (L.map F).prod :=by
 -- use direct previous rankedSalt with relative offsets Rise=-Front, zero positioning and equal perturb context
 choose _ a w k e h hA using g
 let Y:=fun i:I=>(σ i).val-x i j; let B:=fun i:I=>Xτ σ i; let u(i:I) :0<(B i:ℝ):=add_pos (σ i).2 (σ i).2
 let X:= (C j).elementals Y B u A; let z:I→ Cover:= 0
 let P':I→P.VMark:=fun i=>P.vtile t (z i)
 have hz(i:I):P' i=0:= funext fun _=> notch_zero ..
 have hv(i:I): X.frontend (AskR P P' i) i= (κω A).frontend (AskR P x i) i:=by
    change ((P' i j):ℝ)-(((σ i).val:ℝ)-(x i j:ℝ))=(x i j:ℝ)-((σ i).val:ℝ)
    rw [hz]; change 0-(_-_) = _; ring
 have hh(i:I): X.endline (AskR P P' i) i= (κω A).endline (AskR P x i) i:=congrArg (·+(B i:ℝ)) (hv i)
 have hP(L:List I)(b:Option ℝ)(m:(κω A).Correct L (Pages false) (AskR P x) b): X.Correct L (Pages false) (AskR P P') b:=by
   induction L generalizing b with
   | nil=> trivial
   | cons i L ih=> rw [Correct,hv,hh]; exact ⟨m.1,ih _ m.2⟩
 have ht: X.ranking L P' []= cost t (Porch.poseTiles P z F L):=by
   refine (C j).rankedHive u t a w ?_ ?_ ?_ ?_ L (hP L none ((κω A).plane_enough L (by rw[on_rR]; exact p))) -- ↑ w a
   · exact fun i=> (k i).trans (by unfold Y; abel)
   · exact fun i=> (e i).trans (by unfold B Xτ Xφ; abel)
   · intro i; have q:=h i; rw[convey_start] at q; exact q -- z not used! 
   · intro i; have q:= hA i; rw[convey_start] at q; exact q -- Y neg a: X frontend (0)= -up so expected minted a =-U
 have hx: Porch.poseTiles P z F L=(L.map F).prod:=by unfold Porch.poseTiles; rw[show (fun i:I=> P.chartAll (z i) (F i))=F from ?_]; funext k'; let f:=F k'; exact Subtype.ext ((P.followsChart ..).trans (Vacancy.cad_zero _ _ ((marque ..).1 f.property))) -- import tune
 rw [hx] at ht
 have hs(l:List I)(b:Option ℝ): X.stageList l P' [] b = ζ (Ws l b A) η:=by
    induction l generalizing b with
    | nil=> rw[SweepR,map_one]; rfl
    | cons i l ih=>
       let T:= StageR σ (P.publicH j) A
       have ω(i:I) : X.visiting (X.op i) (P' i)=ζ (A i):=by
          rw[hz]; change (C j).porchMove 0*(ζ _*(C j).porchMove (-0))=_; rw[neg_zero,(C j).porch_zero,mul_one,one_mul]
       have hf: X.sep b i (AskR P P' i)= T.sep b i (AskR P x i):=by cases b; exact rfl; unfold sep; rw [hv]; rfl
       rw [stageList, SweepR,ih]; let D':=P.Eucl j (T.sep b i (AskR P x i)); let w:= some (T.endline (AskR P x i) i); let w':=some (X.endline (AskR P P' i) i)
       change (C j).Time.E (X.sep b i (AskR P P' i)) (X.visiting (X.op i) (P' i) (ζ (Ws l w' A) η))=ζ (D'*A i* Ws l w A) η
       rw [ω,hf,(Ξ).heat,map_mul,map_mul, (show w'=w from congrArg some (hh i))]; rfl
 exact (congrArg (inner ℂ η) (hs L none).symm).trans ht
#print axioms PlotAccessR
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
