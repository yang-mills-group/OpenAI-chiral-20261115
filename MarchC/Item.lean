import MarchC.Era
import Aloft.ZL
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(H:Rovers P F C D x)
-- relation tablet/cellar.V used later.Axis 3
local notation "R" => ruler P.par.block
local notation "K" => P.calibration
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
local notation "U"=>P.cartage 3 ξ
private noncomputable def inspect(j:ℕ):Cover:=fun i=> if i=(3:Axis) then setback P F j else 0 -- noncomputable
private lemma situ(j:ℕ): metro P (inspect P F j) (subject P F j)=cellar P F j:=by
 apply node_dC; ext i; rw [cellar,metro_cal,bellV]; unfold inspect; split_ifs with h; rfl; simp
lemma moon(j:ℕ)(b:Bool):tablet P F j 3 b=metro P (sap P F j 3 b) (subject P F j):=by
 cases b; rfl
 change zap _ (metro P _ (zap 3 _))=_; rw [zap_metro,twice_zap]; rfl
lemma sap_z(j:ℕ)(b:Bool):sap P F j 3 b 3=setback P F j:=by
 cases b; rfl
 change difft 3 3 (downR P j (zap 3 (subject P F j)) 3) =_; unfold difft; rw [if_pos rfl]; unfold downR; rw [zap_node, if_pos rfl, neg_neg]; rfl
noncomputable abbrev wand(s j:ℕ)(b:Bool):Cover:=fun i=> (P.par.R.L.val:ℤ)^(s-j)*((sap P F j 3 b - inspect P F j) i)
lemma casting_m(s j:ℕ)(b:Bool): metro P (wand P F s j b) (orbitB P.par.R.L (cellar P F j) (s-j))=orbitB P.par.R.L (tablet P F j 3 b) (s-j):=by
 rw [←swingZ,←situ,hingeZ,←moon]
lemma noted(s j:ℕ)(h:j ≤ s)(b:Bool) : P.gridSpot s (wand P F s j b)= centreA P F j 3 b-central P F j:=by
 let o:=orbitB P.par.R.L (cellar P F j) (s-j)
 exact (leaseZ P s (wand P F s j b) o).symm.trans (congrArg₂ (·-·) ((congrArg (optic P s) (casting_m P F s j b)).trans (leaseK P s j h _)) (leaseK P s j h (cellar P F j)))
lemma eraM(s j:ℕ)(b:Bool) : wand P F s j b 3=0:=by unfold wand; simp only [Pi.sub_apply,inspect,sap_z]; rw [if_pos trivial,sub_self,mul_zero]
set_option maxHeartbeats 960000 in
lemma vector_card(s j:ℕ)(t:j ≤ s)(b:Bool):
 let z:=P.wealth 3 (ξ) (recoup P F C D (ξ) s j)
 headed P x F C D s j 3 b=U (centreA P F j 3 b-central P F j) z:=by
 intro z; let g':=(cellar P F j); let i:=tablet P F j 3 b; let d:=centreA P F j 3 b-central P F j; let y:=wand P F s j b
 let L:=orbitB P.par.R.L; let o:= L g' (s-j); let w:=L i (s-j)
 have hh':(P.calibration.ℓ:ℤ)+22 ≤ nodeC g' 3:= fresh ..
 have hw':(P.calibration.ℓ:ℤ)+22 ≤ nodeC i 3:=tablet_born P F j 3 b
 have g(q:Cover)(h:(P.calibration.ℓ:ℤ)+22 ≤ nodeC q 3):(P.calibration.ℓ:ℤ)+22 ≤ nodeC (L q (s-j)) 3:=by
    unfold L; rw [dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul]; apply h.trans; apply le_mul_of_one_le_left (by omega); exact_mod_cast (show 1 ≤ P.par.R.L.val^(s-j) from Nat.one_le_of_lt (pow_pos P.par.R.L.property _))
 have h:=g g' hh'; have hw:=g i hw'
 let z':=P.viewF 3 (ξ) s (bornP P 3 s o h); let w':=P.viewF 3 (ξ) s (bornP P 3 s w hw)
 have hx:P.gridSpot s y 3=0:=by rw [ P.gridSpot_mul,show y 3=0 from eraM P F s j b,Int.cast_zero,zero_mul]
 let p':=P.wealth 3 (ξ) z'
 have he:P.wealth 3 (ξ) w'=U d p':= Eq.trans (travelS P 3 s o w y 0 (show (0:ℤ) = y 3 from (eraM P F s j b).symm) (casting_m P F s j b) (ξ) h hw) (congrArg₂ (fun (u:Vantage) (v:ℝ≥0)=> (U u) (E v p')) (noted P F s j t b) (show (P.gridSpot s y 3).toNNReal=0 from by rw [hx,Real.toNNReal_zero]) |>.trans (congrArg (U d) (DFunLike.congr_fun (P.seasons 3 (ξ)).eZero p')))
 let A:=((basket P.par.R.L C D F s:ℝ):ℂ); let Z:= P.wealth 3 (ξ)
 exact (map_smul Z A w').trans ((congrArg (fun k:W=> A • k) he).trans ((map_smul ((U d) ∘L Z) A z').symm)) -- compose matches? A•(U d)(Z z) correct
variable (j:ℕ)
lemma shares(hj:F≤j)(k:W)(v:Aloft.PeriodS P F C D x j k)(b:Bool) : incoming P x F C D j 3 b=U (centreA P F j 3 b-central P F j) k:=by
 let a':= (U (centreA P F j 3 b-central P F j))
 let f(s:ℕ):=P.wealth 3 (ξ) (recoup P F C D (ξ) s j)
 exact (show Tendsto (fun s=>headed P x F C D s j 3 b) atTop (𝓝 (a' k)) from (((a').continuous.continuousAt.tendsto.comp (show Tendsto f atTop (𝓝 k) from v.1))).congr' ((eventually_ge_atTop j).mono fun s p=> (vector_card P x F C D s j p b).symm)).limUnder_eq
lemma both_clock(j:ℕ)(b:Bool):(centreA P F j 3 b) 3=tidal P F j:=by
 let y:=wand P F j j b
 have hp:P.gridSpot j y 3=0:=by rw [ P.gridSpot_mul,show y 3=0 from eraM P F j j b,Int.cast_zero,zero_mul]
 have h:(centreA P F j 3 b) 3-(central P F j) 3=0:= (congrFun (noted P F j j le_rfl b) 3).symm.trans hp; exact (sub_eq_zero.mp h).trans (center3 P F j)
lemma tomorrow(j:ℕ): booth P F j 3=tidal P F j+tidal P F j:=congrArg₂ (·+·) (both_clock P F j true) (both_clock P F j false)
local notation "κ"=> valley P x 3
include H J
lemma thanks(h:F ≤j)(v:W)(p:Aloft.PeriodS P F C D x j v)(y:Vantage)(d:y∈{z:Vantage|∀i:Axis,0< z i})(q:2*tidal P F j<y 3):crownM P x F C D y=κ (y 3-(tidal P F j+tidal P F j)) y v v:=by
 let c(b:Bool):=centreA P F j 3 b; let z:=central P F j; let sp (b:Bool):= c b-z
 let b:= y 3-booth P F j 3
 exact ((axis_price P x J F C D H 3 j h (show ∀i:Axis,0<y i from d) (by rw [tomorrow]; linarith only [q])).trans ((congrArg₂ (κ b (y+c true-c false)) (shares P x F C D j h v p true) (shares P x F C D j h v p false)).trans (valley_roll P x 3 b _ (sp true) (sp false) v v))).trans (congrArg₂ (fun (z:ℝ) (a:Vantage)=> κ z a v v) (congrArg (y 3-·) (tomorrow P F j)) (show y+c true-c false+sp false-sp true=y by unfold sp; abel))
#print axioms thanks
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
