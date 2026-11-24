import GaugeFieldConstruction.RovioJ
import GaugeFieldConstruction.FrayTideJ
import GaugeFieldConstruction.SteepleJ
import GaugeFieldConstruction.MovingH
import GaugeFieldConstruction.ZagoraJ
import GaugeFieldConstruction.VirenneJ
import GaugeFieldConstruction.TrollopJ
import GaugeFieldConstruction.ZucatoJ
import GaugeFieldConstruction.KronenJ
import GaugeFieldConstruction.MapicoJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
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
variable (P:Spine) {X:Type}[Fintype X][LinearOrder X]
open ProbeθJ Preparation Yoke
-- Pose. Film any from Advent plus f mirrors. only valid Stamps.S.
local notation "KΑ"=>P.calibration
local notation "Kγ"=>P.par
local notation "Lγ"=> P.par.R.L
local notation "ℓν"=>P.par.R.L.val
local notation "HΥ"=> inkΛJ
variable (x:P.VMark) (f s:ℕ) (j:Axis)
open Etch
-- Width work schedule. Ch chosen just above 100 and H margins (K folded in Xû). Marrow Xû*h is enough >K.V. Have Crown.Price exposures.
local notation "ζ_"=> XûJ P.par P.width f
local notation "ρt"=> ruler P.par.block
abbrev WorkWJ (P:Spine)(f:ℕ):ℕ:=100* XûJ P.par P.width f -- width in ticks
noncomputable def Mapnest(P:Spine)(f:ℕ)(x:P.VMark) :Cover:= fun i=>((adventJ P x f i)/(ruler P.par.block)) - (50*(XûJ P.par P.width f):ℕ) -- gauge coarse.Edge.
local notation "Υ"=>WorkWJ P f
local notation "Γu"=> Mapnest P f x
local notation "Zχ"=> HaloShip P x f s
local notation "rκ"=>runnel KΑ (Υ:ℕ) Γu
lemma NumberRK: 10 ≤ XûJ P.par P.width f:=by unfold XûJ; omega
lemma MarginGK (j:Axis) : let o:= Mapnest P f x; let v:=adventJ P x f j; let A:ℤ:=ruler P.par.block; let q:ℤ:=(WorkWJ P f);let z:ℤ:=(XûJ P.par P.width f); A*(o j)+20*z ≤ v ∧ v+20*z ≤ A*(o j+q):=by
 intro o v A q z; have h:0<A:= ruler_gene _; have e:=Int.emod_add_mul_ediv v A; have hy:= Int.emod_lt_of_pos v h; have hw:=Int.emod_nonneg v (by omega:A≠0); let W:= v % A; have hm: o j=v/A-50*z:=by unfold z; norm_cast
 rw [hm]; have hg:q=100*z:=by unfold z; norm_cast
 rw[hg]; have hp:(10:ℤ)≤ z:=by change 10 ≤ (XûJ P.par P.width f:ℤ); exact_mod_cast NumberRK P f
 constructor <;> nlinarith
-- shift by natural tick integer a at f. implements certificate.S panel offset σ j=0. D and pads.H_ cal
local notation "Δj"=> ruler P.par.block
local notation "tW"=> P.stampPin
abbrev fShiftJ(P:Spine)(f:ℕ)(j:Axis)(x:P.VMark) :ℤ:= -(Mapnest P f x j)
def GrowJ (P:Spine)(f s:ℕ):ℕ:=P.par.R.L.val^(s-f)
local notation "κν"=> GrowJ P f s
local notation "ωf"=>fShiftJ P f j x
abbrev terraceJ(P:Spine)(v:ℤ)(j:Axis):LaurelJ:= [(j,gaugeT P.calibration v),(j,0)]
local notation "Ρ"=> (terraceJ P)
local notation "Γn"=>pet Γu j 0
local notation "Z"=>P.calibration
local notation "Q"=>P.mellow
lemma HeightGlove (u:f≤ s)(i:ℤ): P.stampPin s ((GrowJ P f s:ℤ)*i)=P.stampPin f i:=by
 apply Subtype.ext; change (P.stampPin s _:ℝ)=(_ :ℝ); simp only [mellow_firm]; push_cast; unfold GrowJ; push_cast; rw [←mellow_age P f s u]; ring -- tune
lemma VTerrace (i:ℤ)(b:Axis)(F:Family P.calibration): VivaJ P.par f s P.calibration (terraceJ P i b) F=relocate P.calibration b ((GrowJ P f s:ℤ)*i) F :=by
 change mirror _ _ ((ℓν:ℤ)^(s-f)*_) (mirror _ _ ((ℓν:ℤ)^(s-f)*(0:ℤ)) F)=mirror _ _ (gaugeT _ _) (mirror _ _ 0 F)
 rw [mul_zero]; unfold gaugeT; congr 1; unfold GrowJ Heat.gaugeShift; push_cast; ring
lemma Ridge_j : Inset P.calibration (WorkWJ P f) (pet (Mapnest P f x) j 0) 0 (10 *XûJ P.par P.width f) ((forgeιJ P.par f f (terraceJ P (fShiftJ P f j x) j)).motion (adventJ P x f)):=by
 intro i; let o:=adventJ P x f; have hz:= NumberRK P f
 let t:=ωf; have hp:forgeιJ P.par f f ((Ρ) t j)=joinX (plane j (gaugeT P.calibration t)) (joinX (plane j 0) (incX 1)):=by simp [forgeιJ,globeJ,terraceJ]
 have h:=MarginGK P x f i; rw[hp,palm,palm, fling_move,fling_move]; have eq:(incX 1).motion (adventJ P x f)=adventJ P x f:=by simp [incX,Shape.motion]
 rw[eq,runnel,runnel]; -- goal
 by_cases p:i=j
 · subst i; rw [Pi.zero_apply,pet_i,if_pos rfl,if_pos rfl, ruler_offset]; simp only [mul_zero,add_zero,zero_add,mul_one]; unfold t fShiftJ; rw [mul_neg]; dsimp only at h; rw [show P.calibration.B=P.par.block from rfl]; rw [mul_add] at h
   omega
 rw [pet_j _ p,Pi.zero_apply,if_neg (Ne.symm p),if_neg (Ne.symm p)]; simp only [mul_zero,add_zero,zero_add,mul_one]; rw [show P.calibration.B=P.par.block from rfl]; omega
local notation "W_j"=> WorkWJ P f
local notation "Κj"=> GrowJ P f s*Υ
-- Safe leaf fonts: real center on mesh. 
abbrev Holdκ (P:Spine)(s:ℕ)(f:ℕ)(x:P.VMark)(S:Finset Cover):Prop:=∀ j, P.Marrow j s ((x j:ℝ)- P.mellow f*XûJ P.par P.width f) ((x j:ℝ)+P.mellow f*XûJ P.par P.width f) S
variable (T:Finset Cover)(p:Holdκ P s f x T)
lemma IglooCaps (i:Axis): (P.stampPin f (Mapnest P f x i):ℝ) ≤ (x i:ℝ)- P.mellow f*XûJ P.par P.width f ∧ (x i:ℝ)+P.mellow f*XûJ P.par P.width f ≤ (P.stampPin f (Mapnest P f x i+WorkWJ P f):ℝ):=by
 rw [P.mellow_firm,P.mellow_firm]; let d:= P.mellow f; have ht:= P.spale_J x f i; rw[abs_le] at ht
 obtain ⟨e,g⟩:=MarginGK P x f i -- tune wrong projection
 let x₁:=adventJ P x f i; have he: ((ruler P.par.block*(Mapnest P f x i):ℤ):ℝ)+20*(ζ_:ℝ) ≤ (x₁:ℝ) :=by exact_mod_cast e
 have hv:(x₁:ℝ)+20*(ζ_:ℝ)≤ ((ruler P.par.block*(Mapnest P f x i+WorkWJ P f):ℤ):ℝ):=by exact_mod_cast g
 have hw:(10:ℝ) ≤ ζ_:= by exact_mod_cast NumberRK P f
 have hp:=P.mellow_good f
 constructor <;> nlinarith [ht.1,ht.2,mul_le_mul_of_nonneg_left he hp.le,mul_le_mul_of_nonneg_left hv hp.le,mul_le_mul_of_nonneg_left hw hp.le]
#print gaugeT
#check ruler_offset
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
