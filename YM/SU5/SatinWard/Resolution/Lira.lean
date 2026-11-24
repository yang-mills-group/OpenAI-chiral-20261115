import YM.SU5.SatinWard.Resolution.Waltz
import YM.SU5.SatinWard.Resolution.Amity
import YM.SU5.SatinWard.Resolution.Tenement
import YM.SU5.SatinWard.Resolution.Postern
import YM.SU5.SatinWard.Resolution.Array
import YM.SU5.SatinWard.Resolution.Album
import Velour.Crepe.Aperture
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
local notation "R"=> Option Tilted.Ramp
local notation "ι₀"=>Wage4
local notation "LLl"=> P.par.R.L
local notation "K"=> P.run
local notation "Vic1"=> P.large
open SoulField Verdance CasaF CasaF.Signboard Mezzo
local notation "F🌗"=> CoinSong
-- Atlas-gap requests. Same as PSE including actual Grips etc.. Merit.Raw @parent_lift
variable {f0 s v g i:ℕ} {η:Type}[Fintype η]{A:ℝ}
variable {X:CoinSong}{f δ:ℕ→ℕ}(p:Tendsto f atTop atTop)(e:Melodic P η A f0 f){U:ℕ→ CoinSong} (w:Allegory P η A f0 g X f δ U)
local notation "Yxo"=> f∘δ
local notation "p▶" i:max => P.nomadic ((f ∘ δ) i)
local notation "k▶" i:max => P.engine ((f ∘ δ) i)
variable {o t h: Cover} {kμ:ℕ}
variable (hz:nodeC t=P.clockPlate s g o)(u:nodeC h=P.clockPlate s (g+1) o)(j:Axis)
local notation "V_"=> spinFrame 3
variable {c:UNI SU.Slot} (q:Mezzo.Concert c)
-- operators at the Same certification. lag shake.NEW.Calendar through cartage proof
variable (m:Axis)
local notation "A✲" i:max=> P.reachLeaf s i kμ
local notation "Q₀" => surgeBudget
variable (hp:Almanac P s kμ o)
/-! Reach Flavor-symmetric price in THIS X-channel estimator
 after any Allegory payday, never repricing day chambers of a rotated vacuum. -/
local notation "Εχ" => CoinSong
open _root_.YM.SU5.SatinWard -- conflict Namespace YM.SU5 maybe
variable {γ:ℝ}{Y': CoinSong}
-- Running normalization map. One certified council for every calibrated price.
variable (Kc:P.NightCop)
noncomputable def wavelet (g:ℕ)(h:f0 ≤ g): CoinSong:= (Melody.earned P p e Kc h).choose
lemma waveBraid (t:g≥ f0):Recital P η A f0 g (wavelet P p e Kc g t):=(Melody.earned P p e Kc t).choose_spec
private lemma lowerW (T:Εχ)(G:ℝ)(p:Nomina G (1/2) T.toLinearMap P.par.R.L)(x:Soul): ‖x‖ ≤ 2 * roofL P.par.R.L * ‖T x‖:=by
 have he:=p.2.2 x; change ‖G • T x-x‖≤(1/2:ℝ)*‖x‖ at he; rw [norm_sub_rev] at he; have hx:=norm_sub_norm_le x (G • T x); rw [norm_smul,Real.norm_eq_abs] at hx; linarith only [mul_le_mul_of_nonneg_right p.2.1 (norm_nonneg (T x)), he, hx]
lemma waveInv (z:f0≤g): Function.Bijective (wavelet P p e Kc g z):=by
 let Q:= wavelet P p e Kc g z; obtain ⟨x,q⟩:= (waveBraid P p e Kc z).stage
 have hx: Injective Q.toLinearMap:=LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun i w=>norm_le_zero_iff.mp (calc
     _ ≤ _:= lowerW P Q x q i
     _ ≤ _:=by change 2*_*‖Q.toLinearMap i‖≤0; rw [w,norm_zero,mul_zero])))
 exact ⟨hx,LinearMap.surjective_of_injective hx⟩
noncomputable def heartSym (g:ℕ)(h:f0≤g):Soul≃L[ℝ] Soul:= (LinearEquiv.ofBijective (wavelet P p e Kc g h).toLinearMap (waveInv P p e Kc h)).toContinuousLinearEquiv
noncomputable def hugStep (g:ℕ):Soul≃L[ℝ] Soul:= if h:f0 ≤ g then heartSym P p e Kc g h else ContinuousLinearEquiv.refl ℝ Soul
noncomputable def staircase (s j:ℕ) : Soul≃L[ℝ]Soul:= Nat.rec (ContinuousLinearEquiv.refl ℝ Soul) (fun i z=> z.trans (hugStep P p e Kc (i+s))) j
-- old K calibration from f0+1. for X mirror too yield identity at f0+1: cleaner for sums. `ξ` onset all after maturation base. Keep B data available only from base. Thermal.
noncomputable def trueKey (v:ℕ): Soul≃L[ℝ] Soul:= staircase P p e Kc (f0+1) (v-(f0+1))
local notation "W✲" i:max=> wavelet P p e Kc i
local notation "LKey"=> trueKey P p e Kc
local notation "StepX"=> hugStep P p e Kc
lemma packetUse (x:f0 ≤ v)(z:Soul): StepX v z=(W✲ v) x z:=by rw [hugStep,dif_pos x]; rfl
lemma fixed_family (x:Mezzo.Concert c)(t:f0≤v)(z:Soul) : StepX v (rotor x.gate z)=rotor x.gate (StepX v z):=by
 obtain h:= (waveBraid P p e Kc t).family ⟨c,x⟩; rw [packetUse P p e Kc t,packetUse P p e Kc t]
 have he':=DFunLike.congr_fun h (rotor x.gate z); rw [capital] at he'; change rotor x.gate ((W✲ v) t (rotor x.gate.inv (rotor x.gate z))) = (W✲ v) t (rotor x.gate z) at he'; rw [rotor_undo x.gate] at he'; exact he'.symm
lemma staircase_a (s g:ℕ) : staircase P p e Kc s (g+1)=(staircase P p e Kc s g).trans (StepX (g+s)):=rfl
lemma steps (h:f0+1≤v)(x:Soul) : LKey (v+1) x=(W✲ v) (Nat.le_of_succ_le h) (LKey v x):=by rw [trueKey,Nat.succ_sub h,staircase_a]; simp only [ContinuousLinearEquiv.trans_apply,Nat.sub_add_cancel h]; exact packetUse P p e Kc _ _ -- Nat.le syntax incorrect h
lemma gown (x:Mezzo.Concert c)(v:ℕ)(z:Soul): LKey v (rotor x.gate z)=rotor x.gate (LKey v z):=by
 unfold trueKey; generalize a:v-(f0+1)=k; clear a; induction k with
 | zero=>rfl
 | succ k ih=> rw [staircase_a]; simp only [ContinuousLinearEquiv.trans_apply]; rw [ih,fixed_family P p e Kc x (by omega)]
lemma gown_left (x:Mezzo.Concert c)(v:ℕ)(z:Soul): (LKey v).symm (rotor x.gate z)=rotor x.gate ((LKey v).symm z):=by apply (LKey v).injective; rw [(LKey v).apply_symm_apply,gown _ _ _ _ x,(LKey v).apply_symm_apply]
local notation "T'"=> (spinFrame 3).pulseBase P.par.R.L
local notation "Tι"=>2*roofL P.par.R.L
lemma winMoney (x:f0≤v)(z:Soul): ‖(W✲ v) x z‖ ≤ T' * ‖z‖:= by obtain ⟨γ,u⟩:=(waveBraid P p e Kc x).stage; exact Nomina.guide 3 u z
lemma winRight (x:f0 ≤ v)(z:Soul):‖z‖ ≤ Tι*‖(W✲ v) x z‖:= by obtain ⟨γ,u⟩:=(waveBraid P p e Kc x).stage; exact lowerW _ _ γ u _
lemma winLeft (x:f0<v)(l:v ≤ g)(z:Soul): ‖LKey g z‖ ≤ (T')^(g-v) * ‖LKey v z‖:=by
 induction l with
 | refl=> rw [Nat.sub_self,pow_zero,one_mul]
 | step q h=> rw [steps P p e Kc (le_trans x q), Nat.succ_sub q,pow_succ', mul_assoc]; exact (winMoney P p e Kc _ _).trans (mul_le_mul_of_nonneg_left h (div_pos receipt_pos ((spinFrame _).chi_pos _)).le)
lemma winPast (x:f0<v)(l:v ≤ g)(z:Soul): ‖LKey v z‖ ≤ (Tι)^(g-v) * ‖LKey g z‖:=by
 induction l with
 | refl=> rw [Nat.sub_self,pow_zero,one_mul]
 | step q h=> rw [steps P p e Kc (le_trans x q),Nat.succ_sub q,pow_succ,mul_assoc]; exact h.trans (mul_le_mul_of_nonneg_left (winRight P p e Kc _ _) (pow_nonneg (mul_pos (by norm_num) (roofL_pos _)).le _))
#print axioms fixed_family
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
