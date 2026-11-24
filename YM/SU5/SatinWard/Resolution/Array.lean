import YM.SU5.SatinWard.Resolution.Flow
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
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "K"=> P.run
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
local notation "Q" => P.calibration.ℓ
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "N" => Z∘F
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
-- on the actual unselected Hil.Ku care
omit pZ W WX h
variable (k:P.NightCop)(u:f0≤ s) (a:payable P v 2) (j:Axis)
local notation "Sp"=>P.par.block
local notation "A✲" i:max=> P.reachLeaf s i w
noncomputable abbrev cardWave (Z: Coords Wage4): P.Card j v (P.reachLeaf s v w):= P.snugLeaf j v (A✲ v) (tiltOwned P X a (Y:=Z) (i:=P.clockPlate s v p)).1 (atlasPav P p e j v)
noncomputable abbrev frameWave (Z:Coords Wage4): (P.Hil j).Op:= P.Box j v (A✲ v) (P.reach_w v e.vivid) (cardWave P X p e a j Z)
abbrev τEnd (P:Spine)(s:ℕ)(l:Cover)(x:Coords Wage4)(b:payable P s 2):P.Test:= P.art (bumper P s l (keynote x)) (aux_test (tiltOwned P none b (i:=l) (Y:=x)).1) -- name future
lemma arcStencil : Set.range (cardWave P X p e a j) ⊆ {u | P.voxTest j v u.val ∈ enclave T }:=by rintro f ⟨x,rfl⟩; exact (enclave_spec ..).2 (tiltOwned P X a).2
lemma frame_cost_w {B:Finset Cover}(f g:Family P.calibration)(t:InTest T true B false f)(q:InTest T true B false g)(X:Between T j 0 (ruler P.par.block*w) B)(p:0<w): let f':= P.snugLeaf j v w t X; let g':= P.snugLeaf j v w q X; P.Box j v w p (P.snugLeaf j v w (t.add q) X) = P.Box j v w p f'+P.Box j v w p g':=by let h:P.Box j v w p (P.snugLeaf j v w (t.add q) X) = (1:ℂ) • P.Box j v w p (P.snugLeaf j v w t X)+P.Box j v w p (P.snugLeaf j v w q X):=P.box_linear j v w p _ _ _ 1 (by rw [one_smul]); simpa only [one_smul] using h -- vector.Pay
lemma frame_totals (x z:Coords Wage4):frameWave P X p e a j (x+z)=frameWave P X p e a j x+frameWave P X p e a j z:=by refine Eq.trans (b:=(1:ℂ) • frameWave P X p e a j x+frameWave P X p e a j z) (P.box_linear j v _ _ _ _ _ _ ?_) ?_ <;> rw [one_smul]; change atlas P X s v p (x+z)=atlas P X s v p x + atlas P X s v p z; unfold atlas keynote; rw [concert,map_add]
lemma box_paidCoin (z:ℝ)(U W: P.Card j s w)(x:W.1.1=z • U.1.1)(w0:0<w): P.Box j s w w0 W=z • P.Box j s w w0 U:=by rw [←Complex.coe_smul] at *; exact PhaseChoice.box_scale P.run P.large P.law P.projection j false (P.room j) s w U W w0 _ x
noncomputable def pseV:= plusE true + plusE false
lemma mpse : multiplier pseV=cloverKey 1 1:=by unfold pseV; rw [map_add,multiplier_p,multiplier_p]; unfold glazeKey cloverKey; simp
lemma frame_total_cost (y:Coords Wage4) : frameWave P none p e a j y+frameWave P (some Shrine.ac0) p e a j y+frameWave P (some Shrine.ac1) p e a j y = (3*gatherG y:ℝ) • frameWave P none p e a j pseV:=by
 let i:= P.clockPlate s v p; let S:= alloy P s v p; let h':= P.reach_w (f:=s) v e.vivid; let X:=Between T j 0 (ruler P.par.block * (A✲ v)) S; have ht:X:=atlasPav P p e j v
 let F(α: Option Tilted.Ramp):Family P.calibration:= bumper P v i (costV α (multiplier y)); have pF(α: Option Tilted.Ramp): InTest T true S false (F α):=(tiltOwned P α a).1; let w(V'):=P.Box j v _ h' (P.snugLeaf j _ _ (pF V') ht)
 let K0:= some Shrine.ac0; let K1:= some Shrine.ac1; change w none+w K0+w K1=_
 unfold w; rw [←frame_cost_w P j _ _ (pF none) (pF K0) ht h',←frame_cost_w P j _ _ _ (pF K1) ht h']; apply box_paidCoin P j -- goal coeff direction? Pfee equality
 change F none+F K0+F K1 =(3*gatherG y:ℝ) • (atlas P none s v p pseV); unfold F; rw [←map_add,←map_add]; let x:= y (.inl true); let z:= y (.inl false); unfold atlas keynote; change bumper P v i (cloverKey x z + localFace Shrine.ac0.s (cloverKey x z)+localFace Shrine.ac1.s (cloverKey x z)) = (3*gatherG y:ℝ) • (bumper P v i (multiplier _)); rw [rotate_m,mpse,map_smul]; congr 1; rw [gather_formula]; unfold x z; ring

private lemma vast (G₀ G₁:Finset Cover)(h:s≤g)(p:Between T j 0 (ruler P.par.block * (A✲ g)) G₀)(q:Between T j 0 (ruler P.par.block * (A✲ (g+1))) G₁): Between T j 0 (ruler P.par.block * (A✲ (g+1))) (G₁∪volumeAround P.par P.width (g+1-g) G₀):=by
 intro a x; rw [mem_union] at x; cases x with
 | inl x=> exact q a x
 | inr x=> rw [P.reach_R h (Nat.le_succ _), Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact expands_shape K V p (g+1-g) a x
include k WX pZ W h u
lemma at_evert (b:Bool)(l:s<g): let p₁:payable P g 2:= (W.stock _ (by omega)).2; let p₂:payable P (g+1) 2:=(W.stock _ (by omega)).2
  ‖frameWave P X p e p₂ j (Wq b)-frameWave P X p e p₁ j (plusE b)‖ ≤2*ageBudget P η A C H s*(sprintCost P.par.R.L ^ (g-s))⁻¹:=by
 intro q q'
 let G:= topGrove P s g p; have he(i:Axis): Between T i 0 (ruler P.par.block * (A✲ (g+1))) G:= vast P i _ _ h (atlasPav P p e i g) (atlasPav P p e i (g+1))
 let τ:= P.room j; let Q0:= (A✲ (g+1)); let y:0<Q0:=P.reach_w (g+1) e.vivid
 let t:= continued P X p h pZ W WX b u; let w:= P.snugLeaf j (g+1) Q0 t.landing (he j); let U:=frameWave P X p e q' j (Wq b); let B:= frameWave P X p e q j (plusE b); let z:=Yt^(g-s); have hp:0<z:=pow_pos (sprint_pos L) _; let f':=(1/2:ℝ)*z; have hf:0<f':=by unfold f'; positivity
 let D:=ageBudget P η A C H s; have hg: P.Box j (g+1) Q0 y w= (↑f':ℂ) • ((1:ℂ) • U - B):= P.upstairs_gap j (Nat.le_succ _) (P.reach_R h (Nat.le_succ _) _) _ _ _ _ _ _ _ (by rw [one_smul]; rfl)
 rw [one_smul] at hg
 let ht:=Presidential.boardPrice K V P.law (g+1) P.projection j Q0 _ G (Z∘F) (pZ.comp WX.visits.tendsto_atTop) D (mul_pos (Real.exp_pos _) (rentalP P W u)) y 0 k (P.fitsOrigin (fun i=>he i)) rfl (porch P X p e h pZ W WX b l u) τ w t -- ABI order? revisit
 rw [show boxOp .. = _ from hg,norm_smul,Complex.norm_real,Real.norm_of_nonneg hf.le] at ht
 change ‖U-B‖≤2*D*z⁻¹; rw [←div_eq_mul_inv]; apply (le_div_iff₀ hp).mpr; change 1/2*z*‖U-B‖≤D at ht; linarith only [ht]
lemma tallyFrame (l:s<g): let p₁:payable P g 2 := (W.stock _ (by omega)).2; let p₂:payable P (g+1) 2:=(W.stock _ (by omega)).2
 ‖portGain Wq • frameWave P none p e p₂ j pseV - frameWave P none p e p₁ j pseV‖≤ 4*ageBudget P η A C H s*(sprintCost P.par.R.L ^ (g-s))⁻¹:=by -- PSD
 intro q q'; let F:= frameWave P none p e q j; let A':= F pseV; let F'(Tt':Option Tilted.Ramp):=frameWave P Tt' p e q' j; let Tt(M:Option Tilted.Ramp):=frameWave P M p e q j; let B(b):= F' none (Wq b); let t:= F' none pseV; let D(M:Option Tilted.Ramp)(b:Bool):=F' M (Wq b)-Tt M (plusE b); let C':= ageBudget P η A C H s*(sprintCost P.par.R.L ^ (g-s))⁻¹
 have hc(M b): ‖D M b‖≤2*C':=by simpa only [D,C', ←mul_assoc] using at_evert P M p e h pZ W WX k u j b l -- order tune
 let P'(Y:Option Tilted.Ramp):=D Y true+D Y false; let B0:=some Shrine.ac0; let B1:=some Shrine.ac1; have hu(i): ‖P' i‖ ≤4*C':= ((norm_add_le ..).trans (add_le_add (hc i true) (hc i false))).trans_eq (by ring)
 have hQ(b:Bool): D none b+D B0 b+D B1 b= (3*gatherG (Wq b):ℝ) • t - (3*gatherG (plusE b):ℝ) • A':=by unfold D; let H:= frame_total_cost P p e q j (plusE b); let G:=frame_total_cost P p e q' j (Wq b); calc
          _=(F' none (Wq b)+F' B0 (Wq b)+F' B1 (Wq b))-(Tt none (plusE b)+ Tt B0 (plusE b)+ Tt B1 (plusE b)):=by abel
          _=_:= by rw [show F' none _+F' B0 _+F' B1 _=_ from G, show Tt none _+ Tt B0 _+Tt B1 _= _ from H]
 have he: P' none+P' B0+P' B1=(3:ℝ) • (portGain Wq • t-A'):=by calc
          _=(D none true+D B0 true+D B1 true)+(D none false+D B0 false+D B1 false):= by unfold P'; abel
          _=_:=by rw [hQ,hQ,portGain,mul_smul,mul_smul, smul_sub, add_smul,smul_add,gather_t,gather_f]; module
 have hh:=norm_add_le (P' none+P' B0) (P' B1)|>.trans (add_le_add ((norm_add_le ..).trans (add_le_add (hu none) (hu B0))) (hu B1)); rw [he,norm_smul,Real.norm_of_nonneg (by norm_num :(0:ℝ)≤3)] at hh
 rw [mul_assoc]; linarith only [hh] -- let challenge
#print axioms at_evert
#print axioms tallyFrame
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
