import YM.SU5.SatinWard.Resolution.Lens
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
noncomputable abbrev costV (X:Option Tilted.Ramp) (D:Moto.Skate):= X.elim D (fun p=> localFace p.s D)
abbrev keynote (x:Coords Wage4):=multiplier x
lemma tiltOwned {Y:Coords Wage4}{i:Cover}{s:ℕ}(q:payable P s 2) : InTest T true (pavilion i petalD) false (bumper P s i (costV X (keynote Y))) ∧ ∀ m,covariant ((bumper P s i (costV X (keynote Y))) m):= bump_owns (Y (.inl true)) (Y (.inl false)) P s i q X _ rfl
lemma tiltFilm(X: Option Tilted.Ramp) (Q:Moto.Skate) : costV X Q= X.elim Q (fun p=> localFace p.s Q):=rfl
lemma concert (a b:Coords Wage4) : costV X (multiplier (a+b))=costV X (multiplier a)+costV X (multiplier b):=by rw [map_add]; cases X; rfl; exact local_plus ..
lemma concertR (a:Coords Wage4)(b:ℝ): costV X (multiplier (b • a))= b • costV X (multiplier a):=by rw [map_smul]; cases X; rfl; exact locale_smul ..
noncomputable abbrev atlas (P:Spine)(X:Option Tilted.Ramp)(s v:ℕ)(o:Cover)(x:Coords Wage4): Family P.calibration := bumper P v (P.clockPlate s v o) (costV X (keynote x))
noncomputable def alloy (P:Spine) (s v:ℕ)(o:Cover):= pavilion (P.clockPlate s v o) petalD
structure Almanac (P:Spine)(s W:ℕ)(o:Cover):Prop where
 vivid : 0<W
 budget : P.RentBox s W
 stand : VelourBoard.Secured P.calibration W 0 (rural (P.thresholdF s)+1) 0 (nodeC o)
 near : ∀ i:Axis,(petalD:ℤ)+(P.calibration.ℓ:ℤ) ≤ nodeC o i
 far : ∀ i:Axis,nodeC o i+((petalD:ℤ)+(P.calibration.ℓ:ℤ)) ≤ ruler P.par.block*(W:ℤ)
-- available any O meeting threshold.Furnish proof for specific residues later
variable {s v g w f:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
local notation "Q" => P.calibration.ℓ
local notation "ℓ▸" s:max i:max p:max=> alloy P s i p
-- ▸ token? test
private lemma prePav (D:ℕ) (j:Axis)(v:ℕ)(hm:(D:ℤ)+(P.calibration.ℓ:ℤ) ≤ nodeC p j)(hs:nodeC p j+((D:ℤ)+(P.calibration.ℓ:ℤ)) ≤ ruler P.par.block*(w:ℤ)):Between T j 0 (ruler P.par.block *P.reachLeaf s v w) (pavilion (P.clockPlate s v p) D) :=by

 intro a w₁; let X:= P.clockPlate s v p; have hx:= (pav_v X a _).1 w₁ j; let V':ℤ:=(↑((L).val^(v-s):ℕ) :ℤ); let d:=ruler P.par.block*(w:ℤ); let s':=nodeC p j; have hsk:1≤ V':=by unfold V'; exact_mod_cast (Nat.succ_le_of_lt (pow_pos P.par.R.L.property (v-s)))
 have h:X j=V'*s':=by unfold X clockPlate; rw [Pi.smul_apply,nsmul_eq_mul]
 have h': ruler P.par.block * (P.reachLeaf s v w:ℤ)= V'*d:=by unfold reachLeaf V' d; rw [Nat.cast_mul]; ring
 let Y':ℤ:=D; have hi:0≤Y':= by unfold Y'; positivity
 have h₀:0≤ s':=le_trans (by positivity:(0:ℤ)≤ (Y'+ (Q :ℤ))) hm
 have h₁:0≤d-s':=by
    have ht:(s'+(Y'+(Q:ℤ)))≤d:=hs; have w:0≤ (Q:ℤ):=by positivity
    omega
 have hM:s'≤ V'*s':=le_mul_of_one_le_left h₀ hsk; have hy:=le_mul_of_one_le_left h₁ hsk; rw [mul_sub] at hy
 rw [h] at hx; change _ ∧ a j+_ ≤ _; rw [h']; have hB:s'+ (Y'+(Q:ℤ))≤d:=hs; have hC:= hm; change _≤ s' at hC; constructor<;> omega

include e in
lemma atlasPav (j:Axis)(v:ℕ) :Between T j 0 (ruler P.par.block *P.reachLeaf s v w) (alloy P s v p) :=prePav P p petalD j v (e.near _) (e.far _)
lemma cast_credit (s v:ℕ)(b:payable P v 2)(j:Coords Wage4) : BQueue (alloy P s v p) (fun _=>atlas P X s v p j) (atlas P X s v p j):= P.pallet (tiltOwned P X b).1
lemma forecast (s v:ℕ)(b:payable P v 2)(y:ℕ→ Coords Wage4)(q: Coords Wage4)(e:Tendsto y atTop (𝓝 q)): BQueue (alloy P s v p) (fun i=>atlas P X s v p (y i)) (atlas P X s v p q):=by
 let J:=atlas P X s v p; let z:= plusE; let A(Vx:Coords Wage4)(b:Bool):ℝ:=Vx (.inl b)
 have h(a):J a=(A a true:ℂ) • J (z true)+(A a false:ℂ) • J (z false):=by
    unfold J atlas z keynote; rw [multiplier_p, multiplier_p]; simp_rw [Complex.coe_smul,← map_smul (bumper P v _),← map_add]; apply congrArg; let W:=cloverKey (A a true) (A a false); let S₀:=Ω₁; let S₁:=Ω₂
    change costV X W=_; unfold glazeKey;
    unfold W cloverKey; simp; cases X with
    | none=>rfl
    | some P=> change localFace _ _=_; rw [local_plus, locale_smul, locale_smul]; rfl
 let t(a:Bool):Tendsto (fun i=>(↑(A (y i) a):ℂ)) atTop (𝓝 (A q a:ℂ)):= Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_pi_nhds.mp e (.inl a))
 change BQueue _ (fun i=> J _) (J q); rw [h q, show (fun i=> J (y i)) = (fun i=>(A (y i) true:ℂ) • J (z true)+(A (y i) false:ℂ) • J (z false)) from funext fun i=>h _]; exact cueSum (cue_scale (cast_credit P X p s v b _) _ _ (t _)) (cue_scale (cast_credit P X p s v b _) _ _ (t _))
variable {f0 g₀:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq)

noncomputable def allay (P:Spine)(s r:ℕ)(p:Cover)(u: Family P.calibration)(v: Family P.calibration) := let C:= (↑((1/2:ℝ)* (sprintCost P.par.R.L)^(r-s)):ℂ); C • (u-v)
noncomputable def atlStar (P:Spine)(X:Option Tilted.Ramp)(s g:ℕ)(o:Cover)(u:Coords Wage4)(y:ℕ)(p:Bool):= allay P s g o (atlas P X s (g+1) o u) (P.coastT g (g+1) y (alloy P s g o) (atlas P X s g o (plusE p)))
noncomputable def atlTop (P:Spine)(X:Option Tilted.Ramp)(s g:ℕ)(o:Cover)(u:Coords Wage4)(p:Bool):= allay P s g o (atlas P X s (g+1) o u) (stream P.run P.large P.refineTest g (g+1-g) (atlas P X s g o (plusE p)))
noncomputable def topGrove (P:Spine)(s g:ℕ)(p:Cover):= alloy P s (g+1) p ∪ volumeAround P.par P.width (g+1-g) (alloy P s g p)
include WX pZ W h
lemma continued (i:Bool) (u:f0≤ s): BQueue (topGrove P s g p) (fun n:ℕ=> atlStar P X s g p (Uq n i) (Z (F n)) i) (atlTop P X s g p (Wq i) i):=by
 let H:=pZ.comp WX.visits.tendsto_atTop
 have T':= VelourBoard.convoy K V g P.projection (Z∘ F) H (cast_credit P X p s g (W.stock g (by omega)).2 (plusE i)) (g+1-g);
 apply cue_scale _ _ _ tendsto_const_nhds -- syntactic alignment
 exact cueSub (cueMono (forecast P X p s (g+1) (W.stock (g+1) (by omega)).2 _ _ (tendsto_pi_nhds.mp WX.limit i)) subset_union_left) (cueMono T' subset_union_right)
#print axioms continued
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
