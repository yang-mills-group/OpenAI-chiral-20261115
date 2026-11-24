import YM.SU5.SatinWard.Resolution.Lunar
import Velour.Crepe.Aperture
import YM.SU5.SatinWard.Resolution.Belfry
import YM.SU5.Assay.RawLag
import Velour.Crepe.Dye
import YM.SU5.Assay.Jaw
import YM.SU5.Reconstruction.Cross.Boundaries
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
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
open Selected
local notation "ζ"=>P.sidesPerTick
-- between gauge site homes and integer ticks
abbrev geoAt (P:Spine)(s:ℕ):Cover→ Vantage:= gaugePosition P.par s
variable (a u:Cover)
local notation "z" v:max=> geoAt P v
lemma geo_scale (x:Cover)(h:s≤v)(k:Axis):geoAt P v (((L).val^(v-s):ℕ)• x) k= geoAt P s x k:=by
 unfold geoAt gaugePosition gaugeMesh; rw [show v=s+(v-s) from by omega, pow_add, Nat.add_sub_cancel_left, Pi.smul_apply,nsmul_eq_mul]; push_cast; field_simp
 -- maybe field_simp yields goal ((L).val:ℝ)^_>0 auto?
local notation "A→" v:max=> v+ζ • u
lemma geo_tick (s:ℕ) (k:Axis):geoAt P s (a+P.sidesPerTick • u) k=geoAt P s a k+P.tock s (u k):=by
 unfold geoAt gaugePosition; change ((((a k+ζ • u k):ℤ):ℝ))* gaugeMesh P.par s=_; -- ABI
 rw [nsmul_eq_mul, ← rulerTicks P]; unfold tock; rw [Reconstruction.Atlas.bell_norm]; push_cast; ring
lemma macroUnit (s:ℕ):((ζ):ℝ)* gaugeMesh P.par s=P.macroStep s:=by
 unfold macroStep; rw [Reconstruction.Atlas.pitch_norm,rulerTicks,Int.cast_natCast,mul_comm]
lemma geo_pose (s:ℕ): geoAt P s (a+ζ • u)= geoAt P s a+P.laysM (P.vtile s u):= funext fun i=> geo_tick ..
-- every registered gauge-pose is a genuine chartAll w.r.t origin.
lemma geoDay (h:s≤ v): geoAt P v (P.clockPlate s v p)= geoAt P s (nodeC p):=funext fun i=> geo_scale P (nodeC p) h i
lemma lays_uniq: Injective (P.laysM):=fun x y h=> funext fun i=> Subtype.ext (congrFun h i)
lemma vtNeg (s:ℕ): P.vtile s (-u)= -P.vtile s u:= by
 apply lays_uniq; funext i; change P.tock s (-u i)= -P.tock s (u i); simp only [Spine.tock_price,Int.cast_neg,neg_mul]
lemma laysDiff (p q:P.VMark): P.laysM (p-q)=P.laysM p-P.laysM q:=rfl
variable {a} (u':ResidualPermit a)
abbrev home (P:Spine)(a:Cover)(v:ℕ):Vantage:= (geoAt P v (homeTag P a))
include u' in
lemma home_room (s:ℕ)(j:Axis): |home P a s j| ≤ P.macroStep s:= by
 unfold home; rw [←macroUnit]; unfold geoAt gaugePosition; rw [abs_mul, abs_of_nonneg (gaugeMesh_pos ..).le]; apply mul_le_mul_of_nonneg_right _ (gaugeMesh_pos ..).le; rw [← Int.cast_abs]; exact_mod_cast homeCost P a u' j -- include u'
variable (M: P.par.R.L.val % 16 =1)
section
include M
/-- Anchor and time ticks for simultaneous preselection comparison over full axes. -/
lemma geo_anchor (f v:ℕ)(a:Cover)(h:f ≤ v) : ∃ x:Cover, P.laysM (P.vtile v x)= home P a f-home P a v:=by
 obtain ⟨x,ex⟩:=residues_delta P M a f v; refine ⟨x,?_⟩; apply eq_sub_of_add_eq; rw [add_comm]; unfold home; rw [←geo_pose,←ex]; exact funext fun i=>geo_scale P _ h i
#check geo_anchor
#print axioms geo_anchor
noncomputable abbrev chair (a:Cover){f v:ℕ}(h:f≤ v): P.VMark:= P.vtile v ((geo_anchor P M f v a h).choose)
lemma seated (a:Cover){f v:ℕ}(h:f ≤ v):P.laysM (chair P M a h)=home P a f-home P a v:=(geo_anchor P M f v a h).choose_spec
variable (a:Cover)
lemma position_ticks (h:s≤ v)(U:ShowField P s (homeTag P a) p) : ∃ x:Cover, P.clockPlate s v p=homeTag P a+ ζ • x:=by
 let c:= (fun _:Axis => (↑(waitZ P s):ℤ)); let ν:= (L).val^(v-s); obtain ⟨x,ex⟩:= residues_delta P M a s v; refine ⟨x+ν • c,?_⟩; change ν • nodeC p=_; rw [U.reach,smul_add, show (fun _ : Axis=> (↑(waitZ P s):ℤ))=c from rfl]; rw [show ν • homeTag P a=homeTag P a+ζ • x from ex,smul_comm ν ζ c,smul_add,add_assoc]
lemma position_p (h:s≤ v)(U:ShowField P s (homeTag P a) p)(t:Cover)(e:P.clockPlate s v p=homeTag P a+ζ • t): P.laysM (P.vtile v t)= geoAt P s (nodeC p)-home P a v:=by
 apply eq_sub_of_add_eq; rw [add_comm]; unfold home; rw [←geo_pose,←e,geoDay P p h] -- signatures
end
variable (y:Coords Wage4)(j:Axis)(r:ℤ){pL:payable P v 2} (q:payable P v 2)
lemma temple_m (p:ℤ) : mirror T j p (bumper P v a (keynote y))=bumper P v ((plane j p).motion a) (keynote y):= (bump_mirror P v a _ j p).trans (congrArg _ (templeGlazed j (y (.inl true)) (y (.inl false)))) -- order
lemma temple_step : P.shifts j r (τEnd P v a y q)= τEnd P v (a+(ruler P.par.block*r) • step j) y q :=by
 let F:= bumper P v a (keynote y); apply Subtype.ext
 change relocate T j r F=_; rw [← SlabMark.mirror_at T j (show gaugeT T r-0=gaugeT T r from sub_zero _) (show TestFamily P.calibration true F from aux_test (tiltOwned P none q (Y:=y)).1)]; unfold F; rw [temple_m,temple_m]
 change bumper P v _ _=bumper P v _ _; apply congrArg (fun a=> bumper P v a (keynote y)); -- result type problem
 funext i; rw [SlabMark.moves]; simp only [fling_move, ruler_offset, show P.calibration.B=P.par.block from rfl]; by_cases e:i=j ; · subst i; simp
 simp [e, Ne.symm e]
lemma temple_reflect : P.reflectTest j (τEnd P v a y q)= τEnd P v ((plane j 0).motion a) y q:=Subtype.ext (temple_m P y j 0)
lemma temple_sweep : P.chartAll u (τEnd P v a y q)= τEnd P v (a+ζ • u) y q:=by
 let p(I:List Axis):Cover:= a+ζ • (fun (i:Axis)=> if i∈I then u i else (0:ℤ)); have h(I:List Axis)(e:I.Nodup):P.cruise I u (τEnd P v a y q)= τEnd P v (p I) y q:=by
    induction I with
    | nil=> change τEnd P v a y q= _; rw [show p []=a from by unfold p; simp <;> rfl]
    | cons j I ih=>
        rw [P.cruise_step,AlgHom.comp_apply,ih (List.Nodup.of_cons e), temple_step]; apply congrArg (fun a=> τEnd P v a y q); funext i; unfold p; by_cases w:i=j
        · subst i; rw [SlabMark.moves]; simp [List.nodup_cons.mp e|>.1, rulerTicks,nsmul_eq_mul]
        rw [SlabMark.moves]; simp [w]
 unfold chartAll; rw [h _ ordinate_one]; unfold p; simp only [ordinates,if_true]
noncomputable def choirWidth (P:Spine):ℕ:=petalD+P.sidesPerTick+(P.calibration.ℓ)+1
lemma choir_P : 0< choirWidth P:=by unfold choirWidth; positivity
variable (qa:ResidualPermit a)
include qa
private lemma choir_rW (D:ℕ) : Between T j (- ruler P.par.block*(D+P.sidesPerTick+P.calibration.ℓ+1:ℕ)) (ruler P.par.block*(D+P.sidesPerTick+P.calibration.ℓ+1:ℕ)) (pavilion (homeTag P a) D):=by
 intro z₁ h; let q:= (pav_v (homeTag P a) z₁ D).1 h j; have hp:= abs_le.mp (homeCost P a qa j); have h:0<ruler P.par.block:= ruler_gene _;
 let x:= D+P.sidesPerTick+P.calibration.ℓ+1
 have u : (↑x :ℤ) ≤ ruler P.par.block * (x:ℕ):= le_mul_of_one_le_left (by positivity) (by omega)
 unfold x at *; rw [neg_mul]; omega
lemma choir_R : Between T j (- ruler P.par.block*choirWidth P) (ruler P.par.block*choirWidth P) (pavilion (homeTag P a) petalD):= choir_rW P j qa _
noncomputable def soloV (v:ℕ)(q:payable P v 2)(a:Cover)(qa:ResidualPermit a)(y:Coords Wage4):P.Apron:= ⟨v,fun _=> choirWidth P, fun _=> choir_P P, τEnd P v (homeTag P a) y q, pavilion (homeTag P a) petalD,(tiltOwned P none q).1,(enclave_spec ..).2 (tiltOwned P none q).2, fun i=> choir_R P i qa⟩
lemma solo_width : (soloV P v q a qa y).realWidth P j= choirWidth P * P.macroStep v:=by change P.tock v _= _; rw [P.tock_price]; push_cast; rfl
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
