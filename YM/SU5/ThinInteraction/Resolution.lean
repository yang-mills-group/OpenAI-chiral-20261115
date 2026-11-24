import YM.SU5.ThinInteraction.Spectrum

/-!
# The body actually used by a reflected pair price.

Only ported for reflected across time 3 at zero (suffices e.g. for our interaction tests).
Use formula of TeX exactly. `pp` the port of the position-dependent carrier.

-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 220000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
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
open YM.SatinThin
namespace Thinning
open Set Aria Six Casting
open scoped BigOperators
variable (P:Spine) (x:P.Spectrum0 3) (s n t:ℕ) (Z:Lead.Clan)
local notation "S" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "W" => ShopP P s n
local notation "T" => timeMesh P.par
local notation "d" r:max => offset false r
local notation "τ" => P.probeWidth s n 3
local notation "M" => P.singleState 3 t x
local notation "A" => P.FTest Z s n
local notation "Y" => P.RTest Z s n
section positions
variable {P s n}
-- implement offset d for forward mark, even when not yet ready take index 0
lemma offset_price (r:ShopP P s n): offset false r∈ (marks (timeMesh P.par)) :=
  (marks T).neg_mem (show r.val∈(marks T) from r.prop.2) -- defin
local notation "i₀" => W
lemma offset_abs (r: W) : |d r| < τ := by change |-(r:ℝ)| < τ; rw [abs_neg]; exact abs_lt.mpr r.prop.1

def invests (r : ShopP P s n): Prop:= ∃ i:ℤ, bell (timeMesh P.par) t i=offset false r
lemma invests_late (r: ShopP P s n) : ∀ᶠ t in atTop, invests t r:=by
 obtain ⟨w,i,k⟩:= (show offset false r ∈ marks (timeMesh P.par) from offset_price r)
 filter_upwards [eventually_ge_atTop w] with u h
 exact ⟨castor T w u i,(refineZ T w u h i).trans k⟩
variable (c:ShopP P s n →₀ ℝ)
def covered : Prop := s ≤ t ∧ ∀ i∈ c.support, invests t i
lemma coverable : ∀ᶠ t in atTop, covered t c:= (eventually_ge_atTop s).and ((eventually_all_finset c.support).2 (fun r _=> invests_late r))
variable (r:ShopP P s n)(w:Cover)
noncomputable def notchCharge : ℤ:= if h: invests t r then h.choose else 0
def putCharge (t:ℕ)(r:ShopP P s n)(w:Cover) : Cover:= Function.update w 3 (w 3 + notchCharge t r)
lemma markHeight (e:invests t r): P.meshPose t (putCharge t r w) 3 = P.meshPose t w 3 + offset false r:= by
 change bell T t ((putCharge t r w) 3) = _; rw [putCharge,update_self,bell_add]; exact congrArg (bell T t (w 3)+·) (show bell T t (notchCharge t r)=offset false r from by rw [notchCharge, dif_pos e]; exact e.choose_spec)
lemma markTruck (x:P.Spectrum0 3): P.truck 3 x (P.vtile t (putCharge t r w))= P.truck 3 x (P.vtile t w):=by
  apply congrArg ((P.voyageF 3 x).raw (look 3))
  funext i
  change notch (T) t (putCharge t r w i.val)=_
  rw [putCharge,update_of_ne i.prop]; rfl
lemma width_paid' {y:ℝ}(e:2*τ<y): τ < y +offset false r:=by linarith only [e,(abs_lt.mp (offset_abs r)).1]
lemma width_paid (e:2*τ< P.meshPose t w 3) (h:invests t r): τ < P.meshPose t (putCharge t r w) 3:= by rw [markHeight t r w h]; exact width_paid' r e
end positions

section deposit
variable {P s n x Z}{a:ℝ}(F : SampleDose)(p : Portfolio x s n a Z) (c:ShopP P s n →₀ ℝ)

abbrev momentum (k: Fin 3 → ℤ) : Space3 := WithLp.toLp 2 fun i:Fin 3=>((k i:ℤ):ℝ)
-- plane phase on spatial dot with k, at **center**, unchanged in the whole offset sum.
def pp (y:Vantage) : ℂ:= Complex.exp (((p.m:ℝ) * (y 3):ℝ)- ((↑(inner ℝ (momentum p.k) (spacePart y)):ℂ)*Complex.I)) -- check spacePart expects args
lemma pp_cont : Continuous (pp p) := by unfold pp; fun_prop

def chargePlus (i:Cover) : P.Test:= pp p (P.meshPose t i) • ∑ r∈ c.support, ((c r:ℝ):ℂ) • P.issuing t (P.FTest Z s n) (putCharge t r i)
def deploy : P.Test:= ∑ i∈P.usedGrid t F,P.activation t F i • chargePlus t p c i

def roofed (P:Spine)(s n:ℕ)(F:SampleDose) := ∀ i∈tsupport F.val,2*P.probeWidth s n 3 < i (3:Axis)
#check @deploy
#check @momentum
#check @spacePart

lemma neutral_plus : deploy t F p c ∈ enclave P.calibration := by
  exact Subalgebra.sum_mem _ (fun i _=> Subalgebra.smul_mem _
    (Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun r _=> Subalgebra.smul_mem _ (P.issuing_color t _ _) _)) _) _)

lemma pose_disjoint (p q:Cover)(h:τ<P.meshPose t p 3)(e:τ<P.meshPose t q 3)(W':Lead.Clan):
    Disjoint (P.Aperture (P.RTest Z s n) (P.meshPose t (opposeQ 3 p)))
      (P.Aperture (P.FTest W' s n) (P.meshPose t q)):= by
    rw [P.tile_reflect]; refine Set.disjoint_left.mpr (fun y u v=>?_)
    specialize u 3; specialize v 3; rw [show opposeR 3 (P.meshPose t p) 3= -P.meshPose t p 3 from if_pos rfl] at u
    have ht: |y 3 - -P.meshPose t p 3| ≤ τ := u; have hh:|y 3 - P.meshPose t q 3| ≤ τ:= v; linarith only [(abs_le.mp ht).2,(abs_le.mp hh).1,h,e]

lemma reflected_sum {ι:Type*} (s:Finset ι)(f:ι→ P.Test): P.reflectTest 3 (∑ i∈s,f i)=∑ i∈s,P.reflectTest 3 (f i):=by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; simpa only [zero_smul, star_zero] using P.scale_mirror 0 0 3
  | @insert i s h ih => rw [sum_insert h,sum_insert h,P.sum_mirror,ih]

lemma split_deploy (g:roofed P s n F) (e:n>P.calibration.ℓ) (u:covered t c)
    (G:SampleDose) {Z':Lead.Clan}{b:ℝ}(p':Portfolio x s n b Z') (c':ShopP P s n→₀ℝ) (q: roofed P s n G) (v:covered t c')
    (X : P.Test→ₗ[ℂ]ℂ) (h:Factors P.calibration X) (m: MatterWard P.calibration X ∨ GaugeWard P.calibration X):
    X (P.reflectTest 3 (deploy t F p c)* deploy t G p' c') = 0 := by
  unfold deploy; rw [reflected_sum, Finset.sum_mul,map_sum]; apply Finset.sum_eq_zero
  intro i a; rw [Finset.mul_sum,map_sum]; apply Finset.sum_eq_zero
  intro j b; rw [P.scale_mirror,smul_mul_assoc,mul_smul_comm,map_smul,map_smul]
  suffices hy : X (P.reflectTest 3 (chargePlus t p c i) * chargePlus t p' c' j) = 0 by rw [hy, smul_zero,smul_zero]
  unfold chargePlus; rw [P.scale_mirror,smul_mul_assoc,mul_smul_comm,map_smul,map_smul]
  suffices ht : X (P.reflectTest 3 (∑ r ∈ c.support, ((c r:ℝ):ℂ) • P.issuing t A (putCharge t r i)) *
    (∑ r∈ c'.support, ((c' r:ℝ):ℂ) • P.issuing t (P.FTest Z' s n) (putCharge t r j)))=0 by rw [ht,smul_zero,smul_zero]
  rw [reflected_sum, Finset.sum_mul,map_sum]; apply Finset.sum_eq_zero
  intro r x; rw [Finset.mul_sum,map_sum]; apply Finset.sum_eq_zero
  intro r' y; have hr:= width_paid t r i (g _ ((P.usedPose t F i).1 a)) (u.2 r x); have hs:= width_paid t r' j (q _ ((P.usedPose t G j).1 b)) (v.2 r' y)
  have hh:= pose_disjoint (Z:=Z) t _ _ hr hs Z'
  rw [P.scale_mirror,smul_mul_assoc,mul_smul_comm,map_smul,map_smul,← P.issue_reflect]; rw [P.msplit_pair Z.2 t h m (P.RTest Z s n) (P.FTest Z' s n) (P.sensor_mirror Z.2 3 _ (P.body_senses Z s n e)) u.1 _ _ hh v.1,smul_zero, smul_zero] -- rw exact after change
end deposit
#print axioms split_deploy
end Thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
