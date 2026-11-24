import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme
import YM.SU5.FiniteGaugeData.Tapestry.Cumulus
import Mathlib.LinearAlgebra.Dual.Lemmas
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude
open PiTensorProduct (tprod)

/-!
# The cross-resolution prescription (Euclidean buffered local tests)

Renew the requirements here: INSERT everything at the chosen observing levels,
ORIGINAL gauge & Cape/fields, chiral polarizations (one all-generation exterior
algebra). Read by PUSHing to finer levels -- multiply (ordered at the SAME
links and built on one FC, *not* product-state evaluation) with any tests at
that level. Then signed local reading there. The `tower` products are
COMMUTATIVE tensor polynomials on the even `screenHall`s. This is compatible
with the non-independence in the state: we don't quotient by any translations
or by mapping up a level. There is enough structure to define mixed centers &
full reflected forms and all their Gram matrices.

Vocab uses filtration by height `s`, support to come; off-height defined via
formal Pad (ℂ multiplier in each unaffordable slot), on heights theorem proves
instrument reading on actual "above" if no higher slot or, generally, on ALL
polynomials in `atHeight A n`. Off-height readings not considered physical.
Row state limit and full simultaneous limit use the same multislot space.
-/
set_option quotPrecheck false
section
variable (K:Calibration)
private def vacuumAux (A:Type*)[CommRing A][Algebra ℂ A][Nontrivial A]: Pad A:= let p:= Module.Projective.exists_dual_eq_one ℂ (one_ne_zero (α:=A)); ⟨p.choose,p.choose_spec⟩ -- dummy, not positive, no request about anything except one
def auxiliaryPad : Pad (Dome K):= vacuumAux _
-- some short names
abbrev Room := Cloud (Dome K) -- Ambig Room in YM. rename
abbrev FiniteGaugeDataPoly := Polynomials (Dome K)
abbrev boardedDB (n:ℕ) := shorter (Dome K) n
abbrev sequenceOf := ℕ→ Dome K
abbrev pureShot (x:sequenceOf K): Cloud (Dome K):= tprod ℂ x
lemma localDomeInj(n:ℕ): Injective (pinhole (Dome K) n):=by
  let D : Decking (Dome K) (fun n:ℕ=> Dome K) := ⟨fun i=> AlgHom.id .., fun i=> LinearMap.id, fun i=> rfl⟩
  intro x y p; have he(i:Dome K): D.crown (auxiliaryPad K) n (pinhole _ n i)=i := D.outcrop (auxiliaryPad K) n i; rw [←he x, p, he]
end
section
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ)
local notation "K" => tent Y H
local notation "P"=> auxiliaryPad (tent Y H)
variable (f:sequenceOf (tent Y H))(x:Cloud (Dome (tent Y H)))
-- NB Ward doesn't come by interpreting Families modulo projections because step depends on cutoff. This chain is FINITE and only paid through Y.uv k.
def tidalDressing : Decking (Dome (tent Y H)) (fun s:ℕ=> Ward (side Y i s)):=⟨fun s=>roving Y H s i,fun s=> (music Y s i k).toLinearMap,fun s=>rhythm_one Y s i (rawTariff Y s i k)⟩
-- to come join with nativeGauge

local notation "D"=>tidalDressing Y H i k
local notation "Ω" s:max=> Ward (side Y i s)
noncomputable def breathing : Cloud (Dome (tent Y H))→ₗ[ℂ] Ward (side Y i s):= (D).crown P s
noncomputable def taking : Cloud (Dome (tent Y H))→ₗ[ℂ] ℂ:= (savings Y (Y.uv k) i k).toLinearMap.comp (breathing Y H (Y.uv k) i k)
-- identities. Note P may be changed, they all coincide on the height-restricted span.
lemma breathing_pure (h:Enough s f): breathing Y H s i k (pureShot (tent Y H) f)= Decking.finish (tidalDressing Y H i k) s f:= (D).reckon_paid s P h
lemma breathing_fin (p: Pay Y s i k) (v: x∈boardedDB (tent Y H) s) : taking Y H i k x= savings Y s i k (breathing Y H s i k x):=
 Decking.partial_fin D s (Y.uv k) x P (fun s=>(savings Y s i k).toLinearMap) (fun s v=> congrArg ContinuousLinearMap.toLinearMap (conserve_exact Y s i k ⟨p.1,v⟩)) p.2 v
lemma taking_phys (p: Pay Y s i k) (v:x∈boardedDB (tent Y H) s): taking Y H i k x= Journey.compass Y i k s (attire (breathing Y H s i k x)) := by rw [breathing_fin _ _ _ _ _ _ p v,trueSavings _ _ _ _ _ p]
lemma recordedAt {u:Dome K}(p:Pay Y s i k): taking Y H i k (pinhole (Dome K) s u)= Journey.sharp Y H s i k u.val:= by
 rw [breathing_fin _ _ _ _ _ _ p (Altitude.short_pinhole s u)]; unfold breathing; rw [Decking.outcrop]; exact usesSharp Y H s i k u p
lemma taking_formula (p:Pay Y s i k)(v:x∈boardedDB (tent Y H) s):
    let B:= Y.voyage i; let l':= B.CapeT s; let w:= (B.X (Y.uv k)).gram s
    let Q:=partitionZ w Λ.U l'; let z:= breathing Y H s i k x
    let m:= fun v=> inner ℂ (Dial.mateK _) (acts ((attire z) (drawn l' v)) (denZ w Λ.U l' v))
    Integrable m (city (side Y i s)) ∧ Q ≠ 0 ∧ taking Y H i k x=(∫ v, m v∂city (side Y i s)) / Q:=by
 intro B l' w Q z m; rw [taking_phys _ _ _ _ _ _ p v]; exact funds Y s i k (Ward.signs z).env p.1 p.2
lemma tidal_start (f:sequenceOf K): attire ((tidalDressing Y H i k).finish 0 f)=exhibit Y H 0 i (f 0).val:=rfl
lemma tidal_rise (f:sequenceOf K)(W: Fields (side Y i (s+1))): let u:= (tidalDressing Y H i k).finish s f
    attire ((tidalDressing Y H i k).finish (s+1) f) W=(ascender Y s i k (attire u)) W * (exhibit Y H (s+1) i (f (s+1)).val) W:=by
 intro u; change attire (music Y s i k u) _ * _=_; rw [music,flowing]; rfl
-- no need s paid for finish because Dress uses original price even away. but use tidal_rise only at funded levels
lemma taking_scope (q:x∈FiniteGaugeDataPoly (tent Y H)): ∃ n:ℕ,x∈boardedDB (tent Y H) n:= Altitude.curve.mp q -- course-specific scope optional
lemma takingUnit (p:(Y.voyage i).kick≤ k): taking Y H i k 1=1:= by
 change savings Y (Y.uv k) i k ((D).crown (P) (Y.uv k) 1)=_; rw [Decking.crown1]; exact whereSavings Y (Y.uv k) i k ⟨p,le_rfl⟩
-- similar stories row/state limit
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} {T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}
namespace Fashion
variable (p:Fashion Y H a b I E L B T t)
include p
local notation "F"=> p.toExhibition
def rowDressing (p:Fashion Y H a b I E L B T t) : Decking (Dome (tent Y H)) (fun s=> Ward (side Y i s)):=⟨fun s=>roving Y H s i,fun s=> (rhythm Y s i (T s i)).toLinearMap,fun s=>rhythm_one Y s i (T s i)⟩ -- p include
local notation "r"=> rowDressing Y H i p
noncomputable def rowFinish : Cloud (Dome (tent Y H))→ₗ[ℂ] Ward (side Y i s):= (r).crown (P) s
private lemma agreedR(s:ℕ): ((Exhibition.refreshments Y H (s+1) i (F)).toLinearMap).comp ((rowDressing Y H i p).surge s)=(Exhibition.refreshments Y H s i (F)).toLinearMap:= congrArg ContinuousLinearMap.toLinearMap (p.rhythmRow Y H s i)
noncomputable def rowTake : Cloud (Dome (tent Y H))→ₗ[ℂ] ℂ:= Decking.fadeRead (r) (P) (fun s=> ((F).refreshments Y H s i).toLinearMap) (agreedR Y H i p)
lemma rowCall (v:x∈ boardedDB (tent Y H) s): rowTake Y H i p x= (F).refreshments Y H s i (rowFinish Y H s i p x):=(r).fate s x (P) _ _ v
lemma rowTakeUnit : rowTake Y H i p 1=1:= by rw [rowCall Y H 0 i _ p ((boardedDB ..).one_mem)]; unfold rowFinish; rw [Decking.crown1]; exact Exhibition.savingsUnit Y H 0 i (F)
lemma onRow {u:Dome K} : rowTake Y H i p (pinhole (Dome K) s u)= I s u.val i:=by rw [rowCall Y H s i _ p (Altitude.short_pinhole s u),rowFinish, Decking.outcrop]; exact Exhibition.refreshed Y H s i (F) u
end Fashion

namespace Exhibition
variable (d:Exhibition Y H a b I E L B)
def vistaDressing : Decking (Dome (tent Y H)) (fun _=> Dome (tent Y H)):=⟨fun s=>AlgHom.id ..,fun s=> d.liftD Y H s,fun s=>d.onePlaster Y H s⟩
local notation "F"=>vistaDressing Y H d
noncomputable def vistaFinish: Cloud (Dome (tent Y H))→ₗ[ℂ] Dome (tent Y H):= (F).crown (P) s
private lemma agreedV (s:ℕ): (planet Y H (s+1) d).comp ((vistaDressing Y H d).surge s)= planet Y H s d:= LinearMap.ext (fun v=>(planetTravel Y H s d v).symm)
noncomputable def vistaTake: Cloud (Dome (tent Y H))→ₗ[ℂ]ℂ:= Decking.fadeRead (F) (P) (fun s=>d.planet Y H s) (fun s=>agreedV Y H d s)
lemma vistaCall (v:x∈ boardedDB (tent Y H) s): vistaTake Y H d x= planet Y H s d (vistaFinish Y H s d x):= (F).fate s x (P) _ _ v
lemma vistaTakeUnit : vistaTake Y H d 1=1:= by rw [vistaCall Y H 0 _ d ((boardedDB ..).one_mem)]; unfold vistaFinish; rw [Decking.crown1]; exact planet1 Y H 0 d
lemma onVista {u:Dome K} : vistaTake Y H d (pinhole (Dome K) s u)= E s u.val:=by rw [vistaCall Y H s _ d (short_pinhole s u), vistaFinish, Decking.outcrop]; rfl
end Exhibition
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.rowTakeUnit
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.onRow
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.onVista
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.vistaTakeUnit
#print axioms YM.CF.Buffered.Afterglow.Tapestry.taking_formula
#print axioms YM.CF.Buffered.Afterglow.Tapestry.recordedAt
