import YM.SU5.Reconstruction.Brazier.Band
import YM.SU5.Reconstruction.Brazier.Snap
/-! Reading trajectory maintains both apertures and the entire original Wick prescription. Center part not conflated with repaint's aperture. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Hearth
open Fervor Tarmac SingleFrame
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
 Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (r:Hearth Y H G j)
local notation "Sp"=> r.spanMark Y H G j
local notation "ρ"=> r.roof
local notation "u₁"=> r.height
local notation "St"=> flank j (r.height:ℝ)
local notation "Nt"=> mirrorE j 0 '' St
variable (m u:ℕ) {w:ℕ}
local notation "N'" s:max=> side Y m s
local notation "Tz"=> Y.uv u
local notation "Lg"=> faceOf Y H m u
local notation "X'"=> Altitude.Cloud (Dome (tent Y H))
local notation "Ax"=> r.upper Y H G j
local notation "Bx"=> r.lower Y H G j
local notation "Qg" g:max => volumeAround Λ l g (r.outsideA Y H G j)
local notation "Qp" g:max => volumeAround Λ l g (r.outsideB Y H G j)
lemma spanFunded : (r.spanMark Y H G j)∈shorter (Dome K) r.roof:= ((shorter ..).mul_mem (short_pinhole r.roof r.token) (short_pinhole r.roof (aureole _ j 0 _)))
variable (q₀:∀ i:ℕ, PhaseChoice.FullDistances (volumeAround Λ l i (r.facePlate Y H G j)) (Journey.side Y m (r.roof+i))) -- no ScopeAir in Band.
structure WatchCost (m u w:ℕ) : Prop where
 right_hull : PhaseChoice.SupportedPhysically Λ l (r.roof+w) (volumeAround Λ l w (r.outsideA Y H G j)) (flank j r.height)
 left_hull : PhaseChoice.SupportedPhysically Λ l (r.roof+w) (volumeAround Λ l w (r.outsideB Y H G j)) (mirrorE j 0 '' flank j r.height)
 rightCost : AtSupport false (Satin.region (volumeAround Λ l w (r.outsideA Y H G j)) (Journey.side Y m (r.roof+w))) (faceOf Y H m u (r.roof+w) (r.upper Y H G j))
 leftCost : AtSupport false (Satin.region (volumeAround Λ l w (r.outsideB Y H G j)) (Journey.side Y m (r.roof+w))) (faceOf Y H m u (r.roof+w) (r.lower Y H G j))
 clear : PhaseChoice.FullDistances (volumeAround Λ l w (r.facePlate Y H G j)) (Journey.side Y m (r.roof+w))
 rightGauge : Buffered.covariant (faceOf Y H m u (r.roof+w) (r.upper Y H G j))
 leftGauge : Buffered.covariant (faceOf Y H m u (r.roof+w) (r.lower Y H G j))
 couple : faceOf Y H m u (r.roof+w) (r.lower Y H G j)=reflMark j 0 (faceOf Y H m u (r.roof+w) (r.upper Y H G j))
 owns : faceOf Y H m u (r.roof+w) (r.spanMark Y H G j)=faceOf Y H m u (r.roof+w) (r.upper Y H G j)*faceOf Y H m u (r.roof+w) (r.lower Y H G j)
lemma rightText {w:ℕ}(p:Tapestry.Pay Y (r.roof+w) m u):
 AtSupport false (Satin.region (Qg w) (N' (r.roof+w))) (faceOf Y H m u (r.roof+w) (r.upper Y H G j)):= by
 apply source Y H m u r.roof Ax (short_pinhole r.roof _) _ w p
 exact singleCover Y H m u (x:=r.token) (r.outsideAH Y H G j).1
lemma pairUp {w:ℕ}(p:Tapestry.Pay Y (r.roof+w) m u):
 faceOf Y H m u (r.roof+w) (r.lower Y H G j)=reflMark j 0 (faceOf Y H m u (r.roof+w) (r.upper Y H G j)):=by
 induction w with
 | zero=> unfold lower upper; rw [add_zero, singleRead,singleRead]; exact displayRef ..
 | succ w ih=>
   have h : Tapestry.Pay Y (r.roof+w) m u:=⟨p.1,(by have v:= p.2; omega)⟩
   rw [Nat.add_assoc r.roof w 1|>.symm, connection Y H m u (f:=Bx) (climbs _ (show ρ≤ρ+w by omega) (short_pinhole r.roof _)), connection Y H m u (f:=Ax) (climbs _ (show ρ≤ρ+w by omega) (short_pinhole r.roof _)),ih h, ascendTurn Y (r.roof+w) m u j 0 (p : Satin.PairIdx Y (r.roof+w) m u) ((rightText Y H G j r m u h).mono (Finset.subset_univ _)), mul_zero] -- tune
include q₀ in
lemma boots {w:ℕ}(p:Tapestry.Pay Y (r.roof+w) m u): WatchCost Y H G j r m u w:=by
 refine ⟨(r.outsideAH Y H G j).2.persists w,(r.outsideBH Y H G j).2.persists w, r.rightText Y H G j m u p,?_,q₀ w,?_,?_,r.pairUp Y H G j m u p,r.ExactSpan Y H G j m u p q₀⟩
 · exact source Y H m u _ Bx (short_pinhole r.roof (aureole _ j 0 r.token)) (singleCover Y H m u (x:=aureole _ j 0 r.token) (r.outsideBH Y H G j).1) w p
 · exact paid_coherence Y H m u (r.roof+w) p Ax (show (r.upper Y H G j) ∈well Λ K l true _ _ from r.upperMemo Y H G j) (climbs _ (by omega) (short_pinhole _ _))
 exact paid_coherence Y H m u (r.roof+w) p Bx (show (r.lower Y H G j) ∈well Λ K l true _ _ from r.lowerMemo Y H G j) (climbs _ (by omega) (short_pinhole _ _))
variable (a:Tarmac)
local notation "F"=>r.centralT Y H G j a
structure InsideCost (x:Altitude.Cloud (Dome (tent Y H)))(m u w:ℕ):Prop where
 hull : PhaseChoice.SupportedPhysically Λ l (r.roof+w) (volumeAround Λ l w (r.centralT Y H G j a)) (a.land Λ l)
 charge : AtSupport false (Satin.region (volumeAround Λ l w (r.centralT Y H G j a)) (Journey.side Y m (r.roof+w))) (faceOf Y H m u (r.roof+w) x)
 gaugeCost (V':Set RSpace) : x∈ questions Λ l (tent Y H) true V' → Buffered.covariant (faceOf Y H m u (r.roof+w) x)
 dist : PhaseChoice.FullDistances (volumeAround Λ l w (r.facePlate Y H G j ∪r.centralT Y H G j a)) (Journey.side Y m (r.roof+w))
 insertion : faceOf Y H m u (r.roof+w) (x*r.spanMark Y H G j)=faceOf Y H m u (r.roof+w) x * faceOf Y H m u (r.roof+w) (r.spanMark Y H G j)
lemma insideNow {g:ℝ}(p: Sightline Y H G j r g a)(q:r.LongReach Y H G j a m) {w:ℕ}(h:Tapestry.Pay Y (r.roof+w) m u) {x:Altitude.Cloud (Dome (tent Y H))}{b:ℝ}(z:Pocket (tent Y H) a.book a.roof b x): InsideCost Y H G j r a x m u w:=by
 refine ⟨(r.centralHere Y H G j a p.later.le).persists w,?_,fun u' t=> paid_coherence Y H m u _ h x (show x∈ well Λ K l true _ _ from t) (climbs _ (p.later.le.trans (Nat.le_add_right ..)) z.funded), q w,?_⟩
 · refine source Y H m u _ _ (climbs _ p.later.le z.funded) (r.centralRecord Y H G j a m u ⟨h.1,?_⟩ z p.later.le) w h
   exact (Nat.le_add_right ..).trans h.2
 exact r.ExactRead Y H G j a m u h q z p -- arg order
-- all subsequent use with the progressing trajectory; at TOP also can collapse tags.
end Hearth
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
