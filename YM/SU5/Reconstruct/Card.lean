import YM.SU5.Reconstruct.Symmetry
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 620000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

variable (s:ℕ) (j:Axis)
/-!
# Physical ordered charts

Any finite local queries in Pol and regions can be billed in each fixed axis
whenever the regions admit strictly separated intervals after translating the
queries into place. `AxisAperture` expresses precisely the support condition
in physical coordinates -- a priori no mention of a common height. The
entire billed interval is used to compute the ordered products.

One presentation of a thick mark has an Origin relative to base shape and span appears
only when setting up a presentation. Centers/real-time moves not assumed to
shrink or preserve energy. -/
local notation "M"=> timeMesh Λ
local notation "Ω"=> placement Λ
local notation "m₀" k:max=> meshPos Λ k
local notation "N"=> physPos Λ
local notation "Pn" k:max U:max=> PolAt Y H k U
-- Shift DOWN for the entry which starts at 0. Store low relative to base position of mark. Strict=true
structure IndexEnvelope (R:ℕ→Type _)(p:Prop)(printC: ∀ (o:Cover)(n:ℕ),R n → Prop)(checkC:Cover→ℕ→Prop) where
    origin_: Cover
    span : ℕ
    paidH : 0<span
    cargo : R span
    prepared : p
    points : printC origin_ span cargo
    encloses : checkC origin_ span
noncomputable def StripCard (U:Set RSpace) (x:Pol Y H U) :=
  IndexEnvelope (Entry Y H s j true) (x.val∈PolAt Y H s U)
    (fun origin_ _ cargo=> cargo.val.val = (march Y H (-origin_) ((vistaFinish Y H s D.toExhibition) x.val)).val)
    (fun origin_ span=>∀ z∈ U, (physPos Λ (meshPos Λ s origin_)) j ≤ z j ∧ z j ≤ (physPos Λ (meshPos Λ s origin_)) j + bell (timeMesh Λ) s span)
namespace StripCard
variable {s j}{U:Set RSpace} {x:Pol Y H U}(K':StripCard Y H D s j U x)
section
variable {Y H D}
noncomputable abbrev origin_ : Cover:= K'.1
noncomputable abbrev span : ℕ:= K'.2 -- .2 projected index colimit: number notation structure widths? test
lemma paidH : 0<K'.span := K'.3
noncomputable abbrev cargo : Entry Y H s j true K'.span:= K'.4
include K' in
lemma prepared : x.val∈ PolAt Y H s U:= K'.5
lemma points : K'.cargo.val.val=(march Y H (- K'.origin_) ((vistaFinish Y H s D.toExhibition) x.val)).val:= K'.6
lemma encloses : ∀ z∈U, (physPos Λ (meshPos Λ s K'.origin_)) j ≤ z j ∧ z j ≤ (physPos Λ (meshPos Λ s K'.origin_)) j + bell (timeMesh Λ) s K'.span := K'.7
end
variable (u:ℕ)(p : s ≤ u)
def fromBase : placement Λ:= meshPos Λ s K'.origin_
def lastBit : Cover:= K'.span • step j
def breadthOn : placement Λ:= meshPos Λ s (lastBit Y H D K')
def finishBit : placement Λ:= fromBase Y H D K'+breadthOn Y H D K'
lemma broad_own : physPos Λ (breadthOn Y H D K') j = bell (timeMesh Λ) s K'.span:=by change bell M s _=_; simp [lastBit]
lemma broad_ne {i:Axis}(h:i≠j) : (breadthOn Y H D K') i= 0:=by change notch M _ (lastBit Y H D K' i)=_; simp [lastBit,h,notch_zero]
lemma glassSize : 0< physPos Λ (breadthOn Y H D K') j:=by
  rw [broad_own]; unfold bell; exact mul_pos (by exact_mod_cast K'.paidH) (mill_pos M _)
variable (v:RSpace)
def starts : RSpace:= physPos Λ (fromBase Y H D K') + v
def ends : RSpace:= physPos Λ (finishBit Y H D K') + v
lemma contained : ∀ w∈ carried v U, starts Y H D K' v j ≤ w j ∧ w j ≤ ends Y H D K' v j:=by
 rintro _ ⟨w,p,rfl⟩; obtain ⟨h,t⟩:= K'.encloses w p; unfold starts ends finishBit; rw [map_add]; simp only [Pi.add_apply,broad_own, fromBase]; constructor <;> linarith
lemma before_h : ends Y H D K' v j= starts Y H D K' v j + bell (timeMesh Λ) s K'.span:=by
 unfold ends finishBit starts; rw [map_add, Pi.add_apply,Pi.add_apply, Pi.add_apply,broad_own]; ring
-- High entry from same calibration with ID at u; positions unchanged
lemma pointsH : (furnished Y H s G.history j true K'.span K'.cargo u p).val.val=(march Y H (-netcast Λ s u K'.origin_) ((vistaFinish Y H u D.toExhibition) x.val)).val:=by
  have hr {X':Set RSpace}{q:O}(h:q∈ Pn s X') : ((P₀ u) q).val=stream Y H G.refine s (u-s) ((vistaFinish Y H s D.toExhibition q).val):=by
    induction u,p using Nat.le_induction with
    | base => rw [Nat.sub_self]; rfl
    | succ u p ih=>
       rw [show (P₀ (u+1)) q= liftD Y H u D.toExhibition ((P₀ u) q) from (Decking.joins _ u q _ (inside_budget Y H (polAt_up Y H p h))), lifts_here Y H V G, ih, show u+1-s=u-s+1 by omega, stream_step, show s+(u-s)=u by omega]
  let X':= parcelTo Y H D s (-K'.origin_) x.val
  have hx: (P₀ s) X'=march Y H (-K'.origin_) ((P₀ s) x.val):=tallied Y H D _ _ _
  have hv:(P₀ u) X'=march Y H (-netcast Λ s u K'.origin_) ((vistaFinish Y H u D.toExhibition) x.val):=by
    unfold X'; rw [talliedUp Y H D G _ _ _ p K'.prepared]; have he: netcast Λ s u (-K'.origin_) = -netcast Λ s u K'.origin_:= funext fun i=> by simp [netcast,castor]
    rw [he] -- one-line have tactic risk
  change stream Y H G.refine s _ (K'.cargo.val.val)=_
  rw [←hv,hr (parcel_mem Y H D _ _ K'.prepared),hx,K'.points]
noncomputable def higher : StripCard Y H D u j U x where
    origin_:=netcast Λ s u K'.origin_
    span:= Λ.R.L.val^(u-s)*K'.span
    paidH:= Nat.mul_pos (pow_pos Λ.R.L.property _) K'.paidH
    cargo:= furnished Y H s G.history j true K'.span K'.cargo u p
    points:=pointsH Y H D G K' u p
    prepared := polAt_up Y H p K'.prepared
    encloses:=by
      have he : ((Λ.R.L.val^(u-s)*K'.span:ℕ):ℤ)=castor M s u (K'.span:ℤ):=by unfold castor timeMesh; push_cast; rfl
      rw [netcast_up _ _ _ p,he,refineZ M s u p]
      exact K'.encloses
lemma broad_h : breadthOn Y H D (higher Y H D G K' u p)=breadthOn Y H D K':=by
  ext1 i
  by_cases h:i=j
  · subst i
    change notch M u (lastBit Y H D (higher Y H D G K' u p) j)=notch M s (lastBit Y H D K' j)
    have he : lastBit Y H D (higher Y H D G K' u p) j=castor M s u (lastBit Y H D K' j):=by
      simp only [lastBit,Pi.smul_apply]; rw [show step j j= (1:ℤ) by simp]; simp only [nsmul_eq_mul,mul_one]
      change ((Λ.R.L.val^(u-s)*K'.span:ℕ):ℤ)=castor M s u (K'.span:ℤ); unfold castor timeMesh; push_cast; rfl
    rw [he,notch_up M s u p]
  rw [broad_ne Y H D _ h,broad_ne Y H D _ h]
lemma first_h : fromBase Y H D (higher Y H D G K' u p)=fromBase Y H D K':= netcast_up _ _ _ p _
lemma starts_h : starts Y H D (higher Y H D G K' u p) v=starts Y H D K' v:=by unfold starts; rw [first_h]
lemma ends_h : ends Y H D (higher Y H D G K' u p) v=ends Y H D K' v:=by unfold ends finishBit; rw [broad_h,first_h]
end StripCard

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
