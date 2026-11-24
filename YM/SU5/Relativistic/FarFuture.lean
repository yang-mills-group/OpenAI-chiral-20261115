import YM.SU5.Relativistic.PreparationRoot
import YM.SU5.Relativistic.Joint
/-! # Distant neutral boundary marks reaching every selected ground.

At resolution t large enough, can choose gauge invariant f so literally
actor(t,f) approximates a ground vector. Then shove through any later
slab. Hold widths (level-zero clock basis) isolated outside center.
SPREAD transverse not constrained. Measurements still on the same Course.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition MeshClock
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
section precursor
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V: Universal Y H i k I E)
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j:Axis)(C:Arena Y H G.history.circuit j 0 false)
local notation "ω"=> floorV Y H G.history.circuit j 0 false C
local notation "Φₛ" s:max=> Tower.Field Y H s j 0 false
local notation "κ" s:max=> actor Y H s G.history.circuit j 0 false C
local notation "Ω"=> groundRoom Y H V G.history j false C
local notation "Λ₀"=> timeMesh Λ
local notation "H₀"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "B" n:max w:max z:max h:max=> boxOp Y H V n G.history G.clipped j false C w z h

variable {n s : ℕ} {ε:ℝ}
include V
lemma populated_at (u : Ark.Ht Y H G.history.circuit j 0 false C) (e : 0 < ε): ∀ᶠ s in atTop,
    ∃ x : Tower.Field Y H s j 0 false, ‖(actor Y H s G.history.circuit j 0 false C) x-u‖ ≤ ε ∧
    CovCover K x.val ∧ ∀ m, Continuous (x.val m) := by
  obtain ⟨x,⟨⟨n,g⟩,rfl⟩,p⟩:= Metric.mem_closure_iff.mp (allActors Y H V G.history j false C u) ε e
  have hp: dist u ((κ n) g) < ε := p
  filter_upwards [eventually_ge_atTop n] with s hs
  let l₀(s) (p:n ≤ s):Φₛ s:= Raise Y H G.history.circuit j 0 false n s p g
  obtain ⟨w,z,f,v⟩:= artist_fits_slab Y H s j false (l₀ s hs)
  have he: (B s w f z) ω=(κ n) g:= (lays Y H V s G.history G.clipped j false C w f z).trans (by rw [v]; exact join_actor Y H V G.history.circuit j 0 false C n s hs g)
  obtain ⟨S,h,t⟩:= f.property; obtain ⟨y,r,k⟩:= renovate Y H V G j C S s w t z f h
  have hq:Tendsto (fun i=> (κ s) (y i).val) atTop (𝓝 ((κ n) g)) := by
     rw [← he]; simp_rw [← lays Y H V s G.history G.clipped j false C w _ z]
     let F: stationC Y H V G j false C → H₀:= fun b=> b.val ω
     have hx:Continuous F := Continuous.clm_apply continuous_subtype_val continuous_const
     exact (hx.tendsto (boxElement Y H V G j false C s w f z)).comp k
  obtain ⟨i,a⟩ := (hq.eventually ((Metric.isOpen_ball (x:=u) (ε:=ε)).mem_nhds (x:=(κ n) g)  (Metric.mem_ball.mpr ((dist_comm _ _).trans_lt hp)))).exists
  refine ⟨(y i).val, ?_, (r i).2.1,(r i).2.2⟩
  simpa only [dist_eq_norm] using (a : dist ((κ s) (y i).val) u < ε).le

structure Future (j:Axis)(n:ℕ) where
  t : ℕ
  arrival : n≤ t
  mark : Tower.Field Y H t j 0 false
  singlet : CovCover (tent Y H) mark.val
  S : Finset Cover
  safe : InTest (tent Y H) true S false mark.val
  forward : Tower.region j 0 (tent Y H).ℓ S
variable {n:ℕ} -- same?
namespace Future
omit V
variable (x:Future Y H j n)
local notation "L"=> Λ.R.L.val
local notation "b₀"=> ruler Λ.block
local notation "tβ"=>x.t
def root : Ark.Ht Y H G.history.circuit j 0 false C := actor Y H x.t G.history.circuit j 0 false C x.mark
def wait : ℕ := Λ.R.L.val^x.t*n
def irradiant (m:ℕ):Tower.Field Y H x.t j 0 false:= tick Y H x.t j 0 false (2*m) x.mark
def emit : Tower.Field Y H x.t j 0 false := irradiant Y H j x (wait Y H j x)
local notation "T" k:max=> irradiant Y H j x k
local notation "Tᵣ"=> emit Y H j x
def opening := plow (tent Y H) j (wait Y H j x) x.S
def closing := reflectedBox j 0 (opening Y H j x)
local notation "S₁"=> opening Y H j x
local notation "S₂"=> closing Y H j x
lemma emit_extent : InTest K true (S₁) false (emit Y H j x).val:=by
    unfold emit irradiant; rw [timed_apply]
    exact flow_port _ _ _ x.safe
lemma emit_singlet : CovCover K (emit Y H j x).val:=by
    unfold emit irradiant; rw [timed_apply]
    exact chime_cov _ _ _ x.safe x.singlet
lemma op_far (u:Cover)(h:u∈ S₁): b₀*(x.wait Y H j:ℤ)+ ((K).ℓ:ℤ) ≤ u j:=by
    obtain ⟨v,c,rfl⟩:= plow_stays K j _ x.S h
    rw [moves,if_pos rfl]; change _ ≤ v j+b₀*_
    have he : 0+((K).ℓ:ℤ) ≤ v j:=x.forward v c
    linarith only [he]
lemma cl_far (u:Cover)(h:u∈ S₂): u j+(K).ℓ ≤ -(b₀*(x.wait Y H j:ℤ)):=by
    obtain ⟨t,h,g⟩:= reflect_stays j 0 (S₁) h; rw [g,if_pos rfl]; have hq:=op_far Y H j x t h
    linarith only [hq]
-- physical reading of time also in Heat's units. both workers.
local notation "P" S:max => footprint Λ l tβ S
local notation "μ"=> gaugeMesh Λ tβ
lemma when_wait : (whenly Λ₀ 0 n:ℝ)= (b₀:ℝ)*(wait Y H j x:ℝ)*gaugeMesh Λ x.t:=by
    rw [double_clock_calibration]; unfold gaugeMesh wait; push_cast
    have ht:(L:ℝ)≠0:=by positivity
    field_simp
lemma labels_far : P (S₁)⊆ {u| (whenly Λ₀ 0 n:ℝ) ≤ u j} ∧ P (S₂)⊆ {u| u j ≤ -(whenly Λ₀ 0 n:ℝ)} := by
    let M:= (((b₀*(x.wait Y H j:ℤ)):ℤ):ℝ); let tM:= (whenly Λ₀ 0 n:ℝ)
    have hM:tM=M*μ:= by unfold M; rw [Int.cast_mul,Int.cast_natCast]; exact when_wait Y H j x
    have ht : 0 ≤ μ := (gaugeMesh_pos _ _).le
    constructor
    · intro u h
      obtain ⟨t,p⟩:= Set.mem_iUnion.mp h; obtain ⟨t',p⟩:= Set.mem_iUnion.mp p
      have he: M+ (reserve Λ l:ℝ)≤ (t j:ℝ):= by
        unfold M; exact_mod_cast op_far Y H j x t t'
      refine le_trans ?_ ((p:u∈collar Λ l _ t).1 j)
      change tM ≤ _; rw [hM,lower_gauge]; exact le_sub_iff_add_le.mpr (by simpa only [add_mul,gaugePosition] using mul_le_mul_of_nonneg_right he ht)
    intro u h; obtain ⟨t,p⟩:= Set.mem_iUnion.mp h; obtain ⟨t',p⟩:= Set.mem_iUnion.mp p
    have he : (t j:ℝ)+ (reserve Λ l:ℝ)≤ -M:=by unfold M; exact_mod_cast cl_far Y H j x t t'
    refine le_trans ((p:u∈collar Λ l _ t).2 j) ?_
    change _ ≤ - tM; rw [hM,upper_gauge]; exact (by simpa only [neg_mul,add_mul,gaugePosition] using mul_le_mul_of_nonneg_right he ht)

include V
lemma irradiates (m : ℕ) : advance Y H V G.history.circuit j 0 false C (whenly Λ₀ tβ m) (root Y H G j C x) = (κ tβ) (T m):=by
    unfold root irradiant; rw [advance_at,limited_time Y H V x.t G.history.circuit j 0 false C (2*m) le_rfl,amount_reset]
lemma attends (u:Ω)(h:‖root Y H G j C x - (u.val:H₀)‖ ≤ ε) (m:ℕ) : ‖(κ tβ) (T m)-(u.val:H₀)‖ ≤ ε := by
  let O:=advance Y H V G.history.circuit j 0 false C
  let t:=whenly Λ₀ tβ m
  have he : O t u.val=u.val := floor_rise Y H V G.history j false C u t
  calc
   _ = ‖O t (root Y H G j C x-u.val)‖ := by rw [map_sub, he, show O t (root Y H G j C x)=_ from irradiates Y H V G j C x m]
   _ ≤ ‖root Y H G j C x-u.val‖ := (ContinuousLinearMap.le_opNorm (O t) _).trans (mul_le_of_le_one_left (norm_nonneg _) (advance_small Y H V G.history.circuit j 0 false C t))
   _ ≤ _ := h
lemma record (u: groundRoom Y H V G.history j false C) (n:ℕ)(hp:0 < ε):
    ∃ x:Future Y H j n, ‖root Y H G j C x - (u.val:H₀)‖ ≤ ε := by
  obtain ⟨s, p, y,t,k,w⟩:= ((eventually_ge_atTop n).and (populated_at Y H V G j C u.val hp)).exists
  obtain ⟨S,h,g⟩ := ((purpose_ok ..).mp y.property).1
  have hg : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S := g
  rw [area0] at hg; exact ⟨⟨s,p,y,k,S,h,hg⟩,t⟩
end Future
end precursor
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Future.attends
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Future.record
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Future.labels_far
