import YM.SU5.Reconstruction.Pitch.Coupon
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i qc : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i qc I E)
  (G : GroundExtension (i := i) (k := qc) (E := E) Y H)
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

variable (a:Axis) (c : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
local notation "τ"=> marks (loomD Λ)
local notation "Δ"=> Atlas Λ
local notation "A"=> Warden Y H V G a c
local notation "H₀" x:max=> indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S₀" x:max=> ride Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "X₀" x:max=> OSvector Y H V G j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "I₀"=> flank j 0
local notation "F"=> Domain Y H G false (flank j 0)
local notation "V₀" x:max=> osValue Y H V G a (c a) x
local notation "W" p:max x:max=> leader Y H V G a c p x
variable (p:Atlas Λ) (x y: Warden Y H V G a c) (k:0≤ p j) (h:leader Y H V G a c p x=y)
local notation "px" p:max=> pitches Λ j p
local notation "κ" p:max=> constellation p K
open ConePrice SelectionAnalysis
local notation "Pf" p:max k:max x:max=> promenadeFront Y H G j p x k
local notation "T"=> transportT Y H V G a c j p x y k h
open OS.Semigroup
-- In-product closures comparing at SAME clock, but opposite center observers. Actual discrimination using Joint origin (commuting filtered pricing in CStar reps). Key: produce any PAIR of VACUUM amplitudes via the dense precursor data at all future τ stamps, w/out Full.
open SelectionAnalysis
variable (r:ℝ)(u:0≤r)
local notation "FF"=> Domain Y H G true (flank j r)
local notation "Vf" x:max=> displacement Y H V G.history G.clipped a false (c a) x j (c j)
local notation "ρ" x:max=> procession Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S"=>driveAlgebra Y H V G.history G.clipped j false (c j)
local notation "Hp"=> ((H₀ x).space × (H₀ y).space)
local notation "Ω" x:max=>doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
variable (v: weft Λ)(v₀:0≤v)
variable (Vx : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)))
local notation "P'"=> dressing Y H V G a c j x y r u
local notation "Ds"=> acquit Y H V G a c j x y r u
local notation "uY" f:max=> nearer Y H G j r u f
local notation "θ'"=> flipMark j K
open LightBudget
-- Finish ISSUE. Require only the relevant axis Certs. No new compact torus object substituted.
lemma alwaysAt (h : Absent Y H V G a c j x) : leader Y H V G a c (eject j v) x = x:=by
 by_cases p:0 ≤ v; · exact (h v p).1
 have ht:= (h (-v) (neg_nonneg.mpr (le_of_not_ge p))).1; rw [eject_neg,inverse_lead] at ht; exact ht
lemma spent_clock (f: F)(h_:Absent Y H V G a c j x) : (X₀ x) (prepareTurn Y H G j v f v₀)=(S₀ x).E (Real.toNNReal (v:ℝ)) ((X₀ x) f):=by rw [chargeT_native Y H V G a c j x x v v₀ (alwaysAt Y H V G a c j x v h_),(h_ v v₀).2]; rfl
section frame
-- budget on chosen χ. full
variable (TC: saunters Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))= ⊤)
 (TF: ConePrice.Forward (peninsula Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))))
variable (s:Trans j) (h_ : Absent Y H V G a c s.val x)
local notation "J₀"=>s.val
-- a k-axis spacelike budget: for v with D enough. fixed f,g in flank high & low. Forth narration. No reader h hidden, uses proof paid. Comparison lemma.
local notation "St"=> peninsula Y H V G.history G.clipped j false (c j) (Vf x)
local notation "Ft"=> fort Y H V G.history G.clipped j false (c j) (Vf x)
local notation "pu"=> coreOs Y H V G j (c j) (Vf x)
local notation "Λ₀"=> flank s.val 0
local notation "Vf'"=>displacement Y H V G.history G.clipped a false (c a) x s.val (c s.val)
local notation "U₁" q:max=> transportT Y H V G a c j (eject s.val q) x x
lemma space_v (v:τ) : 0 ≤ eject s.val v j:= by simp [s.property.symm]
include h_ in
noncomputable def sight (v:τ) := transportT Y H V G a c j (eject s.val v) x x (space_v j s v) (alwaysAt Y H V G a c s.val x v h_)
local notation "Sp"=> sight Y H V G a c j x s h_
local notation "D₁"=> Domain Y H G false (flank s.val 0)
local notation "S₁"=> ride Y H V G.history G.clipped s.val false (c s.val) Vf'
local notation "X₁"=> OSvector Y H V G s.val (c s.val) Vf'
include h_
lemma spend_space (f:Domain Y H G false (flank j 0)): (X₀ x) (bystander Y H G j v s f)= Sp v ((X₀ x) f):=by
 let q:= eject s.val v; let p:= space_v j s v; have e := alwaysAt Y H V G a c s.val x v h_
 have h:= native_taste Y H V G a c j q x x p e f; rw [show pitches Λ j q=0 from ?_, (S₀ x).eZero] at h; swap; · unfold pitches q; simp [s.property.symm]
 exact Eq.symm (h.trans (congrArg (X₀ x) (Subtype.ext (cover_solo ..))))
variable (d : weft Λ) (f g:Domain Y H G false (flank j 0)) (p1:f.val∈ Domain Y H G false (lowland s.val 0)) (p2:g.val∈Domain Y H G false (flank s.val (d:ℝ)))
include p1 p2
lemma steady_hall : ∃ f' g': Domain Y H G false (flank s.val 0),∀ q: marks (loomD Λ), 0≤ q+d →
    inner ℂ ((X₀ x) f) (sight Y H V G a c j x s h_ q ((X₀ x) g))= inner ℂ (X₁ f') ((S₁).E (Real.toNNReal (((q+d:τ)):ℝ)) (X₁ g')):=by
 let f': D₁:=⟨_,Nymph.low_flip Y H G j s _ (Nymph.flipped_left Y H G j s _ _ p1)⟩
 let g': D₁:=⟨_, forward_bar Y H G (-d) s.val (d:ℝ) 0 (by simp) g.val p2⟩
 refine ⟨f',g',fun q u=>?_⟩
 rw [← spend_space Y H V G a c j x q s h_,←spent_clock Y H V G a c s.val x (q+d) u g' h_,registered_pair,os_across,registered_pair,os_across]; apply congrArg (V₀ x); apply Subtype.ext
 change _= flipMark s.val K (flipMark s.val K _) * trek K s.val (q+d) (trek K s.val (-d) g.val); rw [mirror_twice, trek_add,add_assoc,add_neg_cancel,add_zero]; rfl
include TC TF
local notation "X₂"=> transversal j s.val s.property
local notation "Lt"=> LightBudget.opCarries Y H V G j (c j) (Vf x)
local notation "H₂" v:max => sight Y H V G a c j x s h_ v
lemma t_segment (u : 0<v+d) :
    inner ℂ (pu f) (Lt (H₂ v).toLinearIsometry.toContinuousLinearMap (pu g))=
     inner ℂ (pu f) ((St).U ((v:ℝ) • transversal j s.val s.property) (pu g)):=by
 obtain ⟨f',g',h⟩:= steady_hall Y H V G a c j x s h_ d f g p1 p2
 let L'(q:ℝ):= inner ℂ (X₁ f') ((S₁).E (Real.toNNReal (q+(d:ℝ))) (X₁ g')); let U(q:ℝ):= inner ℂ (pu f) ((St).U (q • X₂) (pu g))
 have hd(q:τ) (u:0≤ q+d) : inner ℂ (pu f) (Lt (H₂ q).toLinearIsometry.toContinuousLinearMap (pu g))= L' (q:ℝ) := by
    change inner ℂ ((pu f).val) ((Lt _ (pu g)).val)=_; rw [carries_full Y H V G j (c j) (Vf x) TC, voice_full Y H V G j (c j) (Vf x) TC, voice_full Y H V G j (c j) (Vf x) TC]; exact h q u
 have he(q: marks (dainty Λ)) : Lt (H₂ (accept Λ q)).toLinearIsometry.toContinuousLinearMap (pu g)=(St).U ((q:ℝ) • X₂) (pu g):=by
    let p:= even_speaks Y H V G a c j x s q; apply Subtype.ext; rw [carries_full Y H V G j (c j) (Vf x) TC, show (H₂ (accept Λ q)).toLinearIsometry.toContinuousLinearMap= _ from p.2 p.1]; exact (Nymph.enjoy Y H V G a c x j s TF (pu g) q).symm
 have hQ(q:ℝ) (hq: q ∈ Ioi (-(d:ℝ))): L' q=U q:=by
    refine Set.EqOn.closure (s:= Ioi (-(d:ℝ))∩ marks (dainty Λ)) ?_ (continuous_const.inner ((S₁).continuousE _|>.comp (continuous_real_toNNReal.comp (continuous_id.add continuous_const))))
      (continuous_const.inner ((St).continuousU _|>.comp (continuous_id.smul continuous_const))) ((daylight (dainty Λ)).open_subset_closure_inter isOpen_Ioi hq) -- implicit functions
    intro x k; let q: perch Λ:= ⟨x,k.2⟩; have hz:0 ≤ accept Λ q+d:= show 0≤ x+(d:ℝ) from (by linarith [show -(d:ℝ)<x from k.1])
    exact (hd (accept Λ q) hz).symm.trans (congrArg (inner ℂ (pu f)) (he q))
 exact (hd v u.le).trans (hQ v (show -(d:ℝ)<(v:ℝ) from by linarith [show 0<(v:ℝ)+(d:ℝ) from u]))
omit p1 p2
lemma true_space : (H₂ v)= transportT Y H V G a c j (eject s.val v) x x (space_v j s v) (alwaysAt Y H V G a c s.val x v h_) ∧
    opCarries Y H V G j (c j) (Vf x) (H₂ v).toLinearIsometry.toContinuousLinearMap = (St).U ((v:ℝ) • transversal j s.val s.property) := by
 obtain ⟨d,h⟩:= Schedule.very_late (a:=-(v:ℝ)) (daylight (loomD Λ))
 refine ⟨rfl,?_⟩; apply DFunLike.coe_injective; let L' := (opCarries Y H V G j (c j) (Vf x) (H₂ v).toLinearIsometry.toContinuousLinearMap); let W':=(St).U ((v:ℝ) • X₂)
 let K'(q:ℝ)(p:Bool):= far Y H V G j (c j) (Vf x) s.val q p
 have he (q:ℝ)(p:Bool): Dense (K' q p:Set (Ft).space):= far_dense Y H V G j (c j) (Vf x) s.val s.property TC TF q p
 funext y; refine (closure_minimal ?_ (isClosed_eq L'.continuous W'.continuous) (he d true y):L' y=W' y)
 intro f p; obtain ⟨f,rfl⟩:= LinearMap.mem_range.mp p; apply (he 0 false).eq_of_inner_right ℂ; intro g p; obtain ⟨g,rfl⟩:=LinearMap.mem_range.mp p
 let pF:=domain_loose Y H G _ f.property; let gF:=domain_loose Y H G _ g.property; let q:F:=⟨_,domain_mono Y H G inter_subset_left pF⟩; let v':F:=⟨_,domain_mono Y H G inter_subset_left gF⟩
 exact t_segment Y H V G a c j x v TC TF s h_ d v' q (domain_mono Y H G inter_subset_right gF) (domain_mono Y H G inter_subset_right pF) (show 0<(v:ℝ)+(d:ℝ) from by linarith)
lemma actual_real_space (f:Domain Y H G false (flank j 0)): (pu (bystander Y H G j v s f):Ft)=
   (St).U ((v:ℝ) • transversal j s.val s.property) (pu f) := by
 rw [← (true_space Y H V G a c j x v TC TF s h_).2]; apply Subtype.ext; rw [carries_full Y H V G j (c j) (Vf x) TC,voice_full Y H V G j (c j) (Vf x) TC,voice_full Y H V G j (c j) (Vf x) TC, spend_space Y H V G a c j x v s h_]; rfl
end frame
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
