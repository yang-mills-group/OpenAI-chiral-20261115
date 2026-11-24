import YM.SU5.Reconstruction.Pitch.Atlas
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
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

-- Flat teaching versions at condition-free weight. Frame representation always Hess(E) real on indoor, NO purchase of other-axis Info for this part.
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
noncomputable def pitches (Λ:Preparation)(j:Axis) (p:Atlas Λ):ℝ≥0:= Real.toNNReal (p j:ℝ)
local notation "px" p:max=> pitches Λ j p
local notation "κ" p:max=> constellation p K
lemma cover_bar (r d:ℝ)(u:d≤r+(p j:ℝ))(f:Sky (tent Y H)) (g:f∈D q (flank j r)):constellation p K f∈D q (flank j d):=by
 apply domain_mono Y H G _ (coverPoint_inside Y H G p f g); rintro _ ⟨v,e,rfl⟩; apply u.trans; exact add_le_add_left (show r≤v j from e) ((p j):ℝ)
noncomputable def promenadeFront (f: Domain Y H G false (flank j 0)) (k:0≤p j) : Domain Y H G false (flank j 0):= ⟨constellation p (tent Y H) f.val,cover_bar Y H G j p 0 0 (by rw [zero_add]; exact k) _ f.property⟩
local notation "Pf" p:max k:max x:max=> promenadeFront Y H G j p x k
open ConePrice SelectionAnalysis
lemma cover_pair_invoice {v:τ}(l:eject j (p j+p j)=eject j v)(f g:Sky J): flipMark j J (constellation p J f)* constellation p J g = constellation (opposite p j) J (flipMark j J f* trek J j v g):=by
 rw [cover_times,flip_star,← cover_solo,cover_plus, show opposite p j+eject j v=p from by unfold opposite; rw [←l]; abel]
-- buying e#+2^+ ignoring P labels. True for any orientation. CLEAN LHS $t≥0.$
lemma twistsBy (f g: Domain Y H G false (flank j 0)) (u:0≤p j) (v: leader Y H V G a c p x = y) :
    inner ℂ ((X₀ x) (Pf p u f)) ((X₀ x) (Pf p u g))= inner ℂ ((X₀ y) f) ((S₀ y).E (pitches Λ j p+pitches Λ j p) ((X₀ y) g)):=by
 -- pick even representative of projection $2 p_t$
 obtain ⟨r,hr⟩:= duo (p j); have ht: 0≤ (r:ℝ) := by
    change 0≤ (accept _ r).val; rw [hr]; exact add_nonneg u u
 let W₁ : F:=⟨stride K j r g.val,Nymph.pitch_bar Y H G j ht g⟩
 have hp: trek K j (p j+p j) g.val= W₁.val:=by rw [←hr,advance_even]
 have he: (κ (opposite p j)) (flipMark j K f.val*W₁.val) = flipMark j K (Pf p u f).val* (Pf p u g).val:=by rw [←hp]; exact (cover_pair_invoice j p rfl f.val g.val).symm
 rw [registered_pair,os_across Y H V G a (c a) x,show (px p)+(px p)= Real.toNNReal (r:ℝ) from ?_,time_even Y H V G a c y j r ht g,registered_pair,os_across Y H V G a (c a) y]
 · let Y₁ : Domain Y H G false Set.univ := ⟨_,paired_forever Y H G j _ _ f.property W₁.property⟩
   have h : (V₀ x) (horner Y H G (opposite p j) Y₁)=(V₀ y) Y₁:= by rw [reflects_price, leading_turn,v]
   exact Eq.trans (congrArg (V₀ x) (Subtype.ext he.symm)) h
 apply NNReal.coe_injective; rw [NNReal.coe_add,pitches, Real.coe_toNNReal _ u, Real.coe_toNNReal _ ht]; exact (congrArg Subtype.val hr).symm
local notation "Lt" x:max f:max=> (S₀ x).E (pitches Λ j p) ((X₀ x) f)
local notation "Rt" x:max f:max=> (X₀ x) (promenadeFront Y H G j p f k)
lemma escapes (x:A) : DenseRange (fun f=> (S₀ x).E (pitches Λ j p) ((X₀ x) f)) := ((S₀ x).whole _).comp (attains_full_axis Y H V G a j c x) (ContinuousLinearMap.continuous _)
include k
lemma bends_dense : DenseRange (fun f=> (X₀ x) (promenadeFront Y H G j p f k)) := by
 apply (TimeMesh.dense_flanks Y H V G j (c j) _ (p j:ℝ)).mono; rintro _ ⟨v,g,k₁,rfl⟩
 have ht:=domain_loose Y H G _ g; let i:= constellation (-p) K v; let f:F:=⟨i,cover_bar Y H G j (-p) _ 0 (show 0≤ (p j:ℝ)+(((-p) j):ℝ) from le_of_eq (by simp)) v ht⟩
 refine ⟨f,?_⟩; change (X₀ x) (Pf p k f)= (X₀ x) ⟨v,domain_loose Y H G _ k₁⟩; apply congrArg (X₀ x); apply Subtype.ext; change (κ p) ((κ (-p)) v)= _; rw [cover_plus,add_neg_cancel,constell_zero]
include h
lemma taste_exact : ∃ T: indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) y j (c j))≃ₗᵢ[ℂ] indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)),∀ (f: Domain Y H G false (flank j 0)), T ( (S₀ y).E (px p) ((X₀ y) f))=(X₀ x) (promenadeFront Y H G j p f k):=by
 refine Selected.gram_impl («A»:=H₀ y) (B:=H₀ x) (escapes Y H V G a c j p y) (bends_dense Y H V G a c j p x k) ?_
 intro f g; rw [twistsBy Y H V G a c j p x y f g k h]; nth_rw 1 [← (S₀ y).sym]; rw [ContinuousLinearMap.adjoint_inner_left,(S₀ y).time]; rfl

noncomputable def transportT (k:0≤p j) (h: leader Y H V G a c p x=y) : (H₀ y)≃ₗᵢ[ℂ] (H₀ x) := Classical.choose (taste_exact Y H V G a c j p x y k h)
lemma native_taste (f:F) : transportT Y H V G a c j p x y k h ((S₀ y).E (pitches Λ j p) ((X₀ y) f))=(X₀ x) (promenadeFront Y H G j p f k):= Classical.choose_spec (taste_exact Y H V G a c j p x y k h) f
#check @Pitch.transportT
#check @Pitch.native_taste
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
