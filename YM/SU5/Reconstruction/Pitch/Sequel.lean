import YM.SU5.Reconstruction.Pitch.Move
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
include k h
lemma passages (v:ℂ)(u:v∈inside) (f:H₀ y) : transportT Y H V G a c j p x y k h ((S₀ y).F v f)= (S₀ x).F v (T f):=by
 let P:= (fun v:ℂ=> (transportT Y H V G a c j p x y k h) ((S₀ y).F v f)); let Q:= (fun v:ℂ=> (S₀ x).F v (T f))
 have hp {J':Hilbert} (X:OS.Semigroup J' j) (f:J') : AnalyticOnNhd ℂ (fun v=> X.F v f) inside := fun a' h=> ((ContinuousLinearMap.apply ℂ (J').space f).analyticAt _).comp (X.localHeat a' h)
 refine ConePrice.Sail.pioneer («A»:=OS.Semigroup.inside) (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (w:=1) (show ((↑(1:ℝ)):ℂ)∈ inside from (by change 0< (Complex.ofReal (1:ℝ)).re; simp)) 0 2 (by norm_num) (show AnalyticOnNhd ℂ P inside from fun a' h=> ((T).toLinearIsometry.toContinuousLinearMap.analyticAt _).comp (hp _ _ a' h)) (show AnalyticOnNhd ℂ Q inside from hp (S₀ x) (T f)) ?_ u -- local h shadows
 intro u v; change T ((S₀ y).F (u:ℂ) f)= (S₀ x).F (u:ℂ) (T f)
 rw [show (u:ℂ)=duration (Real.toNNReal u) from (by unfold duration; rw [Real.coe_toNNReal u v.1.le]), (S₀ x).roots_heat (Real.toNNReal_pos.mpr v.1),(S₀ y).roots_heat (Real.toNNReal_pos.mpr v.1), arcs_move]
lemma edgeTempo (t:ℝ) (f:H₀ y) : T ((S₀ y).edge t f)=(S₀ x).edge t (T f):=by
 apply congrFun (a:=f) (((S₀ y).whole 1).equalizer ((T).continuous.comp ((S₀ y).edge t).continuous)
    (((S₀ x).edge t).continuous.comp (T).continuous) _)
 funext u; dsimp only [Function.comp_apply]; rw [arcs_move,OS.Semigroup.high,OS.Semigroup.high,passages Y H V G a c j p x y k h _ (length.mpr zero_lt_one)]
local notation "d" x:max=> displacement Y H V G.history G.clipped a false (c a) x j (c j)
local notation "U" x:max u:max v:max=> ((turnstile Y H V G.history G.clipped j false (c j) (d x)).crew u).play v
lemma spectators_taste (u:Trans j) (v:marks (timeMesh Λ)) (f:H₀ y): T ((U y u v) f)=(U x u v) (T f):=by rw [←older_stride Y H V G a c x,←older_stride Y H V G a c y]; exact matches_even ..
lemma stays_joint (f:H₀ y) : RealJoint Y H V G.history G.clipped j false (c j) (d x) (T f) ↔ RealJoint Y H V G.history G.clipped j false (c j) (d y) f:=by
 unfold RealJoint; simp only [←edgeTempo, ←spectators_taste]; exact ⟨fun u=>⟨fun t=>(T).injective (u.1 t), fun a b=>(T).injective (u.2 a b)⟩,fun u=>⟨fun t=>congrArg T (u.1 t), fun a b=>congrArg T (u.2 a b) ⟩⟩
local notation "Ω" x:max=> doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
lemma victory_transfer (v:Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))) : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) y j (c j)):=by
 suffices r:SingleGround (atCharacter Y H V G.history G.clipped j false (c j) (d y)) (traveller Y H V G.history G.clipped j false (c j)) from ⟨r,single_is_extreme _ _ (travellers Y H V G.history G.clipped j false (c j)) (setupState ..) r⟩
 intro z u; obtain ⟨s,q⟩:=one_real Y H V G.history G.clipped j false (c j) (d x) v ((stays_joint Y H V G a c j p x y k h z).2 ((true_joint Y H V G.history G.clipped j false (c j) (d y) z).1 u)); exact ⟨s,(T).injective (by change T (s • Ω y)=_ ; rw [map_smul, carry_vac]; exact q)⟩
open LightBudget
local notation "Wz" x:max=> mainsea Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
lemma voyage_match (u:List (Trans j)) (v:Trans j→marks (timeMesh Λ))(f: H₀ y): T ((Wz y).track.raw u v f)= (Wz x).track.raw u v (T f):=by
 induction u with
 | nil=> rfl
 | cons i u ih=> rw [Germ.Alliance.raw_step,Germ.Alliance.raw_step, ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]; change T ((U y i (v i)) _)= (U x i (v i)) ((Wz x).track.raw u v (T f)); rw [spectators_taste,ih]
lemma pricesMove (r e:ℝ)(v:0≤r)(c₁:LightBudget.TwoShot Y H V G j (c j) (d x) r e) : TwoShot Y H V G j (c j) (d y) r e:=by
 have hz:= (price_at_χ Y H V G j (c j) (d x) v e).2 c₁
 apply (price_at_χ Y H V G j (c j) (d y) v e).1; intro P q f
 have hp:=hz P q (T f); simp only [ConePrice.transverse_play, ←voyage_match Y H V G a c j p x y k h, ←arcs_move, ←map_sub, LinearIsometryEquiv.norm_map] at hp; -- `.list` likely X.list defeq but not simp.
 rw [map_sub] at hp; exact hp
omit k
-- required for all j (regardless input sign) via ±p
lemma nearby_boost (c₁:LightBudget.BoostBacking Y H V G c a x) : LightBudget.BoostBacking Y H V G c a y:=by
 apply (real_boost_purchase Y H V G c a y (le_refl (0:ℝ)) (zero_lt_one' ℝ)).1
 constructor; intro j; apply twoShotPays
 let ψ (χ:Warden Y H V G a c) := displacement Y H V G.history G.clipped a false (c a) χ j (c j)
 have h' := (true_spectrum Y H V G j (c j) (ψ x) (le_refl (0:ℝ)) (zero_lt_one' ℝ)).2 ⟨c₁.present j,c₁.forward j⟩
 by_cases u:0≤p j; · exact pricesMove Y H V G a c j p x y u h 0 1 (le_refl _) h'
 exact pricesMove Y H V G a c j (-p) x y (neg_nonneg.mpr (le_of_not_ge u)) ((inverse_lead Y H V G p a c x).trans h) 0 1 (le_refl _) h' -- check order
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
