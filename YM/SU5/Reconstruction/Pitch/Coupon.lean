import YM.SU5.Reconstruction.Pitch.Ink
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
open SelectionAnalysis
variable (r:ℝ)(u:0≤r)
local notation "FF"=> Domain Y H G true (flank j r)
local notation "Vf" x:max=> displacement Y H V G.history G.clipped a false (c a) x j (c j)
local notation "ρ" x:max=> procession Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S"=>driveAlgebra Y H V G.history G.clipped j false (c j)
local notation "B"=>traveller Y H V G.history G.clipped j false (c j)
local notation "b"=> (SelectionAnalysis.concord (traveller Y H V G.history G.clipped j false (c j)))
local notation "Hp"=> ((H₀ x).space × (H₀ y).space)
local notation "Wf" x:max=> joint (B) (ρ x)
local notation "Jp" x:max=>(Wf x).starProjection
local notation "Ω" x:max=>doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
variable (v: weft Λ)(v₀:0≤v)
variable (Vx : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)))
local notation "P'"=> dressing Y H V G a c j x y r u
local notation "Ds"=> acquit Y H V G a c j x y r u
local notation "uY" f:max=> nearer Y H G j r u f
local notation "θ'"=> flipMark j K
local notation "JX"=> heatT Y H V G a c j
local notation "A₁" v:max x:max=> leader Y H V G a c (eject j v) x
local notation "SX"=> ride Y H V G.history G.clipped j false (c j) (Vf x)
local notation "Hx"=> H₀ x
local notation "ℜ" v:max => Real.toNNReal (v:ℝ)
-- no assertion we have paid. Full meter restoration for this clock and its actual character.
def Absent : Prop:= ∀ v:weft Λ,∀ v₀:0≤v,leader Y H V G a c (eject j v) x=x ∧ ∀ u1:leader Y H V G a c (eject j v) x=x,
   heatT Y H V G a c j x x v v₀ u1= LinearIsometryEquiv.refl ℂ (H₀ x)
private lemma beamHeat {T₁:Hilbert}(M0:OS.Semigroup T₁ j)(z:T₁)(q:ℝ≥0): (inner ℂ z (M0.E q z)).re = ‖M0.E (q/2) z‖^2:=by
 let p:= q/2; have ht: p+p=q:=by unfold p; simp
 have he:= M0.time p p; rw [ht] at he; rw [he, ContinuousLinearMap.comp_apply]; nth_rw 1 [← M0.sym p]; rw [ContinuousLinearMap.adjoint_inner_right]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
private lemma beamMore {T₁:Hilbert}(M0:OS.Semigroup T₁ j)(z:T₁)(e:z≠0)(q:ℝ≥0): 0 < (inner ℂ z (M0.E q z)).re:=by
 rw [beamHeat]; refine pow_pos (norm_pos_iff.mpr fun v=> e ?_) _; refine (M0.whole (q/2)).eq_of_inner_right ℂ ?_
 intro x; rw [inner_zero_right]; nth_rw 1 [← M0.sym]; rw [ContinuousLinearMap.adjoint_inner_left,v,inner_zero_right] -- right lemma orientation

include u v₀ Vx
lemma zero_hush (vE:¬ ∃ t:perch Λ, v= accept Λ t) (p:Ink Y H V G a c j x r 0 v) : Absent Y H V G a c j x:=by
 have θ:=recouples Y H V G a c j x r u v v₀ Vx 0 p; let Y₁:= heatT Y H V G a c j x x v v₀ θ
 have hz: Y₁=LinearIsometryEquiv.refl ℂ (H₀ x):=by
    ext1 f; change Y₁ f=f
    by_contra! hf
    let w:= f-Y₁ f; have he:w≠0 := sub_ne_zero.mpr (Ne.symm hf)
    have hY:Y₁ w= -w:= Eq.trans (map_sub Y₁ f (Y₁ f)) (by rw [show Y₁ (Y₁ f)=f from h_equiv ..]; unfold w; abel)
    have h: Y₁ ((S₀ x).E (ℜ v) w)= - (S₀ x).E (ℜ v) w:= Eq.trans (arcs_move Y H V G a c j (eject j v) x x (by rwa [eject_at]) θ (ℜ v) w) (by change (S₀ x).E (ℜ v) (Y₁ w)=_; rw [hY,map_neg])
    have ht:(0:ℝ) ≤ (inner ℂ w (Y₁ ((S₀ x).E (ℜ v) w))).re := by
       have he:= (ink_operator Y H V G a c j x r u v v₀ 0 θ).1 p w; rw [zero_mul,add_zero] at he; exact he
    rw [h,inner_neg_right,Complex.neg_re] at ht
    exact not_lt_of_ge ht (neg_lt_zero.mpr (beamMore _ _ w he _))
 intro t q; by_cases h:∃ t':perch Λ,t=accept Λ t'
 · obtain ⟨t,rfl⟩:= h; exact even_native Y H V G a c j x t q
 have p:= hatch Y H V G a c j x x v t v₀ q θ vE h
 exact ⟨p.1,fun w=> (p.2 w).trans hz⟩
omit Vx
lemma always (δ:ℝ)(p:0≤δ) (h: Absent Y H V G a c j x): Ink Y H V G a c j x r δ v:=by
 apply (ink_operator Y H V G a c j x r u v v₀ δ (h v v₀).1).2; intro w; rw [(h v v₀).2,LinearIsometryEquiv.coe_refl,id_eq,beamHeat]; positivity
include Vx
lemma ink_exact (h:¬ ∃ t:perch Λ,v=accept Λ t) : Ink Y H V G a c j x r 0 v ↔ Absent Y H V G a c j x:= ⟨zero_hush Y H V G a c j x r u v v₀ Vx h, always Y H V G a c j x r u v v₀ 0 (le_refl _)⟩
omit v₀ u Vx
-- might cost very small RELATIVE ε, no rate in t. ask on one p per neighborhood.
def AlmostClear (δ:ℝ):Prop:= ∀ ε:ℝ,0<ε→ ∃ p:weft Λ, 0 ≤ p ∧ (p:ℝ)<ε ∧ (¬ ∃ t:perch Λ,p=accept Λ t)∧ Ink Y H V G a c j x r δ p
lemma oftenOdd (Λ:Preparation)(i:ℝ)(g:0 < i):∃ p:marks (loomD Λ),0<(p:ℝ) ∧ (p:ℝ)< i ∧ ¬ ∃ t:perch Λ,p=accept Λ t:=by
 obtain ⟨s,hs,h⟩:= Schedule.walls (daylight (dainty Λ)) (show (-1:ℝ)< i-1 by linarith)
 let y:= (accept Λ s); let v:=eyeD Λ; have v':(v:ℝ)=1:=eye_steps _
 refine ⟨v+y,?_ ,?_,?_⟩
 · change 0<(v:ℝ)+(s:ℝ); linarith
 · change (v:ℝ)+(s:ℝ)< i; linarith
 rintro ⟨t,pt⟩; apply eyeD_odd Λ; refine ⟨t-s,?_⟩; rw [map_sub,← pt]; exact add_sub_cancel_right ..
include u Vx
lemma soft_rate (δ:ℝ)(d0:0≤δ)(d1:δ<1) : Absent Y H V G a c j x ↔ AlmostClear Y H V G a c j x r δ:=by
 constructor
 · intro h i v; obtain ⟨s,q,p,g⟩:= oftenOdd Λ i v; exact ⟨s,q.le,p,g,always Y H V G a c j x r u s q.le δ d0 h⟩
 intro hv
 -- normalized failure at negative taste. ONE orientation positive gap
 obtain ⟨v,k,p0,t,e⟩:= hv 1 zero_lt_one
 have θ:=recouples Y H V G a c j x r u v k Vx δ e
 let T₀:=heatT Y H V G a c j x x v k θ
 have he: T₀= LinearIsometryEquiv.refl ℂ (H₀ x):=by
    ext1 f; change T₀ f=f; by_contra! p
    let w:= T₀ f-f; have hw: w≠0:= sub_ne_zero.mpr p; have hp:T₀ w= -w:= (map_sub T₀ (T₀ f) f).trans (by rw [show T₀ (T₀ f)=f from h_equiv Y H V G a c j x v k θ f]; unfold w; abel)
    let G' : ℝ → ℝ:=fun t' => Complex.re (inner ℂ w ( T₀ ((S₀ x).E t'.toNNReal w)))
    have ht: Continuous G':= Complex.continuous_re.comp (continuous_const.inner ((T₀).continuous.comp (((S₀ x).continuousE w).comp continuous_real_toNNReal)))
    have hn: G' 0= -(‖w‖^2):=by unfold G'; rw [Real.toNNReal_zero,OS.Semigroup.eZero,ContinuousLinearMap.id_apply,hp,inner_neg_right,Complex.neg_re]; exact congrArg Neg.neg (inner_self_eq_norm_sq (𝕜:=ℂ) w)
    have hm:∀ᶠ t in 𝓝 0, G' t+δ*‖w‖^2 < 0:= (ht.add continuous_const).continuousAt.eventually_lt continuousAt_const (by change G' 0+δ*‖w‖^2<0; rw [hn]; nlinarith only [mul_lt_mul_of_pos_right d1 (pow_pos (norm_pos_iff.mpr hw) 2)])
    obtain ⟨η,v₁,h⟩:= Metric.mem_nhds_iff.mp hm
    obtain ⟨z,z0,i,z',Q⟩:= hv η v₁
    have hz:(z:ℝ)∈ Metric.ball (0:ℝ) η:=by rw [Metric.mem_ball,dist_zero_right,Real.norm_of_nonneg z0]; exact i
    have he:= hatch Y H V G a c j x x v z k z0 θ t z'
    have ht:= (ink_operator Y H V G a c j x r u z z0 δ he.1).1 Q w; rw [he.2 he.1] at ht
    exact not_lt_of_ge ht (h hz)
 apply zero_hush Y H V G a c j x r u v k Vx t
 apply (ink_operator Y H V G a c j x r u v k 0 θ).2
 intro x; rw [show heatT Y H V G a c j _ _ v k θ= LinearIsometryEquiv.refl ℂ (H₀ _) from he, LinearIsometryEquiv.coe_refl,id_eq,zero_mul,add_zero,beamHeat]; positivity
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
