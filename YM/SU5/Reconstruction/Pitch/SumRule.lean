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
-- group structural simplification. Single taste per time direction. Note Eu letter labels.
lemma e_plus (v w:τ): (eject j (v+w)) = eject j v+ eject j w:=by
 funext i; by_cases t:i=j <;> simp_all
-- no step extension by ℝ until membership proven
noncomputable def heatT (x y:A)(v: marks (loomD Λ)) (u:0≤v)(g:leader Y H V G a c (eject j v) x=y) := transportT Y H V G a c j (eject j v) x y (by rwa [eject_at]) g
local notation "JX"=> heatT Y H V G a c j
lemma goal_step {q:Atlas Λ}(v: marks (dainty Λ))(hv:q=p+eject j (accept Λ v))(u: 0≤q j)(w: leader Y H V G a c q x=y) : transportT Y H V G a c j q x y u w=T:= by
 suffices tick : ∀ (p q:Atlas Λ)(v:perch Λ) (hv:q=p+eject j (accept Λ v))(k:0≤p j) (u:0≤q j) (w:leader Y H V G a c q x=y) (f:leader Y H V G a c p x=y),0≤v → transportT Y H V G a c j q x y u w=transportT Y H V G a c j p x y k f by
    by_cases hz:0 ≤ v; · exact tick p q v hv k u w h hz
    have ht : p=q+ eject j (accept Λ (-v)):=by rw [hv,map_neg,show eject j (-(accept Λ v))=-(eject j (accept Λ v)) from LightBudget.eject_neg ..]; abel
    exact (tick q p (-v) ht u k h w (neg_nonneg.mpr (le_of_not_ge hz))).symm
 intro p q v hv k u w f hz; subst q
 let q := eject j (accept Λ v); let p':(0:τ)≤ q j:=by unfold q; rw [eject_at]; exact hz
 have h :=even_native Y H V G a c j y v hz; rw [←sum_rule Y H V G a c j p x y k f q p' y h.1, show transportT Y H V G a c j q y y p' h.1 =_ from (h.2 h.1)]; rfl
local notation "A₁" v:max x:max=> leader Y H V G a c (eject j v) x
lemma goal_odd (v w:τ)(g: ∃ p:perch Λ, w=v+accept Λ p)(u:0 ≤ v)(t:0≤w)(h:A₁ v x=y)(k':A₁ w x=y) : heatT Y H V G a c j x y v u h=heatT Y H V G a c j x y w t k':=by obtain ⟨z,rfl⟩:= g; refine Eq.symm (goal_step Y H V G a c j _ x y _ _ z (e_plus ..) _ _) -- implicit q arguments maybe `_`
lemma hatch (v w:τ)(p0:0≤v)(p1:0≤w) (h_: A₁ v x=y) (g:¬ ∃ u:perch Λ,v=accept Λ u) (r:¬ ∃ u:perch Λ,w=accept Λ u) : A₁ w x=y ∧ ∀ p: A₁ w x=y, JX x y w p1 p= JX x y v p0 h_ :=by
 have b0(t:τ)(v:¬ ∃ u:perch Λ,t=accept Λ u): ∃ u:perch Λ,t=eyeD Λ+accept Λ u:= by
    obtain ⟨u,e|e⟩:= couple t; · exact (v ⟨u,e⟩).elim
    exact ⟨u,e⟩
 obtain ⟨g,e⟩:= b0 _ g; obtain ⟨r,z⟩:= b0 _ r
 let y1:=r-g
 have he:w=v+accept Λ y1:=by rw [e,z]; unfold y1; rw [map_sub]; abel
 refine ⟨?_,fun b=> (goal_odd Y H V G a c j x y v w ⟨y1,he⟩ p0 p1 h_ b).symm⟩
 calc
   _ = leader Y H V G a c (eject j (accept Λ y1)) (A₁ v x) := by rw [he,e_plus]; exact (leading_plus ..).symm
   _ = _:= by rw [star_leading,no_even,h_]
lemma h_equiv (v: τ)(hv:0≤v)(hx:A₁ v x=x) (f:H₀ x): JX x x v hv hx (JX x x v hv hx f) = f := by
 obtain ⟨u,e⟩:= duo v
 let T' := eject j (accept Λ u); have ht :0 ≤ u:=by change 0≤ accept Λ u; rw [e]; exact add_nonneg hv hv
 let q:= eject j v; have p : 0 ≤ q j:= by unfold q; rwa [eject_at]
 let k:=transportT Y H V G a c j q x x p hx
 have h:=even_native Y H V G a c j x u ht
 change k (k f)=f
 have he:((transportT Y H V G a c j q x x p hx).trans (transportT Y H V G a c j q x x p hx))= _:= sum_rule Y H V G a c j q x x p hx q p x hx
 have hp:T'=q+q:= by unfold T' q; rw [e,e_plus]
 have hr : ∀ (p:0≤ (q+q) j) (v: W (q+q) x=x), transportT Y H V G a c j (q+q) x x p v= LinearIsometryEquiv.refl ℂ (H₀ x):=by rw [←hp]; intro p i; exact h.2 i
 exact (DFunLike.congr_fun (he.trans (hr _ _)) f)
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
