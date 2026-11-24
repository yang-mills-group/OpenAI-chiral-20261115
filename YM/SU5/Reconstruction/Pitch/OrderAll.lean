import YM.SU5.Reconstruction.Pitch.Wrap
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
open LightBudget
local notation "Ω" x:max=>doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "Vf" x:max=> displacement Y H V G.history G.clipped a false (c a) x j (c j)
local notation "TC" x:max=> saunters Y H V G.history G.clipped j false (c j) (Vf x)
local notation "St" x:max=> peninsula Y H V G.history G.clipped j false (c j) (Vf x)
local notation "pu" x:max=> coreOs Y H V G j (c j) (Vf x)
local notation "Ut" x:max u:max v:max=> ((turnstile Y H V G.history G.clipped j false (c j) (Vf x)).crew u).play v
local notation "Tx" p:max k:max=> transportT Y H V G a c j p x (leader Y H V G a c p x) k rfl
local notation "yx" p:max=> leader Y H V G a c p x
local notation "px" p:max=> pitches Λ j p
lemma findCover (r:ℝ)(v: weft Λ)(h:0<2*r+(v:ℝ))(f:Domain Y H G true (flank j r)) :
    ∃ a z : Set RSpace, IsCompact a ∧ IsCompact z ∧ flipMark j K f.val∈ Domain Y H G true a ∧ trek K j v f.val ∈ Domain Y H G true z∧
    Disjoint a z ∧ (∀ x∈a, x j≤ -r) ∧ ∀ y∈z,r+(v:ℝ) ≤ y j:=by
 obtain ⟨T,hT,u,vx⟩:= (compact_domain Y H G).1 (mirror_support Y H G j f.val f.property); obtain ⟨V,hV,h',v'⟩:= (compact_domain Y H G).1 (forward_bar Y H G v j _ _ (le_refl (r+(v:ℝ))) f.val f.property); have hv:∀ x∈T,x j≤ -r:=by
    intro z p; obtain ⟨v,hv,rfl⟩:= u p; rw [mirrorE,if_pos rfl]; linarith [show r≤v j from hv]
 refine ⟨T,V,hT,hV,vx,v',Set.disjoint_left.mpr ?_,hv,h'⟩; intro x p q; linarith [hv x p,show r+(v:ℝ)≤x j from h' q ]

-- Keep link calibration in PITCH firstly at χ. If exhibition requires restoration on
-- FULL grid, can now ask ONE signed-price estimate at any point excluding the even-grid,
-- or much weaker soft version too (ONLY chosen reference). Roots not re-priced relative to
-- the unselected seats (pose visibility matters).
structure Guarantee : Prop where
 leader_k (p:Atlas Λ): (osValue Y H V G a (c a) x).comp (horner Y H G p) = osValue Y H V G a (c a) (leader Y H V G a c p x)
 finite_obstruction (p:Atlas Λ) : ∃ t:Axis→Bool, leader Y H V G a c p x=leader Y H V G a c (bits Λ t) x
 -- prices at every position in populated sectors. no spectral input
 sense (p:Atlas Λ) (h:0≤p j):
    -- real commuting structure already; more in Move.lean, Sequel.
    Victory Y H V G.history G.clipped false j (c j) (Vf (yx p)) ∧
    (∀ f:Domain Y H G false (flank j 0), (Tx p h) ((S₀ (yx p)).E (pitches Λ j p) ((X₀ (yx p)) f))= (X₀ x) (promenadeFront Y H G j p f h))∧
    (Tx p h) (Ω (yx p))=Ω x ∧
    ∀ f:(H₀ (yx p)), (∀ u:Trans j,∀ t:marks (timeMesh Λ), (Tx p h) ((Ut (yx p) u t) f)=(Ut x u t) ((Tx p h) f))∧ (∀ t:ℝ, (Tx p h) ((S₀ (yx p)).edge t f)=(S₀ x).edge t ((Tx p h) f))
 behind_even(p:Atlas Λ)(k:BoostBacking Y H V G c a x): BoostBacking Y H V G c a (yx p)
 needs (r:ℝ)(h:0≤r):
    (∀ (v:weft Λ),0<(v:ℝ) →(¬ ∃ t:Nymph.perch Λ,v=accept Λ t) →
      (Ink Y H V G a c j x r 0 v ↔ Absent Y H V G a c j x))∧
    (Absent Y H V G a c j x ↔ AlmostClear Y H V G a c j x r (1/2))
 enabled (HA:∀ j:Axis, Absent Y H V G a c j x) :
    (∀ p:Atlas Λ,leader Y H V G a c p x=x)∧
    ∀ (p:Atlas Λ)(h':0≤ p j)(f:Domain Y H G false (flank j 0))(t: (TC x)= ⊤)(b:ConePrice.Forward (St x)),
      (coreOs Y H V G j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j)) (promenadeFront Y H G j p f h')) =
        Schedule.route (St x) (coverPoint p) ((pu x) f)

lemma native_inked (h:Victory Y H V G.history G.clipped false j (c j) (Vf x)): Guarantee Y H V G a c j x:=by
 refine ⟨fun p=> (leadership Y H V G a c x p).symm,fun p=> basin_size Y H V G a c x p, fun p u=>⟨victory_transfer Y H V G a c j p x (yx p) u rfl h, fun f=> native_taste .., carry_vac ..,fun f=>⟨fun _ _=>spectators_taste ..,fun _=>edgeTempo .. ⟩⟩,
       fun p u=> nearby_boost Y H V G a c p x (yx p) rfl u,
       fun r h'=> ⟨fun v b t=>ink_exact Y H V G a c j x r h' v b.le h t, soft_rate Y H V G a c j x r h' h (1/2) (by norm_num) (by norm_num)⟩,
       fun p=>⟨fun t=> global_here Y H V G a c t x p,fun t u f b h=> roll_every Y H V G a c j t x u b h p f⟩⟩
 -- `..` HA & TC args? implicit unresolved. give
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
