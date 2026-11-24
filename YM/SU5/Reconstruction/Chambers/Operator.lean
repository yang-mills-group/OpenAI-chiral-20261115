import YM.SU5.Reconstruction.Chambers.Strips
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
namespace Chambers
open Selected SlabMark MeshClock
variable (j : Axis)
set_option quotPrecheck false
local notation "D" => Domain Y H G
local notation "T" => flank j 0
local notation "R" => RSpace
local notation "δ₁" => (timeMesh Λ)
local notation "M" => (MeshClock.marks (timeMesh Λ))
local notation "κ" => ticket Y H G
local notation "Ξ" a:max => move (tent Y H) (eject j a)
local notation "J" t:max => insideAt Λ l K false (flank j 0) t
local notation "N" => Domain Y H G false (flank j 0)

section
variable (s w : ℕ)
local notation "u" => notch (timeMesh Λ) s (w:ℤ)

private lemma state_further (x : Entry Y H s j false w) {t}
    (h : s ≤ t) :
    let w' := Λ.R.L.val^(t-s)*w
    let f:= furnished Y H s G.history j false w x t h
    notch (timeMesh Λ) t (w':ℤ)=notch (timeMesh Λ) s (w:ℤ) ∧
      ticket Y H G t (base Y H j t w' f).val= ticket Y H G s (base Y H j s w x).val := by
  intro w' f
  constructor
  · have he: (w':ℤ)= castor δ₁ s t (w:ℤ) := by unfold w' castor; push_cast; rfl
    rw [he,notch_up _ _ _ h]
  rw [show (base Y H j t w' f).val= spreadTo Y H G s t (base Y H j s w x).val from rfl]
  exact ticket_spread Y H G h _

include V in
lemma combine_today (x : Entry Y H s j false w) (y : Tower.Field Y H s j 0 false) :
    let f := (base Y H j s w x).val
    let g := (fromField Y H j s y).val
    ticket Y H G s (fromField Y H j s (slabT Y H s j false w x y)).val=
      ticket Y H G s f * move K (eject j (notch (timeMesh Λ) s (w:ℤ))) (ticket Y H G s g) := by
  intro f g; let z : Cover := eject j (w:ℤ)
  rw [move_at Y H V G (eject j u) s g z (stamps_eject j s _)]
  -- Detached with permitted touching
  obtain ⟨S, (a:InTest K true S false f.val), b⟩ := x.property
  obtain ⟨P, (c:InTest K true P false g.val), d⟩ := (((purpose_ok ..).1 y.property).1 : ∃ _ , _)
  rw [area0] at d
  let Q:= plow K j (w:ℤ) P
  let k:=reposition K z g
  have h : Tower.region j (ruler Λ.block*w) (K).ℓ Q := by
    intro i t; obtain ⟨i,h,rfl⟩ := plow_stays K j _ _ t
    specialize d i h; rw [moves,if_pos rfl,show (K).B=Λ.block from rfl]; linarith
  have g' : k.val=relocate K j w g.val := chart_eject j (w:ℤ) g
  have c' : InTest K true Q false k.val := by rw [g']; exact flow_port _ _ _ c
  have he : (fromField Y H j s (slabT Y H s j false w x y)).val=f*k := by
    apply Subtype.ext; rw [fromField_val,slab_eq]; change _*_= f.val*k.val; rw [g']; rfl
  rw [he]; apply Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun t=>?_
  exact Subtype.ext (woven_product Y H G.history.circuit s (t-s) a c'
    (cover_between K Λ l rfl j (fun p h=> (b p h).2) h))
end
-- because `combine_today` needs V for move_at.
variable (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "I₀" => indoor Y H V G.history G.clipped j false C χ
local notation "os" => OSvector Y H V G j C χ

structure Follows (f : Sky (tent Y H)) (w : M) (B : (indoor Y H V G.history G.clipped j false C χ).Op) : Prop where
  pose : f ∈Domain Y H G false (strip j 0 (w:ℝ))
  graph (x : Domain Y H G false (flank j 0)) : ∃ y : Domain Y H G false (flank j 0),
    y.val=f * (Ξ w) x.val ∧ os y=B (os x)

local notation "Γ" => Follows Y H V G j C χ
local notation "λ₀" s:max x:max t:max => procession Y H V G.history G.clipped j false C χ (entrance Y H V s G.history G.clipped j false C x t)

lemma arrangement (s w : ℕ) (x : Entry Y H s j false w) (p : 0<w) :
    Follows Y H V G j C χ (ticket Y H G s (base Y H j s w x).val) (notch (timeMesh Λ) s w) (λ₀ s x p) := by
  constructor
  · have ht : (notch (timeMesh Λ) s (w:ℤ):ℝ) = (whenly (timeMesh Λ) s w:ℝ) := natural_time ..
    rw [ht]; exact ticket_mem Y H G (base_coverage Y H j s w x)
  intro f; obtain ⟨t,h,⟨a,rfl⟩⟩ := ((eventually_ge_atTop s).and (eventually_enclosed Y H G f)).exists
  let w' := Λ.R.L.val^(t-s)*w
  let y := asField Y H j false t a
  let f' := furnished Y H s G.history j false w x t h
  let g := slabT Y H t j false w' f' y
  obtain ⟨e,h'⟩ := state_further Y H G j s w x h
  refine ⟨enclose Y H G T false t (fromField Y H j t g),?_,?_⟩
  · rw [←e,←h']; exact combine_today Y H V G j t w' f' y
  rw [OSvector_enclose,OSvector_enclose]; exact (slot_high Y H V s G.history G.clipped j false C χ x p t h y).symm -- tune

variable (u : MeshClock.marks (timeMesh Λ)) (b : 0 < (u:ℝ))

include b in
lemma fits (x : Sky (tent Y H)) (p : x∈ Domain Y H G false (strip j 0 (u:ℝ))) :
    ∃ B : (indoor Y H V G.history G.clipped j false C χ).Op,
      Follows Y H V G j C χ x u B := by
  obtain ⟨s,⟨f,h,rfl⟩,w,t,e⟩ := (((domain_eventually Y H G).1 p).and (notch_nat_event u b)).exists
  have he : (u:ℝ)=(whenly (timeMesh Λ) s w:ℝ) := by rw [←e]; exact natural_time ..
  rw [he] at h
  let x:= startOp Y H j s w f h
  refine ⟨λ₀ s x t, ?_⟩
  rw [←e]; exact arrangement Y H V G j C χ s w x t

noncomputable def stripOp (x : Sky (tent Y H)) (p : x∈ Domain Y H G false (strip j 0 (u:ℝ))) :
    (indoor Y H V G.history G.clipped j false C χ).Op := (fits Y H V G j C χ u b x p).choose

lemma stripOp_follows (x : Sky (tent Y H)) (p : x∈D false (strip j 0 (u:ℝ))) : Γ x u (stripOp Y H V G j C χ u b x p) :=
 (fits Y H V G j C χ u b x p).choose_spec

lemma unique_op {x : Sky (tent Y H)} {U W : (I₀).Op} (p : Γ x u U) (q : Γ x u W) : U=W := by
  ext1 z; apply congrFun (a:=z) ((physical_dense Y H V G j C χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _) _)
  funext y
  let x:=Submodule.inclusion (domain_loose Y H G T) y
  obtain ⟨a,h,h'⟩ := p.graph x; obtain ⟨b,t,e⟩ := q.graph x; exact h'.symm.trans ((congrArg os (Subtype.ext (h.trans t.symm))).trans e)

end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
