import YM.SU5.Reconstruction.Nymph.Ladder
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
namespace Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false
open SelectionAnalysis OS.Semigroup
variable (iA:Axis) (R : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped iA false (R iA) →⋆ₐ[ℂ] ℂ)
local notation "P" => D false Set.univ
local notation "ν" => marks (dainty Λ)
local notation "c" j:max => displacement Y H V G.history G.clipped iA false (R iA) χ j (R j)
variable (j:Axis)
local notation "A" => indoor Y H V G.history G.clipped j false (R j) (c j)
local notation "Q" => ride Y H V G.history G.clipped j false (R j) (c j)
local notation "Ξ" => atEstate Y H V G.history G.clipped j false (R j) (c j)
local notation "X" => OSvector Y H V G j (R j) (c j)
local notation "T" => flank j 0
local notation "N" => Domain Y H G false (flank j 0)
local notation "V₀" => turnstile Y H V G.history G.clipped j false (R j) (c j)
local notation "B" i:max p:max => stride (tent Y H) i p
local notation "μ" j1:max => osValue Y H V G j1 (R j1) (c j1)
set_option quotPrecheck false
open Schedule Fixture Compose
variable (p : Axis→marks (dainty Λ)) (s : List Axis) (x:Sky (tent Y H))
local notation "δ" => (Axis → marks (dainty Λ))
noncomputable def swoop := s.foldr (fun i x=> (stride K i (p i)) x) x
lemma swoop_step (i:Axis): swoop Y H p (i::s) x=(stride _ i (p i)) (swoop Y H p s x) := rfl
lemma swoop_perm {t : List Axis}(b:s.Perm t) : swoop Y H p s x=swoop Y H p t x :=by induction b with
| nil=>rfl
| cons i _ ih=> rw [swoop_step,ih,swoop_step]
| swap i j t=>exact stride_cross ..
| trans p q u v=> exact u.trans v
noncomputable def all_steps (p : Axis→marks (dainty Λ)) (x:Sky (tent Y H)):= swoop Y H p ordinate x
noncomputable def polarHalf := swoop Y H p (spare j (look j)) x
lemma swoop_all (p:δ)(x:Sky K): all_steps Y H p x=(stride _ j (p j)) (polarHalf Y H j p x):=swoop_perm Y H p _ x (normal j)
lemma sparely (p:δ)(x:Sky K)(v:δ)(h:∀ i:Axis,i≠j→p i=v i): polarHalf Y H j p x=polarHalf Y H j v x :=by
  unfold polarHalf; generalize look j=l
  induction l with
  | nil=> change x=x; rfl
  | cons i t ih=> change stride K i.val (p i.val) (swoop Y H p (spare j t) x)=stride K i.val (v i.val) (swoop Y H v (spare j t) x); rw [ih,h i.val i.property]

lemma polar_range (p:δ)(x:Sky K)(a b:ℝ)(h:x∈ Domain Y H G q (strip j a b)): polarHalf Y H j p x ∈ D q (strip j a b):=by
  unfold polarHalf; generalize look j=l
  induction l with
  | nil=>exact h
  | cons i t ih=>
    apply domain_mono Y H G _ (stride_region Y H G i.val _ _ ih); rintro _ ⟨v,hv,rfl⟩; change (v j+ eject i.val (↑(p i.val):ℝ) j)≥a ∧ (v j+ eject i.val (↑(p i.val):ℝ) j)≤b
    rw [eject_away i.val _ _ i.property.symm,add_zero]; exact hv

section accounting
private def covered (J: Type*) [AddGroup J] (p:Axis→J) (s:List Axis): Axis→ J := (s.map fun i=> eject i (p i)).sum

private lemma old_tape (p : placement Λ)(s: List Axis)(x:Sky K): swoop Y H (fun i=>finerNow Λ (p i)) s x= move (tent Y H) (covered _ p s) x :=by
  induction s with
  | nil=> exact (move_by_zero ..).symm
  | cons i s ih=> rw [swoop_step,earlier_here,ih,move_sum]; rfl

private lemma cash {J:Type*}[AddGroup J] (p:Axis→J)(s:List Axis)(h:s.Nodup)(i:Axis): covered J p s i= if i∈ s then p i else 0:=by
 induction s with
 | nil=> simp [covered]
 | cons j t ih=>
   rw [show covered J p (j::t)= _+covered J p t from (show covered J p (j::t)= eject j (p j)+ _ from rfl),Pi.add_apply,ih (List.nodup_cons.mp h).2] -- remove
   by_cases g:i=j; · subst i; simp [(List.nodup_cons.mp h).1]
   simp [g]
lemma old_steps (p:placement Λ)(x:Sky K): all_steps Y H (fun i=>finerNow Λ (p i)) x=move (tent Y H) p x:=by
  unfold all_steps; rw [old_tape Y H]; rw [show covered _ p ordinate=p from funext (fun i=> (cash _ _ ordinate_one i).trans (if_pos (ordinates i)))] -- omit G actually

end accounting
lemma stride_one (p:ν)(J:Calibration)(j:Axis): stride J j p (1:Sky J)=1:=by
 refine Filter.Germ.coe_eq.mpr ?_; apply Eventually.of_forall; intro i; change cruise j J (2*beatAt p i) (1:Dome J)= 1; apply map_one

lemma from_dainty : DenseRange (finerNow Λ):=by
 intro x; rw [Metric.mem_closure_iff]; intro ε p
 obtain ⟨y,t,w⟩:= Schedule.walls (daylight (timeMesh Λ)) (show (x:ℝ)<(x:ℝ)+ε by linarith); refine ⟨finerNow Λ y,⟨y,rfl⟩,?_⟩
 change dist (x:ℝ) (y:ℝ)<ε; rw [Real.dist_eq, abs_of_neg (sub_neg.mpr t)]; linarith
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
