import YM.SU5.Reconstruction.Brazier.Beacon
import YM.SU5.Reconstruction.Seams.Court
/-! Time stamping & spaces even on the unselected Root; use for doing phase costs there. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "X" => Cloud (Dome (tent Y H))
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
open Chambers
abbrev Pub (t:MeshClock.marks (timeMesh Λ)) : Sky (tent Y H) →ₗ[ℂ] Sky (tent Y H):= move (tent Y H) (eject j t)
def lantern (Λ:Preparation) (s n:ℕ): MeshClock.marks (timeMesh Λ):= notch (timeMesh Λ) s n
local notation "δ"=> timeMesh Λ
lemma lantern_clock (s n:ℕ) : (lantern Λ s n:ℝ)=whenly δ s n:= natural_time ..
lemma lantern_add (s w n:ℕ) : lantern Λ s (w+n) = lantern Λ s w + lantern Λ s n:= by
 apply Subtype.ext; simp_rw [AddSubgroup.coe_add, lantern_clock,whenly]; push_cast; ring
lemma lanterns (s:ℕ)(r:ℝ) : ∀ᶠ n:ℕ in atTop, r < (lantern Λ s n:ℝ):= by
 simp_rw [lantern_clock,whenly,NNReal.coe_mul,NNReal.coe_natCast]
 exact ((tendsto_natCast_atTop_atTop).atTop_mul_const (show 0 < (mill δ s:ℝ) from mill_pos δ s)).eventually_gt_atTop r -- issue mul order
include V in
lemma PubL (s w:ℕ)(b: Dome (tent Y H)): Pub Y H j (lantern Λ s w) (ticket Y H G s b)= ticket Y H G s (Tarmac.center Y H j w b):=
 move_at Y H V G _ s b (eject j (w:ℤ)) (stamps_eject ..) -- need include V
-- Elise
include V in
lemma pub_area {t:Gt}{q:Bool}(b:Sky (tent Y H)){v:ℝ} (p:b ∈ Domain Y H G q (flank j v)):
    Pub Y H j t b ∈ Domain Y H G q (flank j (v + (t:ℝ))) :=
 domain_mono Y H G (even_flank j (eject j t) (by rw [eject_at])) (moving Y H V G _ _ p)
local notation "P"=> Pub Y H j
lemma pub_sum (r t:Gt)(x:Sky (tent Y H)): P r (P t x)=P (r+t) x:= by rw [Pub,Pub,move_sum]; rw [LightBudget.selectRay]
lemma pub_negflip (r:Gt)(x:Sky (tent Y H)): flipMark j (tent Y H) (Pub Y H j r x)= Pub Y H j (-r) (flipMark j (tent Y H) x):=by unfold Pub; rw [flipped_moves,LightBudget.reverse_eject]
local notation "H₀"=> advance Y H V G.history.circuit j 0 false C
lemma still (t:ℝ≥0)(v:Aurora Y H V G.history j false C): H₀ t v.val=v.val:=
 ((formal Y H V 0 G.history j false C v.val).1 ((Submodule.mem_iInf _).1 v.property 0)).1 t
lemma warmth {x:Sky (tent Y H)}{d:Gt}(q:x∈ Domain Y H G false (flank j 0))(h: P d x∈ Domain Y H G false (flank j 0))(u:0≤d):
 Px ⟨P d x,h⟩= H₀ (Real.toNNReal (d:ℝ)) (Px ⟨x,q⟩):=by -- notation Px tune
 unfold Pub at *
 rw [←LightBudget.initial_moves Y H V G j C x q (eject j d) (by simp; exact u)]
 unfold LightBudget.ruler; rw [ContinuousLinearMap.comp_apply,coordinates_eject,eject_at,show (fun i : Trans j=> eject j d i.val)=0 from funext fun i=> by rw [eject_away _ _ _ i.property]; rfl, Germ.Alliance.raw_zero]; rfl
lemma vista_on (x:FiniteGaugeDataPoly (tent Y H))(q:realize Y H Z x ∈ Domain Y H G false univ):
    courseValue Y H V G ⟨realize Y H Z x,q⟩ = vistaTake Y H Z x.val:=by
  obtain ⟨s,h⟩:= curve.mp x.property
  rw [show (⟨realize Y H Z x,q⟩ : D false univ)=⟨ticket Y H G s ((Kx s) x.val), ticket_loose ..⟩ from Subtype.ext (realize_ticket Y H V G Z s x h),course_ticket_val]; exact (Exhibition.vistaCall Y H s _ Z h).symm
include C in
lemma root_shift (p : placement Λ) {f : Sky (tent Y H)} (h : f∈ D false univ) (q : move K p f∈ D false univ) :
 courseValue Y H V G ⟨move K p f,q⟩ = courseValue Y H V G ⟨f,h⟩ := by
 obtain ⟨s,⟨a,ha⟩,b,u,rfl⟩:= ((stamps_eventually p).and ((domain_eventually Y H G).1 h)).exists
 rw [show (⟨move K p _,q⟩ : D false univ)=⟨ticket Y H G s (reposition K a b),ticket_loose ..⟩ from Subtype.ext (move_at Y H V G p s b a ha),course_ticket_val,course_ticket_val]; exact Vacancy.roots Y H V G.history j false C _ a ((marque ..).1 b.property)
local notation "R"=> Domain Y H G false (flank j 0)
lemma rootGraph (s w : ℕ) (x : Entry Y H s j false w) (p : 0<w) (f : Domain Y H G false (flank j 0)) :
    ∃ y : Domain Y H G false (flank j 0), y.val=ticket Y H G s (base Y H j s w x).val*Pub Y H j (lantern Λ s w) f.val ∧
      Px y=(entrance Y H V s G.history G.clipped j false C x p).val (Px f) := by
  obtain ⟨t,h,⟨a,rfl⟩⟩ := ((eventually_ge_atTop s).and (eventually_enclosed Y H G f)).exists
  let w' := Λ.R.L.val^(t-s)*w
  let y := asField Y H j false t a
  let f' := furnished Y H s G.history j false w x t h
  let g := slabT Y H t j false w' f' y
  have e : lantern Λ t w'=lantern Λ s w:= by
    unfold lantern; rw [show (w':ℤ)= castor δ s t (w:ℤ) from (by unfold w' castor; push_cast; rfl),notch_up _ _ _ h]
  have h' : ticket Y H G t (base Y H j t w' f').val=ticket Y H G s (base Y H j s w x).val:= by
    rw [show (base Y H j t w' f').val= spreadTo Y H G s t (base Y H j s w x).val from rfl]; exact ticket_spread Y H G h _
  refine ⟨enclose Y H G (flank j 0) false t (fromField Y H j t g),?_,?_⟩
  · rw [←e,←h']; exact combine_today Y H V G j t w' f' y
  rw [LightBudget.prepaid_enclose,LightBudget.prepaid_enclose]
  exact (snatch Y H V s G.history G.clipped j false C w x p h y).symm
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
