import YM.SU5.Reconstruction.Chambers.Operator
import YM.SU5.Reconstruction.Brazier.Fare
import YM.SU5.Selected.CanCount
/-! Support localization in Central aperture, with local polynomial norm bills at EXACT translations. -/
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
open Chambers PhaseChoice
namespace Tarmac
local notation "Yx" => Year -- unused
variable (a:Tarmac)(w:ℕ)
local notation "rB"=> a.roof
local notation "Ψ"=>frameBudget a.book Λ l a.roof
local notation "Ar"=> a.land Λ l
local notation "A₁"=> (timeMesh Λ)
local notation "ax" w:max=>whenly (timeMesh Λ) a.roof w
local notation "V₊" h:max=> (strip j 0 (h:ℝ))
local notation "V₀" h:max=> strip j (-(h:ℝ)) (h:ℝ)
-- physical motion by an actual level-rB clock.Price.Between for perfect stamping.
structure Stage (Λ: Preparation) (l:ℕ)(j:Axis) (a:Tarmac)(w:ℕ): Prop where
 pos:0<w
 fits : land Λ l a⊆ Chambers.strip j (-(whenly (timeMesh Λ) a.roof w:ℝ)) (whenly (timeMesh Λ) a.roof w:ℝ)
private lemma lengthens (s:ℕ) : Tendsto (fun w:ℕ=> (whenly (timeMesh Λ) s w:ℝ)) atTop atTop := by
 simp only [whenly, NNReal.coe_natCast,NNReal.coe_mul]
 exact (tendsto_natCast_atTop_atTop).atTop_mul_const (mill_pos (timeMesh Λ) s) -- tune
lemma allStage : ∀ᶠ w in atTop,Stage Λ l j a w:=by
 obtain ⟨r,h⟩ := ((land_compact a (Λ:=Λ) (l:=l)).image (f:=fun x:RSpace=>|x j|) (by fun_prop)).bddAbove
 filter_upwards [(lengthens (Λ:=Λ) a.roof).eventually_ge_atTop r, eventually_gt_atTop (0:ℕ)] with w hw e
 refine ⟨e,fun x z=>?_⟩
 exact abs_le.mp ((h (Set.mem_image_of_mem (fun x:RSpace=>|x j|) z)).trans hw)
local notation "z'"=> eject j (w:ℤ)
abbrev center (w:ℕ): Dome (tent Y H) →ₗ[ℂ] Dome (tent Y H):= reposition (tent Y H) (eject j (w:ℤ))
noncomputable def balcony : Finset Cover:= streetBox (tent Y H) (eject j (w:ℤ)) (frameBudget a.book Λ l a.roof)
variable (p:Stage Λ l j a w)
lemma center_length (s w:ℕ): (whenly (timeMesh Λ) s (w+w):ℝ)=(whenly (timeMesh Λ) s w:ℝ)+(whenly (timeMesh Λ) s w:ℝ):=by simp [whenly,add_mul]
include p
lemma between : Between (tent Y H) j 0 (ruler Λ.block*(w+w:ℕ)) (a.balcony Y H j w):=by
 have he := slides_cov Y H a.roof (Ψ) (eject j (w:ℤ)) a.pays
 apply (strip_seats Y H j a.roof _).1
 apply (supported_iff ..).2
 refine ( (supported_iff ..).1 he).trans ?_
 rintro _ ⟨x, hx, rfl⟩; have hx:= p.fits hx
 simp only [Chambers.strip, mem_setOf_eq,stamps_eject,coordinates_eject,eject_at, Pi.add_apply, center_length] at hx ⊢; rw [show (notch (timeMesh Λ) a.roof (w:ℤ):ℝ)=ax w from natural_time ..]; constructor <;> linarith [hx.1,hx.2]
omit p
lemma center_shift (f:Dome (tent Y H))(h:f∈bay (tent Y H) (frameBudget a.book Λ l a.roof) true) : center Y H j w f∈ bay (tent Y H) (a.balcony Y H j w) true:=
 cad_test z' ordinate (h : InTest _ _ _ _ _)
variable {x:Cloud (Dome (tent Y H))}
lemma pocketRepresentation {r:ℝ}(p:Pocket (tent Y H) a.book a.roof r x) : ∃ b:Swatch (frameBudget a.book Λ l a.roof),
   render (frameBudget a.book Λ l a.roof) (tent Y H) b=((Kx a.roof) x).val ∧ ‖b‖ ≤ Hank Y H a.book a.roof B *r:=by
 induction p with
 | stone t u=>
   refine ⟨outfitView Y H a.roof a.book t B,?_, powers_payVista Y H a.book a.roof t⟩ -- arg order
   unfold motif pureShot vistaFinish; rw [Decking.reckon_paid _ _ _ u, Z.comparedVista Y H a.roof a.book]; rfl
 | no=> refine ⟨0,?_,?_⟩; rw [map_zero,map_zero]; rfl; rw [norm_zero,mul_zero] -- tune
 | blend _ _ p q=>
   obtain ⟨b,h,f⟩:= p; obtain ⟨c,t,g⟩:=q; refine ⟨b+c,by rw [map_add,map_add,h,t]; rfl,(norm_add_le ..).trans ((add_le_add f g).trans_eq (mul_add ..).symm)⟩
 | @shade x r z _ q=>
   obtain ⟨b,h,f⟩:=q; refine ⟨z•b,by rw [map_smul,map_smul,h]; rfl,?_⟩
   rw [norm_smul]; exact (mul_le_mul_of_nonneg_left f (norm_nonneg _)).trans_eq (by ring)
 | fully t _ q=> obtain ⟨b,h,f⟩:=q; exact ⟨b,h,f.trans (mul_le_mul_of_nonneg_left t (Hank_pos ..))⟩
lemma translatedWallet {r:ℝ}(q:Pocket (tent Y H) a.book a.roof r x) : ∃ b:Swatch (a.balcony Y H j w), render (a.balcony Y H j w) (tent Y H) b=(center Y H j w ((Kx a.roof) x)).val ∧
    ‖b‖ ≤ (spread (frameBudget a.book Λ l a.roof):ℝ) * (Hank Y H a.book a.roof B * r) := by
 have hv:= a.center_shift Y H j w _ (shaping Y H Z _ _ _ q) -- args
 let y:=center Y H j w ((Kx a.roof) x)
 obtain ⟨b,h⟩ := accolade K _ _ hv
 -- `h` type badge
 obtain ⟨c,t,e⟩ := a.pocketRepresentation Y H Z q
 have he: render (a.balcony Y H j w) K b = y.val:= congrArg Subtype.val h
 refine ⟨b,he,PhaseChoice.sample_price Y H _ b ?_⟩
 rw [he,show y.val=relocate K j w (render (Ψ) K c) from ((chart_eject j (J:=K) (w:ℤ) ((Kx a.roof) x)).trans (congrArg (relocate K j w) t.symm))]
 intro n U
 exact ((chime_pay _ j _ _ (PhaseChoice.rendered_price Y H _ c)) n U).trans (mul_le_mul_of_nonneg_left e (by positivity)) -- metavariable tune
end Tarmac
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
