import YM.SU5.Reconstruction.PilotLight.Meter
import YM.SU5.Reconstruction.PilotLight.Composition
import YM.SU5.Reconstruction.PilotLight.Rent
/-! Battery bookkeeping. At every applicable stencil. -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5700
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "J₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "T₀"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Lp'"=> Follows Y H V G j (c j) χ
variable {A B : (indoor Y H V G.history G.clipped j false (c j) χ).Op}
variable (s w:ℕ)
variable {x y:Dome (tent Y H)}
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
local notation "bP" n:max=> bAll Λ s w n
local notation "K₁"=> ticket Y H G s
local notation "vi"=> stamps Λ s (granite w)
local notation "Sp"=> splice Y H V G j (c j) χ
local notation "A₀" n:max=> insideAt Λ l (tent Y H) true (alcove (hAll Λ s w n)) s
local notation "A₁"=> insideAt Λ l (tent Y H) true (alcove g₁) s
local notation "Xp" n:max=>layers K x w n
local notation "Xa" n:max=>lantern K x w n

lemma oneCalibrates : Lp' 1 b₁ ((L).E g₁):= by have h:= bTime (Λ:=Λ) s w; have hp:=unitScore Y H V G j (c j) χ b₁ (by rw [h]; positivity); rwa [h,Real.toNNReal_coe] at hp
lemma total_unit (n:ℕ): Lp' 1 (bP n) ((L).E (g₂ n)):= by have h:= aTime (Λ:=Λ) s w n; have hp:=unitScore Y H V G j (c j) χ (bP n) (by rw [h]; positivity); rwa [h,Real.toNNReal_coe] at hp
lemma stack_precision' (t : x∈ A₁)(h: Lp' (K₁ x) b₁ A)(d:ℝ)(hd:‖A+(L).E g₁‖≤ d) (n:ℕ)(hw:0<w): ∃ Z:(J₀).Op,Lp' (K₁ (Xp n)) (bP n) Z ∧ ‖Z‖≤d^n:=by
 induction n with
 | zero=> rw [layer_starts,ticket_one]; exact ⟨_,total_unit ..,(by rw [pow_zero]; exact (L).shrinks _)⟩
 | succ n ih=>
   obtain ⟨Z,v,hz⟩:=ih
   let X:= (L).E g₁+A
   have He:Lp' (K₁ (1+x)) b₁ X:=by rw [map_add,ticket_one]; exact addScore Y H V G j (c j) χ (oneCalibrates Y H V G j c χ s w) h
   refine ⟨_,(along_stack Y H V G j (c j) χ s w hw ((A₁).add_mem (Subalgebra.one_mem _) t) (permit_layers Y H s w hw t n) He v),?_⟩
   have hA:‖X‖ ≤ d:= by unfold X; rwa [add_comm] -- trouble rwa uses goal
   rw [pow_succ']; exact (splicing ..).trans (mul_le_mul hA hz (norm_nonneg Z) ((norm_nonneg X).trans hA))
lemma stack_precision (t:x∈A₁)(h:Lp' (K₁ x) b₁ A)(d:ℝ)(hd:‖A+(L).E g₁‖≤d)(n:ℕ)(hw:0<w) : ∃ Z:(J₀).Op, Follows Y H V G j (c j) χ (ticket Y H G s (Xa n)) (bP n) Z ∧ ‖Z+(L).E (g₂ n)‖ ≤ d^n := by
 obtain ⟨B,u,q⟩:= stack_precision' Y H V G j c χ s w t h d hd n hw; unfold lantern; rw [map_sub,ticket_one];  refine ⟨_,subScore Y H V G j (c j) χ u (total_unit ..),by rw [sub_add_cancel]; exact q⟩ -- tune

variable {z:SU.Slot}{d:ℕ}{S:Finset Cover}{a:Fin d → Cover}
lemma every_cold (p:∀ j, Between (tent Y H) j 0 (ruler Λ.block*w) S)(t:Injective a)(hw:0<w){n:ℕ}{b:Bool}(e:Clause (tent Y H) z S a w n b x y)(hb:b=true): Lp' (ticket Y H G s y) (bP n) 0 :=by
 induction e with
 | begin_=> contradiction
 | later_ e ih=>
    rename_i b i x y; have he:= (clause_permitted Y H s w hw p e).2
    have h:= oneCalibrates Y H V G j c χ s w; rw [←ticket_one Y H G s] at h
    have hx:=along_stack Y H V G j (c j) χ s w hw ((A₁).one_mem) he h (ih hb); rw [one_mul] at hx; unfold splice at hx; rwa [mul_zero,zero_mul] at hx
 | here_ h e q ih=>
    rename_i b i g m x' y';
    have ht:= (clause_permitted Y H s w hw p q).2
    have hu:Lp' (K₁ y') b₁ 0:= vanishesLode Y H V G j (c j) S s w (p j) hw χ t (show y'.val∈ Lode K (Window.family z) a S from e)
    have hV:=roomKit Y H s w p (f:=y') (b':=false) (lode_base Y H e) nofun
    rcases Nat.eq_zero_or_pos i with HI|HI
    · subst i
      cases q
      rw [lined,reposition_unit];
      -- can use alongStack after resetting.
      have he:Lp' (K₁ 1) (bP 0) ((L).E (g₂ 0)):= (ticket_one Y H G s).symm ▸ total_unit Y H V G j c χ s w 0
      have hx:=along_stack Y H V G j (c j) χ s w hw hV ((A₀ 0).one_mem) hu he; unfold splice lined at hx; rwa [zero_mul,zero_mul,zero_mul,reposition_unit] at hx
    obtain ⟨B,Gb⟩:= fits Y H V G j (c j) χ (bP i) (by rw [aTime]; exact tPositive (Λ:=Λ) s hw HI) (K₁ m) (ticket_mem Y H G (insideAt_mono (show alcove (g₂ i) ⊆ Chambers.strip j 0 (bP i) from (by rw [aTime]; exact alcove_in_strip _ j)) ht))
    have hx:=along_stack Y H V G j (c j) χ s w hw hV ht hu Gb; unfold splice at hx; rwa [zero_mul,zero_mul,zero_mul] at hx
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.stack_precision
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.every_cold
