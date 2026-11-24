import YM.SU5.FiniteGaugeData.Indigo.Carda
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "U"=> W (tent Y h)
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
variable {a:Axis}{d w n m:ℕ}{x f:W (tent Y h)}{vD:Axis→ℕ}(L:Master Y s i)(lP:Club Y g s)

namespace Bonbon
open Steam.Indigo
variable (Z:Finset (Face ℤ)) (C':ℝ) (p q j:ℕ) (f: W (tent Y h))
abbrev triggerM (r:ℝ)(i:Side)(x:Pane ((tent Y h).c i)) : Prop:= alarm Z (μX Λ s r) (onC _ x,onC _ x) -- Kₜ . notation fix
abbrev swatch(r:ℝ): W (tent Y h):= seesT Kₜ Z (μX Λ s r)
local notation "L"=> swatch Y h s Z -- L shadows Master but omit
local notation "A₁"=>triggerM Y h s Z
-- geometry
variable (r u':ℝ)
lemma trigger' {i:Side}(x:Pane ((tent Y h).c i)) (v:u' ≤ r) (e:A₁ r i x) : A₁ u' i x:=by obtain ⟨j,p,e⟩:=e; exact ⟨j,p,(div_le_div_of_nonneg_right v (boostP Y s).le).trans_lt e⟩
open scoped Classical
lemma stroke (i:Side)(x:Buffered.Fields ((tent Y h).c i)): (L r).val i x= if A₁ r i x.1 then 1 else 0 :=by
 change (if alarm Z (μX Λ s r) (onC _ x.1, onC _ x.2) then (1:ℂ) else 0) • (1:FC _) = _
 by_cases v:A₁ r i x.1; rw [if_pos (show alarm Z (μX Λ s r) ( onC _ x.1,onC _ x.2) from v),if_pos v,one_smul]; rw [if_neg (show ¬alarm Z (μX Λ s r) (onC _ x.1,onC _ x.2) from v),if_neg v,zero_smul]
lemma plenty : ∀ᶠ p:ℕ in atTop, ∀ i:Side, ∀ x:Pane ((tent Y h).c i), ¬triggerM Y h s Z p i x :=by
 let μω:=cool_ι Λ s; obtain ⟨w,t⟩:= exists_nat_ge (2*μω); filter_upwards [eventually_ge_atTop w] with p g i x a; obtain ⟨j,v,a⟩:=a; exact (a.trans_le (SU.group.chord_le_two _)).not_ge ((le_div_iff₀ (boostP Y s)).mpr (t.trans (Nat.cast_le.mpr g)))
lemma swatchV : swatch Y h s Z r* swatch Y h s Z r = L r:=by apply Subtype.ext; funext m x; change (L r).val _ _*(L r).val _ _=_; rw [stroke]; split <;> simp
lemma swatchZ (p:∀ i:Side,∀ x, ¬ triggerM Y h s Z r i x): L r=0:=by apply Subtype.ext; funext i x; rw [stroke,if_neg (p _ _)]; rfl
lemma turfS (g:carpet Z⊆S): Locator Kₜ (swatch Y h s Z r) S:= locate_sub Kₜ (show Locator Kₜ _ _ from undone Kₜ Z (μX Λ s r)) g
lemma locW_sub (P Q:W Kₜ)(w:Locator Kₜ P S)(q:Locator Kₜ Q S): Locator Kₜ (P-Q) S:=by rw [show P-Q=P+(-1:ℂ)•Q from (by module)]; exact locate_sum Kₜ _ w (locate_scale _ _ _ q)
-- polynomial growth certificate inside *whole* W space
structure Tulle (s:ℕ)(Z:Finset (Face ℤ))(p:ℕ)(C:ℝ) (f:W (tent Y h)) : Prop where
 zeroB : 0 ≤ C
 bound(j:ℕ)(e:0<j)(i:Side)(x:Buffered.Fields ((tent Y h).c i)): ¬triggerM Y h s Z j i x.1 → ‖f.val i x‖≤ C*j^p -- cast? j^p nat then coe
variable (t:Tulle Y h s Z p C f)
abbrev insideM (n:ℕ)(f:W (tent Y h)):= (1-swatch Y h s Z n)*f
local notation "J'"=> insideM Y h s Z
include t
lemma innerP(n:ℕ)(p':0<n): Width Kₜ (insideM Y h s Z n f) (C*n^p):=by
 intro i x; let V:=swatch Y h s Z n; change ‖((1:FC _)-V.val _ _)*_‖≤_; unfold V; rw [stroke]; split; · rw [sub_self,zero_mul,norm_zero]; exact mul_nonneg t.zeroB (by positivity)
 rename_i e; rw [sub_zero,one_mul]; exact t.bound n p' i x e
omit t
lemma loomBracket (v:q≤j): L (q:ℝ)* L j=L j:=by
 apply Subtype.ext; funext m x; change (L _).val _ _*(L _).val _ _=_; rw [stroke,stroke]; split_ifs with f g g; simp; simp; exact False.elim (f (trigger' Y h s Z j q _ (by exact_mod_cast v) g)); simp
lemma faithful (n:ℕ): L (n:ℝ) * f= L (n:ℝ)*insideM Y h s Z (n+1) f+L (↑(n+1:ℕ):ℝ)*f:=by
 unfold insideM; let A:=swatch Y h s Z; rw [←mul_assoc,_root_.mul_sub,mul_one,loomBracket Y h s Z n (n+1) (by omega)]; rw [_root_.sub_mul]; exact (sub_add_cancel ..).symm -- RHS maybe simpl
#print axioms innerP
end Bonbon
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
