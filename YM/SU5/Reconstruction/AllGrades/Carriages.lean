import YM.SU5.Reconstruction.AllGrades.Balcony
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "S"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
-- $Epoch uses Matter pitch argument. Every motion through these stamps ACTUAL chime.
lemma march_sums {J:Calibration}{f:Family J}{B:Finset Cover}(p:InTest J true B b f)(x y:ℤ): chime J a x (chime J a y f)= chime J a (x+y) f:=by rw [←moted J a (x+y) y x (flow_port J a y p) (by omega),show chime J a y f=mirror J a y (mirror J a 0 f) from rfl,reversal J a y (axial J a 0 p)]; rfl
lemma march_comm {J:Calibration}{f:Family J}{B:Finset Cover}(p:InTest J true B b f)(x y:ℤ)(j:Axis): chime J j x (chime J a y f)= chime J a y (chime J j x f):=by
 by_cases h:j=a
 · subst j; rw [march_sums a b p,march_sums a b p,add_comm x]
 change chime J j x (mirror J a y (mirror J a 0 f))=mirror J a y (mirror J a 0 (chime J j x f))
 rw [straddle j a h x y (axial J a 0 p),straddle j a h x 0 p]
lemma march_zero {J:Calibration}{f:Family J}{B:Finset Cover}(p:InTest J true B b f):chime J a 0 f=f:=reversal J a 0 p
lemma march_flip {J:Calibration}{f:Family J}{B:Finset Cover}(p:InTest J true B b f)(x:ℤ): mirror J a 0 (chime J a x f) = chime J a (-x) (mirror J a 0 f):=by rw [←moted J a 0 (-x) x p (by omega),reversal J a 0 (axial J a (-x) p),chime,reversal J a 0 p]
-- displace in half‐epoch geometry for horizontal or vertical Stamp. retain stamps positive by WOT grid only.
noncomputable def cart (j:Axis)(z:ℤ)(u:a=j→ 0 ≤ z): S→ₗ[ℂ] S where
 toFun f:= ⟨C₀ j z f.val,by
    obtain ⟨T,p,t⟩:= atSouth Y H a b f; let p':=flow_port K j z p; refine ⟨_,p', fun i v=>?_⟩; obtain ⟨i',w,rfl⟩:= Finset.mem_image.mp v; specialize t i' w; rw [SlabMark.moves]; split
    next h=> subst j; have h:=u rfl; linarith
    next=>exact t⟩
 map_add' _ _:= Subtype.ext (chime_plus ..)
 map_smul' _ _:=Subtype.ext (chime_scale ..)
local notation "Ct"=> cart Y H a b
lemma cart_apply (x:S)(j t p): (Ct j t p x).val= chime K j t x.val:=rfl
lemma cart_sums (x:S)(j:Axis){t u:ℤ}(p:a=j→0 ≤ t)(q:a=j→0 ≤ u): Ct j t p (Ct j u q x)=Ct j (t+u) (fun e=> add_nonneg (p e) (q e)) x:=Subtype.ext (march_sums j b (atSouth Y H a b x).choose_spec.1 t u)
lemma cart_zero(x:S)(j:Axis): Ct j 0 (fun _=>le_rfl) x=x:=Subtype.ext (march_zero j b (atSouth Y H a b x).choose_spec.1)
lemma cart_comm(x:S)(j k:Axis)(t u:ℤ)(p:a=j→0 ≤ t)(q:a=k→0 ≤ u):Ct j t p (Ct k u q x) = Ct k u q (Ct j t p x):= Subtype.ext (march_comm k b (atSouth Y H a b x).choose_spec.1 t u j)
-- congruence convenience for eliminating the dependent p.
lemma cart_eq{t u:ℤ}{j:Axis}{p:a=j→0≤ t}{q:a=j→0≤u}(e:t=u): Ct j t p=Ct j u q:=by subst_vars; rfl
variable (j:Axis)(z:ℤ)
lemma cart_up {s t:ℕ}(p:s≤ t)(v:a=j→0 ≤ z)(x:S): hP p (Ct j z v x)= Ct j ((Λ.R.L.val:ℤ)^(t-s)*z) (fun i=> mul_nonneg (by positivity) (v i)) (hP p x):=Subtype.ext (flight_chime Y H V s G D (atSouth Y H a b x).choose_spec.1 (t-s) j z)
variable (x y:studio (tent Y H) a 0 b)
private lemma packatSouth : TestFamily (tent Y H) true (mirror K a 0 x.val * y.val):=by
 obtain ⟨B,h,_⟩:=atSouth Y H a b x; obtain ⟨U,v,_⟩:=atSouth Y H a b y; let Z:=reflectedBox a 0 B ∪ U; have ht:InTest K true Z (Bool.xor b b) (mirror K a 0 x.val * y.val):= InTest.mul (((axial K a 0 h)).mono Finset.subset_union_left) (v.mono Finset.subset_union_right); rw [Bool.xor_self] at ht; exact aux_test ht
lemma rune_shift (h:a≠ j): inner ℂ ((Bp s) (Ct j (2*z) (fun v=>False.elim (h v)) x)) ((Bp s) (Ct j (2*z) (fun v=> False.elim (h v)) y)) = inner ℂ ((Bp s) x) ((Bp s) y):=by
 rw [measures_here,measures_here]; unfold poleForm; rw [cart_apply,cart_apply, ← straddle j a h.symm (2*z) _ ((atSouth Y H a b x).choose_spec.1), ← chime_product, ← chime_scale]; exact P.parity s j z (printedS Y H a b x y)
lemma lectern (T:ℤ) (v:0 ≤ T): inner ℂ ((Bp s) x) ((Bp s) (Ct a (2*T) (fun _=> mul_nonneg (by decide) v) y)) = inner ℂ ((Bp s) (Ct a (2*T) (fun _=> mul_nonneg (by decide) v) x)) ((Bp s) y):=by
 let p₀:= (fun (_:a=a)=>mul_nonneg (show 0≤(2:ℤ) by decide) v); let X:=Ct a (2*T) p₀ x
 rw [measures_here,measures_here,← P.parity s a T (printedS Y H a b X y)]; unfold poleForm X; rw [cart_apply,cart_apply,march_flip a b ((atSouth Y H a b x).choose_spec.1),chime_scale,chime_product,march_sums a b (axial (tent Y H) a 0 ((atSouth Y H a b x).choose_spec.1)),add_neg_cancel, march_zero a b (axial _ a 0 ((atSouth Y H a b x).choose_spec.1))]

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.cart
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.cart_up
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.rune_shift
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.lectern
