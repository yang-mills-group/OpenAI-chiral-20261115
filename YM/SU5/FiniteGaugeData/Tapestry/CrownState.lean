import YM.SU5.FiniteGaugeData.Tapestry.Belvedere
import Mathlib.Order.Filter.AtTopBot.Basic
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
/-!
# Evaluating the polynomial algebra. (Probabilistic normalization when separately supplied)

A state `fadeRead` on the entire algebra once the levels are coherent. Arbitrary
extensions to non-prefinite uses are not relevant; all our states on hierarchy
and here referred as such live on the `PreFinite` span. This module bundles
neither reflection nor positivity (they require separate work using support). It
proves basic coherence (even off-payment for a total mathematical chain). It
also exposes finite-reading lemma: projection from a polynomial of height ≤ n
to height n and then n+1 (with no new observations inserted) is just surge of
the projection. Use to show marginals for any partial state, finite-cutoff etc.
-/
namespace YM.CF.Buffered.Afterglow.Tapestry.Altitude
open Function Filter Finset TensorProduct
open scoped BigOperators Classical
open PiTensorProduct (tprod)
variable {A:Type*}[CommRing A][Algebra ℂ A]
variable {E:ℕ→Type*}[∀ i,CommRing (E i)][∀ i,Algebra ℂ (E i)]
variable (D: Decking A E)
variable (n j:ℕ)(x:Cloud A)(v:Pad A)(θ:∀ i,E i→ₗ[ℂ]ℂ) (u : ∀ i,(θ (i+1)).comp (D.surge i)=θ i)
namespace Decking
lemma joins (p:x∈shorter A n): crown D v (n+1) x=D.surge n (crown D v n x):=by
  apply boarded (M:=fun x=>_) (P:={f|Enough n f}) ?_ ?_ ?_ ?_ p
  · intro f t; have q:Enough n f:=t
    rw [D.reckon_paid n v q, D.reckon_paid (n+1) v (q.taller (by omega))]; rw [Decking.finish,q (n+1) (by omega),map_one,mul_one]
  · simp
  · intro t g h q i j; rw [map_add,map_add,map_add,i,j]
  intro r y p h; rw [map_smul,map_smul,map_smul,h]
-- climb if state edges paid only below top
lemma partial_fin (q : ∀ i<j,(θ (i+1)).comp (D.surge i)=θ i)(w:n≤j)(p:x∈shorter A n): θ j (crown D v j x)=θ n (crown D v n x):=by
  induction j, w using Nat.le_induction with
  | base=>rfl
  | succ t h ih=> rw [joins D t x v (climbs A h p),←LinearMap.comp_apply, q t (by omega)]; exact ih fun i k=> q i (by omega)
section
include u
lemma clarion : ∃ z:ℂ, ∀ᶠ n in atTop, θ n (crown D v n x)=z:=by
  induction x using PiTensorProduct.induction_on with
  | add x y hx hy=> obtain ⟨p,q⟩:=hx; obtain ⟨s,t⟩:=hy; exact ⟨p+s,(q.and t).mono fun n h=> by rw [map_add,map_add,h.1,h.2]⟩
  | smul_tprod r f=>
     by_cases h:PreFinite f
     · obtain ⟨n,t⟩:=h; have he : r • tprod ℂ f∈shorter A n:= (shorter A n).smul_mem (board (P:={f:ℕ→ A|Enough n f}) t) _; exact ⟨_,(eventually_ge_atTop n).mono fun j p=>partial_fin D n j _ v θ (fun i _=>u i) p he⟩
     exact ⟨0,Eventually.of_forall fun i=>by rw [map_smul,D.reckon_unsupported i v _ h,smul_zero,map_zero]⟩

-- avoiding explicit value on nonprefinite
omit u
private lemma marchXYZ {X:Type*} (f:ℕ→X)(u v:X) (p:∀ᶠ t in atTop,f t=u)(q:∀ᶠ t in atTop,f t=v): u=v:= by obtain ⟨t,h,h'⟩:= (p.and q).exists; exact h.symm.trans h'
include u
local notation "ζ" => D.clarion
private def fade (x:Cloud A):ℂ:= (D.clarion x v θ u).choose
lemma faded(x:Cloud A): ∀ᶠ n in atTop, θ n (crown D v n x)=fade D v θ u x := (D.clarion x v θ u).choose_spec
def fadeRead : Cloud A →ₗ[ℂ]ℂ where
 toFun:= fade D v θ u
 map_add' x y:= marchXYZ _ _ _ (D.faded v θ u (x+y)) (((D.faded v θ u x).and (D.faded v θ u y)).mono fun i h=>by rw [map_add,map_add,h.1,h.2])
 map_smul' z x:= marchXYZ _ _ _ (D.faded v θ u (z • x)) ((D.faded v θ u x).mono fun i h=>by rw [map_smul,map_smul,h]; rfl)
lemma burnIn : ∀ᶠ n in atTop, θ n (crown D v n x)=fadeRead D v θ u x:= D.faded v θ u x
lemma fate (p:x∈shorter A n): fadeRead D v θ u x=θ n (crown D v n x):= marchXYZ _ _ _ (D.burnIn x v θ u) ((eventually_ge_atTop n).mono fun i h=>partial_fin D n i x v θ (fun i _=>u i) h p)
lemma fadeOne (h:θ 0 1=1): fadeRead D v θ u 1=1:=by rw [D.fate 0 1 v θ u (shorter A 0|>.one_mem),crown1,h]
lemma fatePad(p:x∈Polynomials A)(w:Pad A): fadeRead D v θ u x=fadeRead D w θ u x:=by obtain ⟨n,p⟩:= curve.mp p; rw [D.fate n x v θ u p, D.fate n x w θ u p,D.solely n v x p w] -- order
end
end Decking
end YM.CF.Buffered.Afterglow.Tapestry.Altitude
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking.fadeOne
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking.joins
