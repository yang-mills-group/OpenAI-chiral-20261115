import YM.CF.BProof.Mapping.Wheel

/- block potential certificate. works real or complex. Wall: Clock supplies
 an agreement (for core map, enlarged) through ORTH condition on nonzero domains (field type).
 `sup` prices over GOOD maps; assembly extension required before contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Account
open Function Filter MeasureTheory Prox Moment Finset RG Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {A X F : Type*}[Fintype A][MeasurableSpace X] [MeasurableSpace F] [NormedAddCommGroup F]
-- B static base. `adm` definitional guard, double argument used, not necessarily measurable.
variable (B: Base A)(adm:X→Prop)(agree:Finset A→ X→ X→ Prop)
structure Teller (I:Type*) (f:X→ F) (α C:ℝ) [Fintype I] where
 starboard : I→ Finset A
 size : I→ ℝ
 bill : I→ X→ F
 values x : adm x → f x = ∑ i,bill i x
 pay : Toll starboard size α C
 amount i (x:X) : adm x → ‖bill i x‖≤size i
 our i : (starboard i).Nonempty∧ B.C (starboard i)
 meas (i:I): Measurable (bill i)
 private_read i x y: agree (starboard i) x y→ adm x→ adm y→ bill i x=bill i y
namespace Teller
variable [BorelSpace F][SecondCountableTopology F]
variable {B agree adm}{f g : X→ F}{I I':Type*}[Fintype I][Fintype I']{C D a:ℝ}(T:Teller B adm agree I f a C)(U:Teller B adm agree I' g a D)
def add : Teller B adm agree (Sum I I') (f+g) a (C+D) where
 starboard:= Sum.elim T.starboard U.starboard
 size:= Sum.elim T.size U.size
 bill:= Sum.elim T.bill U.bill
 values x h:= by rw [Fintype.sum_sum_type]; exact congrArg₂ (·+·) (T.values x h) (U.values x h)
 pay:= Toll.sum T.starboard T.size T.pay U.starboard U.size U.pay
 amount i x h:=by cases i; exact T.amount _ _ h; exact U.amount _ _ h
 our i:=by cases i; exact T.our _; exact U.our _
 meas i:=by cases i; exact T.meas _; exact U.meas _
 private_read i x y h p q:=by cases i; exact T.private_read _ x y h p q; exact U.private_read _ x y h p q

-- zero entries might have no support; move at witness arbitrary B by monotonic reading by p=0
theorem weak [Nonempty A] (u:I→X→ F)(W:I→Finset A)(p:I→ℝ)(h:Toll W p a C)(v:∀ i,p i≠0→ (W i).Nonempty ∧ B.C (W i))(hx:∀ i x,adm x → ‖u i x‖≤p i)(k:∀ i,p i≠0→ ∀ x y, agree (W i) x y→ adm x→adm y→u i x=u i y) (hm:∀ i,Measurable (u i))(he:∀ x,adm x→ f x=∑ i,u i x): Nonempty (Teller B adm agree I f a C):=by
 let x:= Classical.arbitrary A; let Q(i:I):= if p i=0 then {x} else W i
 have hv:Toll Q p a C:=by
    have he (b:A): hit Q p a b= hit W p a b:=by ext i; by_cases H:p i=0; simp [hit,H]; simp [hit,Q,H]
    exact ⟨h.nonneg,fun i=>he i |>.symm ▸ h.pays i⟩
 refine ⟨Q,p,u,he,hv,hx,?_,hm,?_⟩
 · intro i; unfold Q; split; exact ⟨singleton_nonempty _,B.atom _⟩; exact v i ‹_›
 intro i x y h a b; unfold Q at h; split at h; next p=>
   have he(z:X)(k:adm z):u i z=0:= norm_le_zero_iff.mp (p ▸ hx i z k); rw [he x a,he y b]
 next u=>exact k i u x y h a b
end Teller
end YM.CF.BProof.Account
