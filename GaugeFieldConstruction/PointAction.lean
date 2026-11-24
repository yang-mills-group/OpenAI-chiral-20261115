import GaugeFieldConstruction.Conj
import GaugeFieldConstruction.Motion

/-!
# Representation on fields from raw pivot spaces

`Transfer`: a class carries signed coordinate maps (outputs rotate in the
 *displacement* convention). No continuity or observer-limit assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Cauchy Conj Row Record U1 Raw Finset Function
open scoped BigOperators

namespace LabelAction
variable {X V I : Type*} {R : Record X V}

/-- Tax on any slot through grade five, making a table of
 extending representatives after quotient. -/
structure Carries (R : Record X V) (S : Submodule ℂ (J X)) where
  moves : Signed →* Module.End ℂ S
  transit {s w u} (h : R.poses s w u) (a : S) : R.tester u a= R.tester w (moves s a).val

namespace Carries

lemma fix {S} (B : Carries R S) (s : Signed) (f : Module.End ℂ S) (h : ∀ w u (p : R.poses s w u) (a : S), R.tester u a.val= R.tester w (f a).val) : B.moves s=f := by
  apply LinearMap.ext; intro i
  apply Subtype.ext
  apply ext_jet R.faith
  intro w; obtain ⟨u,p⟩:= R.permit s w; rw [← B.transit p i,h w u p]

lemma same {S T : Submodule ℂ (J X)} (A : Carries R S) (B : Carries R T) (s : Signed) (a : S) (b : T)
    (h : a.val=b.val) : (A.moves s a).val=(B.moves s b).val := by
  apply ext_jet R.faith
  intro i; obtain ⟨u,p⟩:=R.permit s i
  rw [← A.transit p,← B.transit p,h]

section Assign
variable (A : Labels I) [Fintype I] (q : I → J X)
abbrev issue (p : I→ℂ) : space q := ⟨Fintype.linearCombination ℂ q p, p, rfl⟩
lemma supplied (u : space q) : ∃ p, u=issue q p := by
  obtain ⟨x,h⟩:=u.property; exact ⟨x, Subtype.ext h.symm⟩

variable (h : R.Reading A q)
include h
lemma toll (s : Signed) (p : I → ℂ) (w u) (v : R.poses s w u) :
    R.tester u (issue q p).val= R.tester w (issue q (A.transport ℂ s p)).val := by
  unfold issue Fintype.linearCombination
  change R.tester u (∑ i : I,p i • q i) = R.tester w (∑ i : I,(A.transport ℂ s p) i • q i)
  conv_rhs=> rw [← Equiv.sum_comp (A.equivMove s)]
  rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _
  rw [map_smul,map_smul,h.moving s w u v i]
  change _ = (A.transport ℂ s p (A.move s i)) • R.tester w _
  rw [Labels.transport_value]; cases A.cost s i <;> simp [Labels.equivMove]

private def make_1 (s : Signed) (a : space q) : space q := issue q ((A.transport ℂ s) (supplied q a).choose)
lemma work {s w u} (v : R.poses s w u) (a : space q) : R.tester u a.val = R.tester w (make_1 A q s a).val := by
  unfold make_1; rw [← toll A q h s _ _ _ v,← (supplied _ a).choose_spec]

lemma accepts (s : Signed) (p : I→ℂ) : make_1 A q s (issue q p)=issue q (A.transport ℂ s p) := by
  apply Subtype.ext; apply ext_jet R.faith; intro w
  obtain ⟨u,m⟩:=R.permit s w; rw [← work A q h m,toll A q h s p w u m]
omit h
private def city (h : R.Reading A q) (s : Signed) : Module.End ℂ (space q) where
  toFun:=make_1 A q s
  map_add' a b:=by
    obtain ⟨x,rfl⟩:=supplied q a; obtain ⟨y,rfl⟩:=supplied q b
    have he (x y) : issue q (x+y)=issue q x+issue q y:= Subtype.ext (map_add ..)
    rw [← he]; simp only [accepts A q h,map_add]; exact he ..
  map_smul' t p:=by
    obtain ⟨x,rfl⟩:=supplied q p
    have he (x) : issue q (t • x)=t • issue q x := Subtype.ext (map_smul ..)
    rw [← he]; simp only [accepts A q h,map_smul]; exact he ..

def basic (h : R.Reading A q) : Carries R (space q) where
  moves:= {
    toFun:=city A q h
    map_one' := by
      apply LinearMap.ext; intro x; obtain ⟨x,rfl⟩:= supplied q x
      change make_1 A q 1 (issue q x)=_
      rw [accepts A q h]
      have e : A.transport ℂ 1 x=x:= by
        funext i; have t:=A.transport_value (K:=ℂ) 1 x i; simpa using t
      rw [e]; rfl
    map_mul' s t:=by
      apply LinearMap.ext; intro x; obtain ⟨x,rfl⟩:= supplied q x
      change make_1 _ _ _ _ = make_1 A q _ (make_1 A q _ _)
      simp only [accepts A q h]
      rw [← A.group]
      rfl }
  transit:= fun {s w u} v a=>work A q h v a

include h
lemma move_basis [DecidableEq I] (B : Carries R (space q)) (j : I) (x : space q) (hx : x.val=q j) (s : Signed) :
    (B.moves s x).val=pay (A.cost s j) (q (A.move s j)) := ext_jet R.faith fun i=> by
  obtain ⟨u,hp⟩ := R.permit s i
  rw [← B.transit hp,hx,h.moving s i u hp]
  cases A.cost s j <;> simp

lemma move_issue (B : Carries R (space q)) (p : I → ℂ) (s : Signed) :
    B.moves s (issue q p)= issue q (A.transport ℂ s p) := Subtype.ext <| ext_jet R.faith fun i=> by
      obtain ⟨u,hp⟩ := R.permit s i; rw [← B.transit hp,toll A q h s p i u hp]

variable (F : Flip X) (z : ∀ i,F (q i)=q i)
include z
omit h in
lemma converted (p : I → ℂ) : F (issue q p).val = (issue q (fun i=> bar (p i))).val := by
  change F (∑ i : I,p i • q i)= ∑ i : I,bar (p i) • q i
  rw [map_sum]; simp only [LinearMap.map_smulₛₗ,z]
omit h in
lemma converts {v : J X} (p : v ∈ space q) : F v ∈ space q := by
  obtain ⟨x,rfl⟩:= p
  change F (issue q x).val ∈ _
  rw [converted q F z]; apply Subtype.coe_prop
lemma c_pres (T : Carries R (space q)) (v : space q) (b : space q) (u : b.val=F v.val) (s) :
    F (T.moves s v).val=(T.moves s b).val := by
  obtain ⟨p,rfl⟩:=supplied q v; rw [converted q F z] at u
  rw [show b=_ from Subtype.ext u, move_issue A q h,move_issue A q h,converted q F z]
  congr; ext i
  obtain ⟨j,rfl⟩:= (A.equivMove s).surjective i
  change _ = _; dsimp only [Labels.equivMove, Equiv.coe_fn_mk]; rw [Labels.transport_value,Labels.transport_value]; cases A.cost s j <;> simp
end Assign

lemma turn_field {X' U} (L : Labels X') (B : Carries R U) (q : X'→ ↥U) : (fun i => (q i).val) ∈ R.tensors L ↔
    ∀ s i, B.moves s (q i) = pay (L.cost s i) (q (L.move s i)) := by
  constructor
  · intro h s i; apply Subtype.ext; apply ext_jet R.faith; intro w
    obtain ⟨u,p⟩:=R.permit s w
    rw [← B.transit p]
    have hv := h s w u p i
    cases e:L.cost s i <;> simpa [e] using hv
  intro h s w u p i
  have ht := B.transit p (q i); rw [h s i] at ht
  cases e:L.cost s i <;> simpa [e] using ht
end Carries
end LabelAction
end YM.GaugeFieldConstruction
