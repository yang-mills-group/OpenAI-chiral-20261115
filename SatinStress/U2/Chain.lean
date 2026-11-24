import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The two-step chain at (93), (94)

We'll instantiate on the actual g/f/x polynomial tests, using U1; on an interacting
price system the fields and these data (and in particular the coordinate frames for
using weak convergence on them) still have to be *constructed*. This file will keep
types flexible. The spacing between the two sectors of the chain makes clear which
test rank is needed. The last space Z need not be finite dimensional (all kernel
tests, including m arbitrary). No notion here of degree-six physical symbol.
-/
namespace SatinStress
namespace U2
open Function (Injective Surjective Bijective)
open Module (finrank)

variable (K T V W Z : Type*) [Field K] [AddCommGroup T] [Module K T]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]

structure ChainData where
  grad : T →ₗ[K] V
  divg : T →ₗ[K] W
  obstruction : (V × W) →ₗ[K] Z

variable {K T V W Z}
namespace ChainData

variable (C : ChainData K T V W Z)

def previous := C.grad.prod C.divg
@[simp] lemma previous_apply (x : T) : C.previous x=(C.grad x,C.divg x) := rfl
abbrev supply := C.divg.ker -- conserved space
/-- (93) kills (94) by actual derivatives on kernel tests. -/
def Closed : Prop := ∀ x, C.obstruction (C.previous x)=0
/-- U1--U2 exact rank theorem conclusions on this chain -/
structure Full : Prop where
  injective_grad : Injective C.grad
  exhaustion : LinearMap.range C.previous = LinearMap.ker C.obstruction
lemma Full.unique {C : ChainData K T V W Z} (h : C.Full) : Injective C.previous :=
  fun _ _ e => h.injective_grad (congr_arg Prod.fst e)
lemma Full.close {C : ChainData K T V W Z} (h : C.Full) : C.Closed := by
  intro x
  apply LinearMap.mem_ker.mp
  rw [← h.exhaustion]
  exact ⟨x,rfl⟩
lemma Full.solves {C : ChainData K T V W Z} (h : C.Full) (x : V × W) (hx : C.obstruction x = 0) :
    ∃! T', C.previous T' = x := by
  obtain ⟨X,rfl⟩ := (show x ∈ C.previous.range from h.exhaustion ▸ LinearMap.mem_ker.mpr hx)
  exact ⟨X,rfl,fun i e => h.unique e⟩

section Prod
variable {T' V' W' Z' : Type*} [AddCommGroup T'] [Module K T']
  [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
  [AddCommGroup Z'] [Module K Z'] (C' : ChainData K T' V' W' Z')

def twine : ((V×V') × (W×W')) ≃ₗ[K] (V×W) × (V'×W') where
  toFun z := ((z.1.1,z.2.1), (z.1.2,z.2.2))
  invFun z := ((z.1.1,z.2.1), (z.1.2,z.2.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prod : ChainData K (T×T') (V×V') (W×W') (Z×Z') where
  grad := C.grad.prodMap C'.grad
  divg := C.divg.prodMap C'.divg
  obstruction := (C.obstruction.prodMap C'.obstruction).comp twine.toLinearMap

@[simp] lemma prod_grad (x) : (C.prod C').grad x = (C.grad x.1,C'.grad x.2) := rfl
@[simp] lemma prod_divg (x) : (C.prod C').divg x = (C.divg x.1,C'.divg x.2) := rfl
lemma prod_obstruction (x) : (C.prod C').obstruction x = (C.obstruction (x.1.1,x.2.1), C'.obstruction (x.1.2,x.2.2)) := rfl

variable {C C'}
lemma Full.prod (h : C.Full) (h' : C'.Full) : (C.prod C').Full := by
  constructor
  · exact fun _ _ e => Prod.ext (h.injective_grad (congr_arg Prod.fst e)) (h'.injective_grad (congr_arg Prod.snd e))
  apply le_antisymm
  · rintro y ⟨t,rfl⟩
    exact LinearMap.mem_ker.mpr (show (C.obstruction (C.previous t.1), C'.obstruction (C'.previous t.2))=0 by
      rw [h.close,h'.close]; rfl)
  rintro ⟨v,w⟩ H
  have e := LinearMap.mem_ker.mp H
  obtain ⟨x,hx,_⟩ := h.solves _ (show C.obstruction (v.1,w.1)=0 from congr_arg Prod.fst e)
  obtain ⟨y,hy,_⟩ := h'.solves _ (show C'.obstruction (v.2,w.2)=0 from congr_arg Prod.snd e)
  exact ⟨(x,y), (twine (K:=K)).injective (Prod.ext hx hy)⟩

def prodParts (s : Submodule K W) (s' : Submodule K W') : s.prod s' ≃ₗ[K] (s × s') where
  toFun x := (⟨x.val.1,x.property.1⟩, ⟨x.val.2,x.property.2⟩)
  invFun x := ⟨(x.1.val,x.2.val),x.1.property,x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma prod_rank_div (C : ChainData K T V W Z) (C' : ChainData K T' V' W' Z') [FiniteDimensional K T] [FiniteDimensional K T'] :
    finrank K ((C.prod C').divg.range) = finrank K (C.divg.range) + finrank K (C'.divg.range) := by
  unfold prod; dsimp only
  rw [LinearMap.range_prodMap, (prodParts _ _).finrank_eq,Module.finrank_prod]
end Prod

section Dimension
variable {C} [FiniteDimensional K T] [FiniteDimensional K V] [FiniteDimensional K W]
omit [FiniteDimensional K T] in
lemma Full.count (u : C.Full) : finrank K (C.obstruction.range) + finrank K T = finrank K V + finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker C.obstruction
  rwa [Module.finrank_prod, ← u.exhaustion, LinearMap.finrank_range_of_inj u.unique] at h
end Dimension
end ChainData
end U2
end SatinStress
