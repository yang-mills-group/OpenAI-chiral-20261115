import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
/-!
# Resolution-polynomial mechanics

Use standard mathlib `PiTensorProduct`, but only PREFINITE submodules or
subalgebras of it. No formal infinite pure tensors used as physical observables.
There is also a non-redundant mathematical restriction posed by this definition:
slots commute across levels. So they will only be instantiated in this work with
scale-wise EVEN tests. If allowing charges spanning several levels with an odd
number of generators at some levels, one may want multiplication twisted with an
explicit Koszul sign. This is not aiming at a theory of those fields.
-/
namespace YM.CF.Buffered.Afterglow.Tapestry
namespace Altitude
open Function Filter Finset TensorProduct
open scoped BigOperators Classical
open PiTensorProduct (tprod)
variable (A:Type*)[CommRing A][Algebra ℂ A]
abbrev Cloud := PiTensorProduct ℂ fun _ : ℕ=> A
-- pure course of an experiment
variable {A} {f g:ℕ→A}
def Enough (n:ℕ) (f:ℕ→A) := ∀ i, n < i → f i=1
def PreFinite (f:ℕ→A) : Prop:= ∃ n:ℕ, Enough n f
theorem Enough.taller {n t:ℕ}(h:Enough n f)(p:n ≤ t): Enough t f:= fun i g=>h i (p.trans_lt g)
theorem Enough.together {n:ℕ}(h:Enough n f)(v:Enough n g): Enough n (f*g):= fun i p=> by rw [Pi.mul_apply,h i p,v i p,one_mul]
theorem enough1 (n : ℕ): Enough n (1:ℕ→ A):= fun i _=>rfl
theorem preFinite1 : PreFinite (1:ℕ→A):= ⟨0,enough1 _⟩
theorem PreFinite.together (h:PreFinite f)(p:PreFinite g): PreFinite (f*g):= by obtain ⟨n,v⟩:=h; obtain ⟨m,x⟩:=p; exact ⟨max n m,((v.taller (le_max_left ..)).together (x.taller (le_max_right ..)))⟩
-- unbundled linear span because sufficient most uses. We provide subalgebra packaging.
def heights (P:Set (ℕ→ A)) : Submodule ℂ (Cloud A):= Submodule.span ℂ (tprod ℂ '' P)
theorem board {P:Set (ℕ→ A)}(p:f∈P): tprod ℂ f∈ heights P:= Submodule.subset_span (Set.mem_image_of_mem (tprod ℂ) p)
@[elab_as_elim]
theorem boarded {P:Set (ℕ→A)} {M: (Cloud A)→ Prop} (h:∀ f,f∈P→ M (tprod ℂ f))(z:M 0)(a:∀ x y, x∈ heights P→ y∈ heights P→ M x→ M y→ M (x+y))(w:∀ (z:ℂ) x,x∈heights P→M x→ M (z • x)){x:Cloud A}(q:x∈heights P): M x := by
 apply Submodule.span_induction (p:=fun x (v:x∈heights P)=> M x) ?_ z a w q
 rintro _ ⟨y,p,rfl⟩; exact h y p
lemma expandHeights {P Q:Set (ℕ→A)} (h:P⊆Q): heights P ≤ heights Q:= Submodule.span_mono (Set.image_mono h)
private lemma mount {P : Set (ℕ→A)} (b : ∀ x∈P, ∀ y∈P,x*y∈P) {x y: Cloud A}(u:x∈heights P)(v:y∈heights P):x*y∈heights P:=by
  apply boarded (M:=fun x=> x*y∈heights P) ?_ (by rw [zero_mul]; exact Submodule.zero_mem _) (by intro a c u v h t; rw [add_mul]; exact (heights P).add_mem h t) (by intro z a p h; rw [Algebra.smul_mul_assoc]; exact (heights P).smul_mem z h) u
  intro x p; apply boarded (M:=fun y=> tprod ℂ x*y∈heights P) ?_ (by rw [mul_zero]; exact (heights P).zero_mem) (by intro a c u v h t; rw [mul_add]; exact (heights P).add_mem h t) (by intro z a p h; rw [Algebra.mul_smul_comm]; exact (heights P).smul_mem z h) v -- direction check
  intro y h; rw [PiTensorProduct.tprod_mul_tprod]; exact board (b _ p _ h)

def spires (P : Set (ℕ→A))(p : (1:ℕ→A)∈P)(b : ∀ x∈P, ∀ y∈P,x*y∈P) : Subalgebra ℂ (Cloud A) where
 carrier:=heights P
 one_mem':= board p
 zero_mem':=(heights P).zero_mem
 add_mem':=fun x y=> (heights P).add_mem x y
 mul_mem':=fun x y=> mount b x y
 algebraMap_mem':=fun r=>by rw [Algebra.algebraMap_eq_smul_one]; exact (heights P).smul_mem r (board p)
lemma spiresSub (P:Set (ℕ→A))(p : (1:ℕ→A)∈P)(b): (spires P p b).toSubmodule= heights P:=rfl

variable (A)
/-- Only actual resolution polynomials, not arbitrary members of the tensor ambient space. -/
def Polynomials : Subalgebra ℂ (Cloud A):= spires {f|PreFinite f} preFinite1 (fun x p y q=> PreFinite.together p q)
def shorter (n: ℕ): Subalgebra ℂ (Cloud A):= spires {f| Enough n f} (enough1 n) (fun x p y q=> Enough.together p q)
lemma delimit (n): shorter A n≤ Polynomials A:= expandHeights (P:={f:ℕ→A | Enough n f}) (fun x (hx:Enough n x)=>⟨n,hx⟩)
lemma climbs {n m}(h:n≤m): shorter A n≤ shorter A m:= expandHeights (P:={f:ℕ→A | Enough n f}) (fun x hx=> Enough.taller hx h)
variable {A}
theorem curve {v:Cloud A}: v∈ Polynomials A ↔ ∃ n,v∈shorter A n := by
  refine ⟨fun p=> ?_,fun ⟨n,v⟩=> delimit A n v⟩
  apply boarded (P:={f:ℕ→A|PreFinite f}) (M:=fun v=>∃ n,v∈shorter A n) ?_ ?_ ?_ ?_ p -- M?
  · rintro f ⟨n,h⟩; exact ⟨n, board (P:={f|Enough n f}) h⟩
  · exact ⟨0,(shorter ..).zero_mem⟩
  · rintro x y _ _ ⟨s,t⟩ ⟨p,q⟩; exact ⟨max s p,(shorter ..).add_mem (climbs A (le_max_left ..) t) (climbs A (le_max_right ..) q)⟩
  rintro z x _ ⟨n,p⟩; exact ⟨n,(shorter ..).smul_mem p z⟩
-- useful height-induction at P constrained (with other arguments)
lemma curveAbove (n) {P:Set (ℕ→ A)}(b:(1:ℕ→ A)∈P)(u:∀ x∈P,∀ y∈P,x*y∈P)(c:∀ x∈P,Enough n x): spires P b u≤shorter A n:= expandHeights c -- subset quantifier?
lemma curve_union {P : ℕ→ Set (ℕ→ A)}(h:Monotone P){x:Cloud A}: x∈ heights (⋃ i:ℕ,P i) ↔ ∃ i:ℕ,x∈ heights (P i):=by
  let Q:=fun i=> heights (P i); have hc:Monotone Q:=fun _ _ k=>expandHeights (h k)
  refine ⟨fun t=> ?_,fun ⟨i,q⟩=>expandHeights (Set.subset_iUnion P i) q⟩
  apply boarded (P:=⋃ i:ℕ,P i) (M:=fun x=>∃ i:ℕ,x∈heights (P i)) ?_ ?_ ?_ ?_ t
  · rintro f h; obtain ⟨i,h⟩:= Set.mem_iUnion.mp h; exact ⟨i,board h⟩
  · exact ⟨0,(Q 0).zero_mem⟩
  · rintro x y _ _ ⟨n,v⟩ ⟨r,t⟩; exact ⟨max n r,(Q (max n r)).add_mem (hc (le_max_left ..) v) (hc (le_max_right ..) t)⟩
  rintro z x _ ⟨n,v⟩; exact ⟨n,(Q n).smul_mem z v⟩
variable (A)
-- one explicit slot, in the shorter window. record identities and optional injection later.
def pinhole (n:ℕ) : A →ₐ[ℂ] Cloud A := PiTensorProduct.singleAlgHom (R:=ℂ) (A:=fun _=>A) n -- tune universe
variable {A}
lemma pinhole_apply (i:ℕ)(x:A) : pinhole A i x=tprod ℂ (update (fun _ : ℕ=> (1:A)) i x):=rfl
lemma enough_slot (i:ℕ)(x:A): Enough i (update (1:ℕ→A) i x):=fun j h=>by rw [update_of_ne h.ne']; rfl
lemma short_pinhole (i:ℕ)(x:A): pinhole A i x∈ shorter A i:= board (P:={f| Enough i f}) (enough_slot i x)
end Altitude
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.curve
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.pinhole_apply
