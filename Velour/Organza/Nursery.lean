import Velour.Organza.Frond
/-! Cyclic piece of a field election. No guesses about cyclicity in
a larger/antecedent space. Compact test words are graph-dense there.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL

local notation "U" => S.unit.translation
local notation "M" => S.liftL


variable {κ:Type}

def sprout (T:κ→S.Detector)(v:D): Submodule ℂ D where
 carrier:= {x |∃ A∈S.grove T {f| LocalTest f}, A v=x}
 zero_mem':= ⟨_, (S.grove T _).zero_mem,rfl⟩
 add_mem':=by rintro x y ⟨A,a',rfl⟩ ⟨F,e,rfl⟩; exact ⟨_,add_mem a' e,rfl⟩
 smul_mem':=by rintro c x ⟨A,a',rfl⟩; exact ⟨_,(S.grove T _).smul_mem a' c,rfl⟩  -- order?

def nursery (T:κ→S.Detector)(v:D): Submodule ℂ H.space:= S.district (S.sprout T v)
lemma at_bud (T:κ→S.Detector)(v:D) : v ∈ S.sprout T v:= ⟨1,one_mem _,rfl⟩

variable {S}
variable {J:κ→ℝ≥0→H.Op} {T:κ→S.Detector} {v:S.muslin}

lemma pruned (i:κ){f:Test4}(p:LocalTest f)(x:D)(e:x∈S.sprout T v):
   T i f x ∈S.sprout T v:=by
  obtain ⟨A,g,rfl⟩:=e
  exact ⟨_, (S.grove T _).mul_mem (grove_seed i (by exact p)) g,rfl⟩


lemma Fray.wiggle (h:S.Fray J T)(k:∀b, U b v.val=v.val):S.Mobile (S.sprout T v):= by
 rintro b x ⟨A,e,rfl⟩
 refine ⟨_, h.covary b (Q:={f|LocalTest f})
     (fun _ y=> LocalTest.ahead y _) e,?_⟩
 have p:M (-b) v=v:=Subtype.ext (k _)
 change M b (A (M (-b) v))=_; rw [p]

lemma nursery_closed : IsClosed (S.nursery T v:Set H.space):=Submodule.isClosed_topologicalClosure _
lemma reflected (x:D)(p:x∈S.sprout T v):x.val∈S.nursery T v:=
 (Submodule.le_topologicalClosure _) ⟨x,p,rfl⟩

lemma Fray.pruned_keep (h:S.Fray J T)(k:∀b, U b v.val=v.val)(i:κ):
  Keeps (S.nursery T v) (T i) ∧ Kept (S.nursery T v) (J i):=
  (h.wiggle k).host (h.1 i) (fun _ p=>pruned i p)

lemma firm_ruffs {X:Module.End ℂ S.muslin}(f:S.Firm X){x:D}{u:ℕ→D}
 (r:S.Ruffles atTop u x): S.Ruffles atTop (fun i=>X (u i)) (X x):= by
   obtain ⟨m,g⟩:=f
   exact r.reach _ (fun i=>⟨_,g i⟩)


lemma grove_keep {N:Submodule ℂ H.space}{P:Set Test4}{X:Module.End ℂ S.muslin}
 (h:∀i:κ,Keeps N (T i))
 (p:X∈S.grove T P):
 ∀x:D,x.val∈N→(X x).val∈N:=by
 refine Algebra.adjoin_induction (p:=fun K _=>∀x:D,x.val∈N→ (K x).val∈N)
    (fun _ y=>?_ )
    (fun c x e=> N.smul_mem c e)
    (fun _ _ _ _ a b x e=> N.add_mem (a x e) (b x e))
    (fun _ _ _ _ a b x e=> a _ (b _ e)) p
 obtain ⟨i,f,_,rfl⟩:=y
 exact h i f

lemma Fray.world (h:S.Fray J T){N:Submodule ℂ H.space}
 (g:IsClosed (N:Set H.space))(c:S.Car N)(u:v.val∈N)
 (b:∀i,Kept N (J i)): S.nursery T v ≤ N:= by
    refine show (S.district (S.sprout T v):Set H.space) ⊆ N from closure_minimal ?_ g
    rintro _ ⟨x,⟨A,e,rfl⟩,rfl⟩
    exact grove_keep (fun i=>(h.1 i).keeps g c (b i)) e _ u


theorem Fray.determines (h:S.Fray J T)(k:∀b, U b v.val=v.val)(i j:κ)
  (e:∀f,LocalTest f → ∀u∈S.sprout T v, ∀w∈S.sprout T v,
    inner ℂ w.val (T i f u).val= inner ℂ w.val (T j f u).val)
  {d:ℝ≥0}(p:0<d): EqOn ⇑(J i d) (J j d) (S.nursery T v:Set H.space):= by
  have y:=h.wiggle k
  refine (h.1 i).sufficient (h.1 j) nursery_closed y.car ?_ p
  intro f a₀ u b
  obtain ⟨x,g,t⟩:=y.core b
  have q(z):T i f (x z) = T j f (x z):= by
    rw [← sub_eq_zero]
    apply Subtype.ext
    change (T i f _).val-(T j f _).val=0
    let w:= T i f (x z)- T j f (x z)
    refine @inner_self_eq_zero ℂ H.space _ _ _ w.val |>.mp ?_
    have a:=e f a₀ (x z) (g z) w
      ((S.sprout T v).sub_mem (pruned i a₀ _ (g z)) (pruned j a₀ _ (g z)))
    conv_lhs=> rhs; change (T i f (x z)).val-(T j f (x z)).val
    rw [inner_sub_right,a,sub_self]


  apply Subtype.ext
  have j' z:= (firm_ruffs ((h.1 z).touch.gives f) t).plain
  exact tendsto_nhds_unique ((j' i).congr fun z=>congrArg _ (q z)) (j' j)

#print axioms Fray.determines
#print axioms Fray.world
#print axioms Fray.pruned_keep

