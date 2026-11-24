import GaugeFieldConstruction.TestsPay
import GaugeFieldConstruction.Coverage


/-!
# Invariant tensors on Record rows, paid on their full wave tests
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Finset Matrix Set
open scoped BigOperators Matrix
namespace Cauchy.Row.Record
open Raw
variable {X Z α β η : Type*} (R : Record X Z) (A : Labels α) (B : Labels β)

/-- Equivariant price on the shell jets, all components. -/
def tensors : Submodule ℂ (β → J X) where
  carrier := {q|∀ s w u (h : R.poses s w u) i, R.tester u (q i)=pay (B.cost s i) (R.tester w (q (B.move s i)))}
  add_mem' {a b} ha hb := by
    intro s w u h i; simp only [Pi.add_apply, map_add, ha s w u h i,hb s w u h i,pay_add]
  smul_mem' c a ha := by
    intro s w u h i; simp only [Pi.smul_apply,map_smul,ha s w u h i]; cases B.cost s i <;> simp
  zero_mem' := by intro s w u h i; simp

lemma tensor_eq (a : β → J X) : a∈R.tensors B ↔ ∀ s w u (h : R.poses s w u) i,
    R.tester u (a i)=pay (B.cost s i) (R.tester w (a (B.move s i))) := Iff.rfl
variable {R B}
lemma fare {a : β → J X} (h : a∈R.tensors B) {s : Signed} {w u : Z} (hp : R.poses s w u) (i : β) :
    R.tester u (a i)=pay (B.cost s i) (R.tester w (a (B.move s i))) := (R.tensor_eq B _).mp h _ _ _ hp _

variable (R B)
/-- Restrict to O-component representatives for equality checking. -/
def part (l : List β) : (β → J X) →ₗ[ℂ] Fin l.length → J X :=
  LinearMap.pi fun i => LinearMap.proj (l.get i)
theorem part_faith (l : List β) (h : Certificate.Hits B l)
    (t : β → J X) (p : t∈R.tensors B) (e : part l t=0) : t=0 := by
  funext i; obtain ⟨j,hj,k,rfl⟩ := h i; obtain ⟨s,hs⟩ := List.mem_iff_get.mp hj
  have hv := congr_fun e s; change t (l.get s)=0 at hv; rw [hs] at hv
  refine R.faith _ fun i => ?_
  obtain ⟨u,w⟩ := R.permit (unsigned k) i
  have he := fare p w j; rw [hv,map_zero] at he
  rw [LinearMap.mem_ker]
  simpa using congr_arg (pay (B.cost (unsigned k) j)) he.symm

lemma part_eq (l : List β) (h : Certificate.Hits B l) (t s) (p : t∈R.tensors B) (q : s∈R.tensors B)
    (e : part l t=part l s) : t=s := sub_eq_zero.mp
  (R.part_faith B l h _ ((R.tensors B).sub_mem p q) (by rw [map_sub,e,sub_self]))

/-- Components have to be from the symbol space of the grade and type. -/
def allowed (U : Submodule ℂ (J X)) : Submodule ℂ (β → J X) := R.tensors B ⊓ Submodule.pi Set.univ (fun _=>U)

section Finite
variable [Fintype α] (q : α → J X)

def space : Submodule ℂ (J X) := LinearMap.range (Fintype.linearCombination ℂ q)
def dot : ((α × β) → ℂ) →ₗ[ℂ] β → J X := LinearMap.pi fun i : β =>
  Fintype.linearCombination ℂ q ∘ₗ LinearMap.pi (fun a : α => LinearMap.proj (a,i))

lemma dot_apply (t : α × β → ℂ) (i : β) : dot q t i = ∑ a, t (a,i) • q a := rfl
lemma value_single [DecidableEq α] [DecidableEq β] (c : ℂ) (i : α) (j : β) :
    dot q (Pi.single (i,j) c) = Pi.single j (c • q i) := by
  ext1 k
  by_cases e : k=j
  · subst k; rw [dot_apply,sum_eq_single i]; swap; intro b _ h; simp [Pi.single_apply,h]
    all_goals simp
  rw [dot_apply,sum_eq_zero, Pi.single_eq_of_ne e]
  intro b _; simp [Pi.single_apply,e]

variable {A R q} (h : R.Reading A q)
include h
private lemma transported {s w u} (hp : R.poses s w u) (t : α×β → ℂ) (i : β) :
    R.tester u (dot q t i) = pay (B.cost s i)
      (R.tester w (dot q ((A.tensorProd B).transport ℂ s t) (B.move s i))) := by
  rw [dot_apply,dot_apply,map_sum,map_sum]
  conv_rhs => rw [← Equiv.sum_comp (A.equivMove s)]
  rw [show ∀ (f : α → ℂ), pay (B.cost s i) (∑ a, f a) = ∑ a, pay (B.cost s i) (f a) from
    fun x => by cases B.cost s i <;> simp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_smul]
  change t _ * R.tester u _=pay _ (((A.tensorProd B).transport ℂ s t ((A.tensorProd B).move s (a,i))) *
    R.tester w (q (A.move s a)))
  rw [Labels.transport_value, h.moving s w u hp]
  change _ = pay _ (pay ((A.cost s a).xor (B.cost s i)) (t (a,i))*_)
  cases A.cost s a <;> cases B.cost s i <;> simp

/-- Lift equivariance through the shell quotient (finite average). -/
theorem paid_span : R.allowed B (space q) =
    Submodule.map (dot q) ((A.tensorProd B).fixed ℂ) := by
  refine le_antisymm ?_ ?_
  · rintro t ⟨p,r⟩
    have he (i : β) : t i ∈ space q := r i (Set.mem_univ i)
    choose y hy using he -- tweak Membership
    let Y := fun a : α×β => y a.2 a.1
    have hv : dot q Y=t := funext fun i => by exact hy i
    have hw (g) : dot q ((A.tensorProd B).transport ℂ g Y)=t := by
      ext1 j
      obtain ⟨i,rfl⟩ := (B.equivMove g).surjective j
      change dot q ((A.tensorProd B).transport ℂ g Y) (B.move g i) = t (B.move g i)
      apply ext_jet R.faith; intro w
      obtain ⟨u,H⟩ := R.permit g w
      have hr := transported B h H Y i
      rw [hv, fare p H] at hr
      exact (by simpa using congr_arg (pay (B.cost g i)) hr.symm)
    let Z' := ∑ g : Signed, (A.tensorProd B).transport ℂ g Y
    have hq : Z' ∈ (A.tensorProd B).fixed ℂ := by
      apply ((A.tensorProd B).fixe_iff _).mpr
      intro g; dsimp only [Z']; rw [map_sum]
      have ht (s) : (A.tensorProd B).transport ℂ g ((A.tensorProd B).transport ℂ s Y) =
          (A.tensorProd B).transport ℂ (g*s) Y := by rw [← Labels.group]; rfl
      simp_rw [ht]
      exact Equiv.sum_comp (Equiv.mulLeft g) (fun k => (A.tensorProd B).transport ℂ k Y)
    refine ⟨(Fintype.card Signed : ℂ)⁻¹ • Z', Submodule.smul_mem _ _ hq, ?_⟩
    rw [map_smul]; unfold Z'; rw [map_sum]; simp_rw [hw]; rw [Finset.sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℂ]
    simp [inv_smul_smul₀ (show (Fintype.card Signed : ℂ)≠0 from by exact_mod_cast Fintype.card_pos.ne')]
  rintro _ ⟨t,ht,rfl⟩
  refine ⟨(tensor_eq ..).mpr ?_, fun i _=> (?_ : dot _ _ i∈space q)⟩
  · intro s w u h' i
    have he := transported B h h' t i; rwa [(Labels.fixe_iff _ _).mp ht s] at he
  exact ⟨fun a => t (a,i),rfl⟩

def column [DecidableEq α] [DecidableEq β] (A : Labels α) (q : α → J X)
    (i : α×β) := dot q ((A.tensorProd B).orbit ℂ i) -- h included?

variable [DecidableEq α] [DecidableEq β]
lemma span_columns [Fintype β] (xs : List (α×β)) (p : Certificate.Picked (A.tensorProd B) xs) :
    R.allowed B (space q) = Submodule.span ℂ ((column B A q) '' (xs.toFinset : Set (α × β))) := by
  classical
  rw [paid_span B h, Certificate.spanPicked _ _ _ p, Submodule.map_span]
  -- needs Fintype β
  rw [Set.image_image]; rfl
end Finite
section Flux
open Raw
/-- Tensor of first derivatives. -/
def heatP (β : Type*) : (β → J X) →ₗ[ℂ] ((Axis × β) → J X) := LinearMap.pi
  fun k => R.P k.1 ∘ₗ LinearMap.proj k.2
lemma chargeP (t : β → J X) (p : t∈R.tensors B) : R.heatP β t ∈ R.tensors (Raw.v.tensorProd B) := by
  intro s w u h k
  have hr := R.atP k.1 (t k.2) (t (B.move s k.2)) s w u h (B.cost s k.2) (fare p h k.2)
  rw [Bool.xor_comm] at hr
  exact hr

/-- Divergence. -/
def divP : (Raw.Sym → J X) →ₗ[ℂ] Axis → J X := LinearMap.pi fun j =>
  ∑ i : Axis, R.P i ∘ₗ LinearMap.proj (ordered i j)
@[simp] lemma divT (a : Raw.Sym → J X) (j) : R.divP a j = ∑ i : Axis, R.P i (a (ordered i j)) := by
  change (∑ i : Axis, R.P i ∘ₗ _) a = _
  rw [LinearMap.sum_apply]; rfl

def divA : (VS → J X) →ₗ[ℂ] Axis × Axis → J X := LinearMap.pi fun j =>
  ∑ i : Axis, R.P i ∘ₗ LinearMap.proj (j.1,ordered i j.2)
@[simp] lemma divV (a : VS → J X) (k j : Axis) : R.divA a (k,j) = ∑ i, R.P i (a (k,ordered i j)) := by
  change (∑ i : Axis, R.P i ∘ₗ _) a = _
  rw [LinearMap.sum_apply]; rfl
lemma sym_turn (s : Signed) (i j : Axis) : symAct.move s (ordered i j)=ordered (s.perm i) (s.perm j) := by
  rw [ordered]; split_ifs
  · exact ordered_swap ..
  rfl
lemma fee_turn (s : Signed) (i j : Axis) : symAct.cost s (ordered i j)=(s.flip i).xor (s.flip j) := by
  rw [ordered]; split_ifs
  · exact Bool.xor_comm ..
  rfl
lemma feePay {M : Type*} [AddCommGroup M] {T : Type*} [Fintype T] (a : T → M) (s : Bool) :
    pay s (∑ i:T,a i)=∑ i:T,pay s (a i) := by cases s <;> simp

lemma paid_div (a : Raw.Sym → J X) (p : a∈R.tensors symAct) : R.divP a∈R.tensors Raw.v := by
  intro s w u h i
  rw [divT,divT,map_sum,map_sum,feePay]
  conv_rhs => rw [← Equiv.sum_comp s.perm]
  apply Finset.sum_congr rfl
  intro j _
  have he := R.atP j _ _ s w u h _ (fare p h (ordered j i))
  rw [fee_turn,sym_turn] at he
  change _ = pay (s.flip i) _; rw [he]
  cases s.flip i <;> cases s.flip j <;> rfl

lemma paid_A (a : VS → J X) (p : a∈R.tensors vsAct) : R.divA a∈R.tensors (Raw.v.tensorProd Raw.v) := by
  rintro s w u h ⟨k,i⟩
  change R.tester u _=pay ((s.flip k).xor (s.flip i)) (R.tester w (R.divA a (s.perm k,s.perm i)))
  rw [divV,divV,map_sum,map_sum,feePay]
  conv_rhs => rw [← Equiv.sum_comp s.perm]
  apply Finset.sum_congr rfl
  intro j _
  have he := R.atP j _ _ s w u h _ (fare p h (k,ordered j i))
  change _ = pay (((s.flip k).xor (symAct.cost s (ordered j i))).xor (s.flip j))
    (R.tester w _ ) at he; rw [fee_turn] at he
  change R.tester u _=pay _ (R.tester w (R.P (s.perm j) (a (s.perm k,ordered (s.perm j) (s.perm i)))))
  rw [he]; unfold vsAct Raw.v Labels.tensorProd
  simp only; rw [sym_turn]; cases s.flip k <;> cases s.flip j <;> cases s.flip i <;> rfl

def trace : (Raw.Sym → J X) →ₗ[ℂ] Unit → J X := LinearMap.pi fun _ => ∑ i : Axis, LinearMap.proj (ordered i i)
@[simp] lemma trace_value (x : Raw.Sym → J X) (u : Unit) : trace x u= ∑ i : Axis,x (ordered i i) := by
  change (∑ i : Axis,(LinearMap.proj (ordered i i) : (Raw.Sym → J X) →ₗ[ℂ] J X)) x=_
  rw [LinearMap.sum_apply]; rfl
lemma paid_trace (a : Raw.Sym → J X) (p : a∈R.tensors symAct) :
    trace a ∈ R.tensors (Labels.unitL Unit) := by
  intro s w u h i
  rw [trace_value,map_sum,map_sum]; conv_rhs => rw [← Equiv.sum_comp s.perm]
  rw [show (Labels.unitL Unit).cost s i=false from rfl,pay_false]
  apply Finset.sum_congr rfl
  intro b _; rw [fare p h, sym_turn,fee_turn, Bool.xor_self,pay_false]
end Flux
end Cauchy.Row.Record
end YM.GaugeFieldConstruction
