import GaugeFieldConstruction.CauchyData
/-!
# Gaussian integer sparse calculator

Cheap certifying code: checks integer identities, β-δε reduction
in-kernel (no native_decide). It has no external data. Deals with Finsupp
coordinates of the on-shell jets; operations evaluate `J` actual elements.
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers
open Finset Function Complex Cauchy
open scoped BigOperators
variable {α β γ : Type*}

/-- Coefficient container, no division. -/
structure Credit where
  re : ℤ
  im : ℤ
  deriving DecidableEq, Inhabited
namespace Credit
instance : Zero Credit := ⟨⟨0,0⟩⟩
instance : One Credit := ⟨⟨1,0⟩⟩
def ii : Credit := ⟨0,1⟩
instance : Add Credit := ⟨fun x y => ⟨x.re+y.re,x.im+y.im⟩⟩
instance : Neg Credit := ⟨fun x => ⟨-x.re,-x.im⟩⟩
instance : Mul Credit := ⟨fun x y =>
  ⟨x.re*y.re-x.im*y.im,x.re*y.im+x.im*y.re⟩⟩

noncomputable def money (x : Credit) : ℂ := x.re + I*x.im
@[simp] lemma zero_c : money 0=0 := by
  simp only [money, show (0:Credit).re=0 from rfl,
    show (0:Credit).im=0 from rfl]
  simp
@[simp] lemma one_c : money 1=1 := by
  simp only [money, show (1:Credit).re=1 from rfl,
    show (1:Credit).im=0 from rfl]
  simp
@[simp] lemma imag : money ii=I := by simp [money,ii]
@[simp] lemma plus (x y : Credit) : (x+y).money=x.money+y.money := by
  change (↑(x.re+y.re):ℂ)+I* ↑(x.im+y.im) = _; simp only [money, Int.cast_add]; ring
@[simp] lemma opposite (x : Credit) : (-x).money= -x.money := by
  change (↑(-x.re):ℂ)+I* ↑(-x.im)= _; simp only [money, Int.cast_neg]; ring
@[simp] lemma times (x y : Credit) : (x*y).money=x.money*y.money := by
  change (↑(x.re*y.re-x.im*y.im):ℂ) + I* ↑(x.re*y.im+x.im*y.re) = _
  simp only [money, Int.cast_sub,Int.cast_mul,Int.cast_add]
  ring_nf; simp; ring
@[simp] lemma nonzero (x : Credit) : x.money ≠ 0 ↔ x ≠ 0 := by
  constructor
  · exact fun h t => h (by simp [t])
  intro h u
  have hr := congr_arg Complex.re u; have hs := congr_arg Complex.im u
  simp [money] at hr hs; rcases x with ⟨a,b⟩; exact h (by
    change a=0 at hr; change b=0 at hs; rw [hr,hs]; rfl)
end Credit
abbrev Bill (α : Type*) := List (α × Credit)
namespace Bill
noncomputable def total : Bill α → J α
  | [] => 0
  | (x,c)::l => c.money • ket x + total l
lemma total_append (x y : Bill α) : total (x++y)=total x+total y := by
  induction x with
  | nil => simp [total]
  | cons a x h => simp only [List.cons_append,total,h,add_assoc]

def join (l : List α) (f : α → Bill β) : Bill β := l.flatMap f
lemma take_join (l : List α) (f : α → Bill β) : total (join l f)=(l.map (total ∘ f)).sum := by
  induction l with
  | nil => rfl
  | cons i l h=>
    rw [show join (i::l) f=f i++join l f from rfl,total_append,h]; rfl

def spend (c : Credit) (l : Bill α) : Bill α := if c=0 then [] else l.map fun p => (p.1,c*p.2)
lemma cost (c : Credit) (l : Bill α) : total (spend c l)=c.money • total l := by
  by_cases e : c=0
  · simp [e,spend,total]
  induction l with
  | nil => simp [spend,total,e]
  | cons b q h=> simp [spend,e,total, smul_add,smul_smul] at *; exact h

def flash (i : α) (c : Credit := 1) : Bill α := if c=0 then [] else [(i,c)]
lemma take_flash (i : α) (c : Credit) : total (flash i c)=c.money • ket i := by
  by_cases e : c=0 <;> simp [flash,e,total]
lemma take_one (i : α) : total (flash i)=ket i := by rw [take_flash,Credit.one_c,one_smul]

def prep (B : Bill α) (f : α → Bill β) := join B (fun p=> spend p.2 (f p.1))
lemma earn (B : Bill α) (f : α → Bill β) (z : J α →ₗ[ℂ] J β) (h : ∀ i,total (f i)=z (ket i)) :
    total (prep B f)=z (total B) := by
  induction B with
  | nil => simp [prep,join,total]
  | cons i B he=> rw [show prep (i::B) f=spend i.2 (f i.1) ++ prep B f from rfl,
      total_append,total, map_add, he,cost,h,map_smul]
end Bill

/-! Use standard complex linear meaning of Scan. -/
section Scan
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Exact greedy span test, pays each Bool as true iff its column increases
rank; begins Scan0 at the empty span. -/
def scan : List V → List Bool → Submodule ℂ V → Prop
  | [],[],_ => True
  | x::t,true::q,H => x ∉ H ∧ scan t q (H⊔Submodule.span ℂ {x})
  | x::t,false::q,H => x ∈ H ∧ scan t q (H⊔Submodule.span ℂ {x})
  | _,_,_ => False
def Scan0 (l : List V) (b : List Bool) := scan l b ⊥

open Submodule
/-- Transform through any linear map faithful on the indicated subspace. -/
theorem carry {x : List V} (p : V →ₗ[ℂ] W) (H : Submodule ℂ V)
    (h : ∀ u∈H,p u=0→u=0) (c : ∀ u∈x,u∈H) (t : Submodule ℂ V) (ht : t≤H) (b) (w : scan (x.map p) b (map p t)) :
    scan x b t := by
  induction x generalizing t b with
  | nil => cases b <;> exact w
  | cons y x ih=>
    have hy : y∈H := c _ (by simp)
    have hv : p y ∈ map p t ↔ y∈t := by
      constructor
      · rintro ⟨z,hz,e⟩
        have hv := h (z-y) (H.sub_mem (ht hz) hy) (by rw [map_sub,e,sub_self])
        rwa [← sub_eq_zero.mp hv]
      exact fun h=> ⟨_,h,rfl⟩
    have hp : t⊔span ℂ {y} ≤ H := sup_le ht ((span_singleton_le_iff_mem ..).mpr hy)
    have hu : map p (t ⊔ span ℂ {y})=map p t ⊔ span ℂ {p y} := by rw [Submodule.map_sup,map_span]; simp
    match b with
    | [] => exact False.elim w
    | true::a =>
      exact ⟨mt hv.mpr w.1, ih (fun x hx=>c _ (List.mem_cons_of_mem _ hx)) _ hp a (hu.symm ▸ w.2)⟩
    | false::a =>
      exact ⟨hv.mp w.1, ih (fun x hx=>c _ (List.mem_cons_of_mem _ hx)) _ hp a (hu.symm ▸ w.2)⟩

/-- Walk used in proof checker; doesn't apply a noncomputable predicate on
modules as a decision procedure. -/
def pick : List Bool → List α → List α
  | b::B,x::X => if b then x:: pick B X else pick B X
  | _,_ => []
def line (u : List V) := span ℂ {x|x∈u}
lemma accumulated (u : List V) (b : List Bool) (H : Submodule ℂ V) (h : scan u b H) :
    H⊔line u=H⊔line (pick b u) := by
  have he (l : List V) (x : V) : line (x::l)=span ℂ {x}⊔line l := by
    rw [line,line,← span_union]; congr; ext p; simp; change _ ↔ p ∈ insert x (_:Set V); simp
  induction u generalizing b H with
  | nil => cases b <;> rfl
  | cons x u ih =>
    match b with
    | [] => exact False.elim h
    | true::B => rw [show pick ..=x ::pick B u from rfl,he,← sup_assoc, ih B _ h.2, he]; exact sup_assoc ..
    | false::B =>
      have hg := sup_eq_left.mpr ((span_singleton_le_iff_mem ..).mpr h.1)
      rw [he, ← sup_assoc, ih B _ h.2,hg]; rfl
end Scan
end YM.GaugeFieldConstruction.Vouchers
