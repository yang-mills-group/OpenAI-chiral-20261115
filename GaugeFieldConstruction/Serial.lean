import GaugeFieldConstruction.Camera
import GaugeFieldConstruction.TensorTax
/-!
# Criterion for establishing scan on the column outputs
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers.Camera
open Finset Function Cauchy Row Raw Bill Record Certificate
open scoped BigOperators
variable {α β γ X Z : Type*} (R : Record X Z)

noncomputable def ia (a : α) : J X →ₗ[ℂ] J (α× X) := times' (ket a)
noncomputable def bundle (l : List α) : (α → J X) →ₗ[ℂ] J (α × X) :=
    (l.map fun i => ia i ∘ₗ LinearMap.proj i).sum

variable [DecidableEq α]
include R
lemma assigns (q : List α) (h : q.Nodup) (x : α → J X) (i : α) (hi : i∈q) :
    another (Finsupp.lapply i) (bundle q x)=x i := by
  have hs (i j : α) : another (β:=X) (Finsupp.lapply i) ∘ₗ ia j = -- tweak
      if j=i then LinearMap.id else 0 := by
    apply ket_ext; intro a
    rw [LinearMap.comp_apply]; change another _ (times' (ket j) (ket a)) = _; rw [takes,another,on_ket]
    by_cases e : j=i
    · subst i; rw [if_pos rfl]; simp [ket]
    rw [if_neg e]; simp [ket,e,Finsupp.single_apply]
  have he : bundle (X:=X) q = ∑ i ∈ q.toFinset, ia i ∘ₗ LinearMap.proj i := by
    rw [List.sum_toFinset _ h]; rfl
  rw [he,LinearMap.sum_apply,map_sum]
  rw [Finset.sum_eq_single_of_mem i (List.mem_toFinset.mpr hi)]
  · rw [LinearMap.comp_apply,← LinearMap.comp_apply (another _), hs, if_pos rfl]; rfl
  intro b _ hb; rw [LinearMap.comp_apply,← LinearMap.comp_apply (another _), hs,if_neg hb]; rfl

variable (A : Labels α)
theorem sends (q : List α) (d : q.Nodup) (h : Hits A q) (u : List (α → J X))
    (H : ∀ x∈u,x∈R.tensors A) (b : List Bool) (p : Scan0 (u.map (bundle q)) b) : Scan0 u b := by
  refine carry (bundle q) (R.tensors A) ?_ H _ bot_le b (by rw [Submodule.map_bot]; exact p)
  intro x hx he
  apply part_faith R A q h _ hx
  ext1 i
  have hi := assigns R q d x _ (List.get_mem q i)
  rw [he,map_zero] at hi; exact hi.symm

variable [DecidableEq β] (B : Labels β)

def bundleCost (q : List α) (w : α → Bill X) : Bill (α× X) := Bill.join q fun i => cart (flash i) (w i)

omit R [DecidableEq α] in
lemma bundleAt (q : List α) (w : α → Bill X) (x : α → J X) (h : ∀ i,total (w i)=x i) :
    total (bundleCost q w)=bundle q x := by
  induction q with
  | nil => simp [bundleCost,Bill.join,total,bundle]
  | cons i q he=> rw [show bundleCost .. = _ from show bundleCost (i::q) w=cart (flash i) (w i)++bundleCost q w from rfl,
                         total_append,he,give,take_one,h]; rfl

section
variable [DecidableEq X]
/-- Column sum over the 24 permutations. Keep specified component. Before pivot test.
This uses *non-normalized* columns. -/
def inspect (payroll : α → Bill X) (o : α×β) (i : β) := Bill.norm (α:=X)
  (Bill.join perm4 fun p =>
    let s:=unsigned p; let pt:=(A.tensorProd B).move s o
    if pt.2=i then spend (pay ((A.tensorProd B).cost s o) 1) (payroll pt.1) else [])
-- norm needs DecEq X

omit R in
lemma inspect_c [Fintype α] (payroll : α → Bill X) (p : α → J X) (hp : ∀ i,total (payroll i)=p i)
    (o : α × β) (i : β) : total (inspect A B payroll o i)=column B A p o i := by
  rw [inspect,Bill.same, take_join, sum_perm]
  simp only [Record.column, Labels.orbit, map_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [comp_apply,Labels.one_impulse] -- tune
  let t := (A.tensorProd B).move (unsigned b) o
  rw [show (A.tensorProd B).move (unsigned b) o=(t.1,t.2) from rfl, value_single]
  by_cases h:t.2=i
  · subst i; simp only [↓reduceIte,Pi.single_eq_same]
    change total (spend _ _)= _
    rw [cost,hp]; cases (A.tensorProd B).cost (unsigned b) o <;> simp
  change total (if t.2=i then _ else _)=_
  rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]; rfl
end

def axisList : List Axis := [0,1,2,3]
def dimTest (d : Axis → Bill X → Bill X) (x : Raw.Sym → Bill X) (i : Axis) :=
  Bill.join axisList fun j => d j (x (S j i))
def vecTest (d : Axis → Bill X → Bill X) (x : VS → Bill X) (i : Axis × Axis) :=
  Bill.join axisList fun j => d j (x (i.1,S j i.2))
def gradTest (d : Axis → Bill X → Bill X) (x : Axis → Bill X) (i : Axis × Axis) := d i.1 (x i.2)
def trTest (x : Raw.Sym → Bill X) (_ : Unit) := Bill.join axisList fun j => x (S j j)

omit R in
private lemma take_ax (p : Axis → Bill X) : total (Bill.join axisList p)=∑ i : Axis,total (p i) := by
  rw [take_join]
  simp [axisList, Fin.sum_univ_succ]

variable (d : Axis → Bill X → Bill X) (fee : ∀ k i,total (d k i)=R.P k (total i))
include fee
lemma dim_cost (x : Raw.Sym → Bill X) (y : Raw.Sym → J X) (h : ∀ i,total (x i)=y i) (j : Axis) :
    total (dimTest d x j) = R.divP y j := by rw [dimTest,take_ax,divT]; simp only [fee,h]
lemma vec_cost (x : VS → Bill X) (y : VS → J X) (h : ∀ i,total (x i)=y i) (j : Axis × Axis) :
    total (vecTest d x j) = R.divA y j := by
  cases j; rw [vecTest,take_ax,divV]; simp only [fee,h]
lemma grad_cost (x : Axis → Bill X) (y : Axis → J X) (h : ∀ i,total (x i)=y i) (j : Axis × Axis) :
    total (gradTest d x j) = R.heatP Axis y j := by rw [gradTest,fee,h]; rfl
omit R fee in
lemma tr_cost (x : Raw.Sym → Bill X) (y : Raw.Sym → J X) (h : ∀ i,total (x i)=y i) (j : Unit) :
    total (trTest x j) = trace y j := by rw [trTest,take_ax,trace_value]; simp only [h]
end YM.GaugeFieldConstruction.Vouchers.Camera
