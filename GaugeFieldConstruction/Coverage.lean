import GaugeFieldConstruction.Perm4

/-!
# U1 raw spanning proof checker

Work over complex scalars in U1. This part doesn't test the on-shell jets;
negative stabilizer, flips of odd parity, etc. eliminate columns BEFORE that
test. Use unnormalised sum over ALL 24 permutations (scaling columns by their
positive-integer stabilizer sizes doesn't affect independence/spans).
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Certificate
open Function
open Raw Labels
variable {α β : Type*} (A : Labels α) (B : Labels β)
variable [DecidableEq α]

def ok (a : α) := axes.all (fun i => let g := Signed.mirror i; decide (A.move g a=a) && !A.cost g a) &&
  perm4.all (fun p => let g := unsigned p; !(decide (A.move g a=a) && A.cost g a))

def droppable (a : α) := axes.any (fun i => let g := Signed.mirror i; A.cost g a && decide (A.move g a=a)) ||
  perm4.any (fun p => let g := unsigned p; decide (A.move g a=a) && A.cost g a)

def different (xs : List α) := xs.all fun a =>
  perm4.all fun p => let b := A.move (unsigned p) a
                     decide (b=a) || !decide (b ∈ xs)

structure Picked (xs : List α) : Prop where
  nodup : xs.Nodup
  good : ∀ i∈xs, A.evenAt i ∧ A.coheres i
  diff : ∀ i∈xs, ∀ j∈xs, ∀ p, A.move (unsigned p) i=j → i=j
  pass : ∀ i, A.coveredBy xs i

theorem spanPicked [Fintype α] (xs : List α) (K : Type*) [Field K] [CharZero K]
    (h : Picked A xs) :
    A.fixed K = Submodule.span K (A.orbit K '' (xs.toFinset : Set α)) := by
  apply A.basis_criterion
  · simpa using h.good
  · simpa using h.diff
  simpa [coveredBy] using h.pass

lemma ok_def (a : α) (h : ok A a=true) : A.evenAt a ∧ A.coheres a := by
  simp only [ok, Bool.and_eq_true] at h
  constructor
  · intro i; have hr := List.all_eq_true.mp h.1 i (mem_axes i); simpa using hr
  intro i e; have hr := List.all_eq_true.mp h.2 i (mem_perm i); simpa [e] using hr

lemma droppable_def (a : α) (h : droppable A a=true) : ∃ g, A.move g a=a ∧ A.cost g a=true := by
  simp only [droppable, Bool.or_eq_true] at h; rcases h with u|u
  · obtain ⟨i,_,v⟩ := List.any_eq_true.mp u; exact ⟨Signed.mirror i,by simpa [and_comm] using v⟩
  obtain ⟨i,_,v⟩ := List.any_eq_true.mp u; exact ⟨unsigned i,by simpa using v⟩

variable [DecidableEq β]

/-- The test list covers output components up to permutations. -/
def Hits (xs : List β) := ∀ (j : β), ∃ i ∈ xs, ∃ p, B.move (unsigned p) i=j

def looks (o : β) (reps : List (α×β)) (l : List α) :=
  let candidates := reps.flatMap fun a => perm4.filterMap fun p =>
    if B.move (unsigned p) a.2=o then some (A.move (unsigned p) a.1) else none
  l.all fun a => droppable (A.tensorProd B) (a,o) || decide (a ∈ candidates)

lemma looks_paid (o : β) (reps : List (α×β)) (l : List α) (hl : looks A B o reps l=true) :
    ∀ a∈l, (A.tensorProd B).coveredBy reps (a,o) := by
  intro a h; have hh := List.all_eq_true.mp hl a h; rw [Bool.or_eq_true] at hh; rcases hh with u|u
  · exact Or.inl (droppable_def _ _ u)
  right
  obtain ⟨z,hz,hv⟩ := List.mem_flatMap.mp (of_decide_eq_true u)
  obtain ⟨p,_,v⟩ := List.mem_filterMap.mp hv
  split_ifs at v with ht
  · exact ⟨z,hz,p,Prod.ext (Option.some.inj v) ht⟩

def Approves (r : List (α × β)) (test : List β) (l : List α) : Bool :=
  let P := A.tensorProd B
  (decide r.Nodup && r.all (ok P)) && (different P r && test.all fun o => looks A B o r l)

theorem certify (r : List (α × β)) (test : List β) (l : List α) (hit : Hits B test)
    (m : ∀ a, a∈l) (h : Approves A B r test l=true) : Picked (A.tensorProd B) r := by
  simp only [Approves, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, fun a ha => ok_def _ _ (List.all_eq_true.mp h.1.2 a ha), ?_,
    A.cover_expand B r test hit (fun i hi a =>
      looks_paid _ _ i _ l (List.all_eq_true.mp h.2.2 i hi) a (m a))⟩
  intro a ha b hb p he
  have hv := List.all_eq_true.mp (List.all_eq_true.mp h.2.1 a ha) p (mem_perm p)
  dsimp only at hv; simpa [he,hb,eq_comm] using hv

-- Raw alphabet lists
abbrev S := ordered (α:=Axis)
def W (i j : Axis) (h : i<j := by decide) : Wed := Wed.mk i j h

def symElems := [S 0 0,S 0 1,S 0 2,S 0 3,S 1 1,S 1 2,S 1 3,S 2 2,S 2 3,S 3 3]
def wedElems := [W 0 1,W 0 2,W 0 3,W 1 2,W 1 3,W 2 3]

theorem mem_sym : ∀ i, i∈symElems := by decide
theorem mem_wed : ∀ i, i∈wedElems := by decide

def wTest : List Axis := [0]
def sTest := [S 0 0,S 0 1]
def vTest : List VS := [(0,S 0 0),(0,S 0 1),(0,S 1 1),(0,S 1 2)]
def vvTest : List (Axis × Axis) := [(0,0),(0,1)]
lemma of_hit (t : List β) (l : List β) (m : ∀ i, i∈l)
    (h : l.all (fun i => t.any fun j => perm4.any fun p => decide (B.move (unsigned p) j = i)) = true) : Hits B t := by
  intro i
  obtain ⟨j,hj,v⟩ := List.any_eq_true.mp (List.all_eq_true.mp h i (m i))
  obtain ⟨p,_,h⟩ := List.any_eq_true.mp v
  exact ⟨j,hj,p,of_decide_eq_true h⟩

def sprod (a : List α) (b : List β) := a.flatMap fun i => b.map fun j => (i,j)

omit [DecidableEq α] [DecidableEq β] in
lemma stock_prod (a : List α) (b : List β) (ha : ∀ i, i∈a) (hb : ∀ i, i∈b) (u : α×β) :
    u∈sprod a b := List.mem_flatMap.mpr ⟨u.1,ha _,List.mem_map.mpr ⟨u.2,hb _,rfl⟩⟩
lemma wTest_ok : Hits v wTest := of_hit v wTest axes mem_axes (by decide)
lemma sTest_ok : Hits symAct sTest := of_hit _ _ symElems mem_sym (by decide +kernel)
set_option maxRecDepth 100000 in
lemma vTest_ok : Hits vsAct vTest := of_hit _ _ _ (stock_prod _ _ mem_axes mem_sym) (by decide +kernel)
lemma vvTest_ok : Hits (v.tensorProd v) vvTest := of_hit _ _ _ (stock_prod _ _ mem_axes mem_axes)
  (by decide +kernel)

def g4Elems := ((sprod wedElems wedElems).map fun i => ordered i.1 i.2) -- repetitions harmless
lemma mem_g4 (a : G4) : a∈g4Elems := List.mem_map.mpr ⟨a.val, stock_prod _ _ mem_wed mem_wed _, ordered_same a⟩

def g5Elems := sprod wedElems (sprod wedElems axes)
lemma mem_g5 (a : G5) : a∈g5Elems := stock_prod _ _ mem_wed (stock_prod _ _ mem_wed mem_axes) _

def f3Elems := axes
lemma mem_f3 (i : F3) : i∈f3Elems := mem_axes i

def enumSum (a : List α) (b : List β) : List (α ⊕ β) := a.map Sum.inl ++ b.map Sum.inr
omit [DecidableEq α] [DecidableEq β] in
lemma stock_sum (a : List α) (b : List β) (ha : ∀ i, i∈a) (hb : ∀ i, i∈b) : ∀ i, i∈enumSum a b := by
  intro i; cases i <;> simp [enumSum,ha,hb]

def f4Elems := sprod axes (enumSum axes axes)
lemma mem_f4 (a : F4) : a∈f4Elems := stock_prod _ _ mem_axes (stock_sum _ _ mem_axes mem_axes) _

def f5Elems := sprod axes (enumSum symElems (enumSum symElems (sprod axes axes)))
lemma mem_f5 (a : F5) : a∈f5Elems := stock_prod _ _ mem_axes
  (stock_sum _ _ mem_sym (stock_sum _ _ mem_sym (stock_prod _ _ mem_axes mem_axes))) _

def x5Elems := sprod axes wedElems
lemma mem_x5 (a : X5) : a∈x5Elems := stock_prod _ _ mem_axes mem_wed _
end YM.GaugeFieldConstruction.Certificate
