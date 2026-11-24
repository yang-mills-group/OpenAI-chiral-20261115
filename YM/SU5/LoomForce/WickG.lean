import YM.SU5.Thin.Avalanche.Shelter

/-! Sparse Gaussian prices. The pair tables will be asked to converge only on
DISTINCT entries of our roster -- no price limit at a same-site curvature variance is
necessary. Need Wick equivalence with the real finite sector of the actual
preparation, including its sign and normalization. Use `Resonance.gramStein`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
namespace WickG
open Function Filter Metric MeasureTheory ProbabilityTheory NormedSpace InnerProductSpace Finset
open Regis.Resonance
open scoped Topology BigOperators InnerProductSpace ENNReal NNReal Classical List
variable {I J : Type*}

/-- fuel argument to make recursion on shuffles unambiguous. Never stop at a nonempty
word in quoting an actual Wick price. -/
def pick (u : I) (c : I → I → ℂ) (f : List I → ℂ) (P : List I) : List I → ℂ
  | [] => 0
  | i::L => c u i * f (P ++ L) + pick u c f (P ++ [i]) L

def peek (c : I → I → ℂ) : ℕ → List I → ℂ
  | 0, [] => 1
  | 0, (_ :: _) => 0
  | _+1, [] => 1
  | k+1, x::L => pick x c (peek c k) [] L

def read (c : I → I → ℂ) (P : List I) : ℂ := peek c P.length P

lemma pick_congr' (x : I) (c d : I → I → ℂ) (f f' : List I → ℂ) (V P : List I)
    (p : ∀ i ∈ P, c x i = d x i) (q : ∀ (W : List I), W <+ V ++ P →
      W.length + 1 = V.length + P.length → f W = f' W) :
    pick x c f V P = pick x d f' V P := by
  induction P generalizing V with
  | nil => rfl
  | cons i P ih =>
    refine congrArg₂ (· + ·) (congrArg₂ (· * ·) (p _ List.mem_cons_self) (q (V++P) ?_ ?_))
      (ih (V++[i]) (fun j t=>p _ (List.mem_cons_of_mem _ t)) ?_)
    · apply List.Sublist.append (List.Sublist.refl V) ((List.Sublist.refl P).cons i)
    · simp [Nat.add_assoc]
    intro W h e; apply q W (by simpa using h); simpa [Nat.add_right_comm V.length 1 P.length,Nat.add_assoc,Nat.add_comm 1 P.length] using e

lemma fuel_once (c : I → I → ℂ) (P : List I) (b : ℕ) (p : P.length ≤ b) : peek c (b+1) P=peek c b P := by
  induction b generalizing P with
  | zero =>
    obtain rfl : P=[]:= by simpa using p
    rfl
  | succ b ih =>
    cases P with
    | nil=>rfl
    | cons x P=>
      apply pick_congr' x c c (peek c (b+1)) (peek c b) [] P (fun _ _=>rfl)
      intro R _ t; apply ih; simp at p t; omega

lemma fuel (c : I → I → ℂ) (P : List I) (b : ℕ) (p : P.length ≤ b) : peek c b P=read c P := by
  induction b,p using Nat.le_induction with
  | base=>rfl
  | succ b t ih=>rw [fuel_once c P b t]; exact ih

@[simp] lemma read_nil (c : I → I → ℂ) : read c [] = 1 := rfl
lemma read_more (c : I → I → ℂ) (x : I) (P : List I) : read c (x::P)=pick x c (read c) [] P := by
  change pick x c _ [] P = _
  apply pick_congr' _ _ _ _ _ _ _ (fun _ _=> rfl)
  intro W h _; apply fuel; simpa using h.length_le

lemma peek_congr (b : ℕ) (c d : I → I → ℂ) (P : List I)
    (p : P.Pairwise (fun i j=> c i j=d i j)) : peek c b P=peek d b P := by
  induction b generalizing P with
  | zero=>cases P <;> rfl
  | succ b ih=>
    cases P with
    | nil=> rfl
    | cons i P=>
      apply pick_congr' _ _ _ _ _ _ _ (List.pairwise_cons.mp p).1
      exact fun W h _=>ih W ((List.pairwise_cons.mp p).2.sublist (by simpa using h))

lemma pick_map (c : J → J → ℂ) (u : I) (g : I → J) (V P : List I) (w : List J → ℂ) :
    pick (g u) c w (V.map g) (P.map g) =
    pick u (fun i j=> c (g i) (g j)) (fun W => w (W.map g)) V P := by
  induction P generalizing V with
  | nil => rfl
  | cons i P ih=>
    simp only [List.map_cons,pick, List.map_append]
    congr 1
    simpa using ih (V++[i])

lemma peek_map (b : ℕ) (c : J → J → ℂ) (P : List I) (g : I → J) :
    peek c b (P.map g)=peek (fun i j=> c (g i) (g j)) b P := by
  induction b generalizing P with
  | zero=>cases P <;> rfl
  | succ b ih=>
    cases P with
    | nil=>rfl
    | cons i P=>
      rw [List.map_cons,peek]; have he:=pick_map c i g [] P (peek c b)
      rw [List.map_nil] at he; rw [he]; simp_rw [ih]; rfl

lemma read_map (c : J → J → ℂ) (P : List I) (g : I → J) :
    read c (P.map g)=read (fun i j=> c (g i) (g j)) P := by rw [read,List.length_map,peek_map]; rfl

-- product clustering limit across a genuine R-space gap in a proof like IA.9
lemma insulated (c : I → I → ℂ) (A B : List I) (p : ∀ i∈A,∀ j∈B,c i j=0) :
    read c (A++B)=read c A*read c B := by
  suffices h : ∀ (n : ℕ) (L : List I) (_ : L <+ A) (_ : L.length ≤ n), read c (L++B)=read c L * read c B from
    h A.length A (.refl _) (le_refl _)
  intro n
  induction n with
  | zero=> intro W _ t; simp only [nonpos_iff_eq_zero,List.length_eq_zero_iff] at t; rw [t]; simp
  | succ n ih =>
    intro L hL k
    cases L with
    | nil=>simp
    | cons x L=>
      have he:= p x (hL.subset List.mem_cons_self)
      have hs : L <+ A := (.trans ((List.Sublist.refl _).cons _) hL)
      have hp (P W U : List I) (p' : ∀ i∈U,c x i=0): pick x c (read c) P U=0 := by
        induction U generalizing P with
        | nil=> rfl
        | cons i L ih=> rw [pick,p' _ List.mem_cons_self,ih (P++[i]) (fun i t=>p' i (List.mem_cons_of_mem _ t)),zero_mul,zero_add]
      suffices H : ∀ P W : List I, P ++ W <+ L →
          pick x c (read c) P (W++B)= pick x c (read c) P W*read c B by
        rw [List.cons_append, read_more, read_more, H [] L (by simp)]
      intro P W hw; induction W generalizing P with
      | nil=> rw [List.nil_append,hp _ [] B he,pick,zero_mul]
      | cons i W ih' =>
        have hv := (List.Sublist.append (List.Sublist.refl P) ((List.Sublist.refl W).cons i)).trans hw
        rw [List.cons_append,pick, ← List.append_assoc P, ih _ (hv.trans hs)
          (hv.length_le.trans (by simpa using k)), ih' (P++[i]) (by simpa using hw),pick]
        ring

-- Off-diagonal convergence. Need ordered-pair prices even on large Gram.
variable {b : Filter J} {c : J → I → I → ℂ} {d : I → I → ℂ}
lemma attend (L : List I) (p : L.Pairwise (fun i j=> Tendsto (fun n=> c n i j) b (𝓝 (d i j)))) :
    Tendsto (fun n => read (c n) L) b (𝓝 (read d L)) := by
  suffices h : ∀ (i : ℕ) (P : List I), P <+ L → Tendsto (fun n => peek (c n) i P) b (𝓝 (peek d i P)) from
    h L.length L (.refl _)
  intro i; induction i with
  | zero=> intro P h; cases P <;> exact tendsto_const_nhds
  | succ a ih=>
    intro P hP
    cases P with
    | nil=>exact tendsto_const_nhds
    | cons i P=>
      have ht := List.pairwise_cons.mp (p.sublist hP)
      have hs : P <+ L := ((List.Sublist.refl _).cons _).trans hP
      suffices H : ∀ (U V : List I), U ++ V <+ P → Tendsto
          (fun n => pick i (c n) (peek (c n) a) U V) b (𝓝 (pick i d (peek d a) U V)) from H [] P (by simp)
      intro U V h; induction V generalizing U with
      | nil=>exact tendsto_const_nhds
      | cons j V ih' =>
        have hl := (List.Sublist.append (List.Sublist.refl U) ((List.Sublist.refl V).cons j)).trans h
        exact ((ht.1 j (h.subset (List.mem_append_right _ List.mem_cons_self))).mul
          (ih (U++V) (hl.trans hs))).add (ih' (U++[j]) (by simpa using h))

variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
def grainG (a b : E) : ℂ := (inner ℝ a b : ℝ)

lemma peek_memo (k : ℕ) (P : List E) (p : P.length ≤ k) :
    peek grainG k P=(memo P : ℂ) := by
  induction k generalizing P with
  | zero=> obtain rfl : P=[] := by simpa using p
           change 1 = _; simp [memo,payday]
  | succ k ih=>
    cases P with
    | nil => simp [peek, memo,payday]
    | cons x P=>
      rw [peek,gramStein]
      suffices h:∀ (U V : List E), U.length+V.length≤k →
          pick x grainG (peek grainG k) U V=(roster x U V:ℂ) from h [] P (by simpa using p)
      intro U V h; induction V generalizing U with
      | nil => simp [pick, roster]
      | cons i V ih'=>
        rw [pick, ih (U++V) (by simp at h ⊢; omega), ih' (U++[i]) (by simp at h ⊢; omega), roster]; push_cast; rfl

lemma census (P : List I) (X : I → E) :
    read (fun i j => grainG (X i) (X j)) P = (memo (P.map X):ℂ) := by
  rw [← read_map grainG P X, read]; exact peek_memo _ _ (le_refl _)

#print axioms attend
#print axioms insulated
#print axioms census
end WickG
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
