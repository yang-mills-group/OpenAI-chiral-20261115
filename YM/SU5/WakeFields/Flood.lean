import YM.CF.Roots.Sort

/-!
# Flood: a filtration (lower degree, retains analytic data on the whole hill)

Needed when a physical marking is *inserted on top of* already active RG Keys.
We cannot regard the old occurrences as the unmarked Gram; and the new perturbations
must use those same Keys in computing the many-pose coefficients. Thus terms of the
layer-finite birth recurrence will no longer be homogeneous. Work directly in the
filtered algebra on the diagonal with the earlier Keys. We measure in the tipI convention
(i.e., once in each Key, not daisy chaining along a single Key).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.CF.Mew
open Function NormedSpace Filter Finset
open scoped Topology BigOperators ContDiff Classical
variable {I E F G N : Type*} [LinearOrder I] [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- The function must be River, not just near the origin. Lengths here count cut
integrals (they agree with the appropriate successive derivatives for distinct Keys).
Very convenient not to have to exclude lists with repeated indices. -/
structure Flood (p : ℕ) (f : Key I → E) : Prop where
    riv : River f
    ebb : ∀ l : List I, l.length < p → tipI f l = 0
namespace Flood
variable {p r : ℕ} {f g : Key I → E}
lemma ground (h : River f) : Flood 0 f := ⟨h, fun _ v=> False.elim (by omega)⟩
lemma lower (v : Flood p f) (h : r ≤ p) : Flood r f := ⟨v.riv,fun l u=>v.ebb l (u.trans_le h)⟩
lemma null (r : ℕ) : Flood r (fun _ : Key I=>(0:E)) := ⟨zeroR _,fun l _=>tip_0 l⟩
lemma oneStep (f : Key I → E) : Flood 1 f ↔ River f ∧ f 0 = 0 := by
 constructor
 · exact fun p=> ⟨p.riv,p.ebb [] (by simp)⟩
 exact fun ⟨v,h⟩ => ⟨v,fun l u=> by
    cases l
    · exact h
    simp at u⟩
lemma grow (v : Flood p f) : p>0 → f 0 = 0 := fun h=>v.ebb [] h
lemma coord (i : I) : Flood 1 (fun x : Key I=>x i) :=
 (oneStep _).mpr ⟨(pine_r ({i}:Finset I)).cong (fun x _=>by simp [pine]), rfl⟩
lemma cong (p : Flood r f) (v : Set.EqOn g f (hill I)) : Flood r g :=
 ⟨p.riv.cong v,fun l h => (lace_C _ v roots).trans (p.ebb l h)⟩
lemma plus (h : Flood p f) (q : Flood p g) : Flood p (fun x=> f x+g x) :=
 ⟨dub_V h.riv q.riv,fun i v=> by rw [tip_A h.riv q.riv,h.ebb i v,q.ebb i v,add_zero]⟩
lemma scaler (h : Flood p f) (c : ℂ) : Flood p (fun z=> c • f z) :=
 ⟨h.riv.scale _,fun i v=> by rw [tip_C h.riv,h.ebb i v,smul_zero]⟩
lemma sub (h : Flood p f) (q : Flood p g) : Flood p (fun x=> f x-g x) := by
 simp_rw [sub_eq_add_neg, ← neg_one_smul ℂ (g _)]; exact h.plus (q.scaler _)
lemma total {A : Type*} (S : Finset A) (W : A → Key I → E) (q : ∀ i∈S,Flood p (W i)) :
    Flood p (fun x=>∑ i∈S, W i x) := by
 let A' := tip_bank S W (fun i v=>(q i v).riv); refine ⟨A'.1,fun i u=>?_⟩
 rw [A'.2]; exact sum_eq_zero (fun j v=> (q j v).ebb i u)
lemma transport (h : Flood p f) (v : E →L[ℂ] F) : Flood p (fun x=>v (f x)) :=
 ⟨sc_V h.riv v,fun i k=> (sim_H h.riv v i roots).trans (by change v (tipI f i)=0; rw [h.ebb i k, map_zero])⟩

lemma bridge (h : Flood p f) (i : I) : Flood p (f ∘ dune i) := by
 let v:=h.riv.stay i; refine ⟨v,fun l p=>?_⟩
 by_cases g:i∉l
 · rw [tip_V i l g,h.ebb l p]

 have ht : Set.EqOn (cutI (f∘dune i) i) (fun _=>0) (hill I) := by
    intro z w
    rw [←(mitt v w i).deriv]; simp [dune]
 calc
    _ = tipI (f∘dune i) (i::l.erase i) := Roots.move_ζ (List.perm_cons_erase (not_not.mp g)) v roots
    _ = _ := (lace_C (l.erase i) ht roots).trans (tip_0 _)

lemma wind (h : Flood p f) (i : I) : Flood (p-1) (cutI f i) :=
 ⟨h.riv.flow i,fun l k=> h.ebb (i::l) (by rw [List.length_cons]; omega)⟩

end Flood
lemma riverBeam (V : E→L[ℂ]F→L[ℂ]G) {f : Key I→E} {g : Key I→ F}
    (p : River f) (q : River g) : River (fun x=> V (f x) (g x)) :=
 ⟨(V.continuous.comp_continuousOn p.shore).clm_apply q.shore,fun x t i y u =>
    (V.differentiableAt.comp y (p.slope x t i y u)).clm_apply (q.slope x t i y u)⟩

lemma beam_tip (V : E→L[ℂ]F→L[ℂ]G) {f : Key I→E} {g : Key I→ F}
    (p : River f) (q : River g) (i : I) (l : List I) :
    tipI (fun z=>V (f z) (g z)) (i::l) =
        tipI (fun z=>V (cutI f i z) ((g∘dune i) z)) l +
        tipI (fun z=>V ((f∘dune i) z) (cutI g i z)) l := by
 let A(z):= V (cutI f i z) (g (dune i z)); let B(z):= V (f (dune i z)) (cutI g i z)
 have e : Set.EqOn (cutI (fun z=>V (f z) (g z)) i) (fun z=>A z+B z) (hill I):=
    fun z w=> (mitt (riverBeam V p q) w i).deriv.symm.trans
       (((V.hasFDerivAt.comp_hasDerivAt _ (mitt p w i)).clm_apply (mitt q w i)).deriv)
 exact (lace_C l e roots).trans (tip_A (f:=A) (riverBeam V (p.flow i) (q.stay i)) (g:=B) (riverBeam V (p.stay i) (q.flow i)) l)

lemma Flood.beam (V : E→L[ℂ]F→L[ℂ]G) {f : Key I→E} {g : Key I→F} {p r : ℕ}
    (h : Flood p f) (q : Flood r g) : Flood (p+r) (fun z=>V (f z) (g z)) := by
 refine ⟨riverBeam V h.riv q.riv,?_⟩
 intro l w; induction l generalizing p r f g with
 | nil =>
    simp only [List.length_nil] at w; change V (f 0) (g 0)=0; by_cases k: p>0
    · rw [h.grow k,map_zero]; rfl
    rw [q.grow (by omega),map_zero]
 | cons i l ih =>
    rw [List.length_cons] at w
    rw [beam_tip V h.riv q.riv, ih (h.wind i) (q.bridge i) (by omega), ih (h.bridge i) (q.wind i) (by omega), zero_add]

lemma Flood.times [NormedRing N] [NormedAlgebra ℂ N] [CompleteSpace N]
    {f g : Key I→N} {p r : ℕ} (v : Flood p f) (w : Flood r g) :
    Flood (p+r) (fun x=> f x*g x) := v.beam (ContinuousLinearMap.mul ℂ N) w
lemma Flood.purchase {A : Type*} [NormedCommRing N] [NormedAlgebra ℂ N] [CompleteSpace N]
    (S : Finset A) (F : A→Key I→N) (v : A→ℕ) (p : ∀ i∈S,Flood (v i) (F i)) :
    Flood (∑ i ∈ S, v i) (fun z=> ∏ i∈S,F i z) := by
 induction S using Finset.induction_on with
 | empty=> simp_rw [sum_empty,prod_empty]; exact Flood.ground (zeroR _)
 | insert i S h ih=> simp_rw [sum_insert h,prod_insert h]; exact (p i (mem_insert_self ..)).times (ih (fun i v=> p i (mem_insert_of_mem v)))
end YM.CF.Mew
#print axioms YM.CF.Mew.Flood.beam
