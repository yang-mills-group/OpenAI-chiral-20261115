/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Momenta.Tiled
import YM.SU5.Registration.LineUp.Assembly
/-!
 # Support local operators
 adapting Work/C27. On citizen test fields over station.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Set Filter Distribution MeasureTheory Mink Mink.Poincare Boundary
open _root_.YM.Boundary.Probe
open scoped Topology BigOperators ContDiff InnerProductSpace
variable {V:Type*} [AddCommGroup V] [Module ℂ V] {W:WView V} {n:ℕ}
namespace WView
theorem coordinate_tsupport (f : Fin n → Test4) (i : Fin n) :
    tsupport (Joint.materialize n f) ⊆ (fun x : Points n => x i) ⁻¹' tsupport (f i) := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro x hx
  apply subset_tsupport
  intro h
  apply hx
  exact (Joint.material_at f x).trans (Finset.prod_eq_zero (Finset.mem_univ i) h)

theorem materialize_switch (P : NearPair n) (f : Fin n → Test4) :
    Probe.along P.switch.toContinuousLinearEquiv (Joint.materialize n f) = Joint.materialize n (f ∘ P.s) := by
  ext1 x
  change Joint.materialize n f (P.switch x) = _
  simp only [Joint.material_at, NearPair.switch_at, Function.comp_apply]
  exact ((Equiv.prod_comp P.s (fun i => f i (x (P.s i)))) |>.symm.trans (by simp [NearPair.s]))

theorem exchange (W : WView V) (H : W.Localizes) (P : NearPair n)
    (v : Fin n → V) (f : Fin n → Test4) (hf : Fields.causal (f P.i) (f P.j)) :
    W.W n v (Joint.materialize n f) = W.W n (v ∘ P.s) (Joint.materialize n (f ∘ P.s)) := by
  have hs : tsupport (Joint.materialize n f) ⊆ P.gap := by
    intro x hx
    have hh := lateral _ |>.mp (hf (x P.i) (coordinate_tsupport f P.i hx) (x P.j) (coordinate_tsupport f P.j hx))
    change x P.j - x P.i ∈ spacelike
    rw [lateral, ← neg_sub (x P.i)]
    simpa only [clock_neg, rest_neg, abs_neg, norm_neg] using hh
  have hm := H n v P (Joint.materialize n f) hs
  change W.W n v _ - W.W n _ (Probe.along _ _) = 0 at hm
  rwa [sub_eq_zero, materialize_switch] at hm

theorem expect_get (W : WView V) (b : MarkWords V) (v : Fin n → MarkType V)
    (h : b.length = n) (hv : ∀ i, b.get i = v (Fin.cast h i)) :
    W.expect b = W.W n (fun i => (v i).1) (Joint.materialize n (fun i => (v i).2)) := by
  subst n
  have he : b.get = v := funext hv
  rw [WView.expect, he]

variable {α : Type*}

/-- Place two letters between the spectator lists. -/
def slots (a b : List α) (x y : α) (i : Fin (a.length + (b.length+2))) : α :=
    if h : i.val < a.length then a[i.val]
    else if _ : i.val = a.length then x
    else if _ : i.val = a.length+1 then y
    else b[i.val-(a.length+2)]'(by omega)

def pair (a b : List α) : NearPair (a.length + (b.length+2)) :=
  ⟨⟨a.length, by omega⟩, ⟨a.length+1, by omega⟩, rfl⟩

theorem get_slots (a b : List α) (x y : α) (i : Fin (a ++ x::y::b).length) :
    (a ++ x::y::b).get i = slots a b x y (Fin.cast (by simp) i) := by
  simp only [List.get_eq_getElem, slots, Fin.val_cast]
  split_ifs with h1 h2 h3
  · exact List.getElem_append_left h1
  · rw [List.getElem_append_right (by omega)]
    generalize_proofs _
    simp [h2]
  · rw [List.getElem_append_right (by omega)]
    generalize_proofs _
    simp [h3]
  rw [List.getElem_append_right (by omega)]
  have h : i.val - a.length = i.val - (a.length+2) + 1 + 1 := by omega
  generalize_proofs _
  simp [h]

theorem slots_switch (a b : List α) (x y : α) (i : Fin (a.length + (b.length+2))) :
    slots a b x y ((pair a b).s i) = slots a b y x i := by
  rcases eq_or_ne i (pair a b).i with rfl|hi
  · simp [NearPair.s, slots, pair]
  rcases eq_or_ne i (pair a b).j with rfl|hj
  · simp [NearPair.s, slots, pair]
  rw [NearPair.s, Equiv.swap_apply_of_ne_of_ne hi hj]
  have h : i.val ≠ a.length := fun h => hi (Fin.ext h)
  have k : i.val ≠ a.length+1 := fun h => hj (Fin.ext h)
  simp [slots, h, k]


lemma before_local (W:WView V)(H:W.Localizes)(a b:MarkWords V) (x y:V)(f g:Test4)(h:Fields.causal f g) : W.expect (a ++ (x,f)::(y,g)::b)=W.expect (a ++ (y,g)::(x,f)::b):=by
  rw [expect_get W _ _ _ (get_slots a b (x,f) (y,g)), expect_get W _ _ _ (get_slots a b (y,g) (x,f))]
  have he := exchange W H (pair a b) (fun i => (slots a b (x,f) (y,g) i).1)
    (fun i => (slots a b (x,f) (y,g) i).2) (by simpa [pair,slots] using h)
  simpa only [Function.comp_def,slots_switch] using he
end WView
namespace Carton
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}(B:Carton S V)(J:JMap V){F: InkWaves V}(u: InkPort B F W)(p: Remembers B J)
-- Dense detection on the sector.
lemma charged_iff {x y:B.station}: x=y ↔ ∀ i,inner ℂ (B.engaged i) x=inner ℂ (B.engaged i) y:=by
 constructor
 · rintro rfl i; rfl
 intro h; apply ext_inner_left ℂ; have he(c: (MarkWords V→₀ ℂ)): inner ℂ (B.seedPorts c) x=inner ℂ (B.seedPorts c) y:=by
   induction c using Finsupp.induction_linear with
   | zero=>simp
   | add i t e m=>simp only [map_add,inner_add_left,e,m]
   | single i t=>simp only [seedPorts,Finsupp.linearCombination_single,inner_smul_left,h]
 exact fun b=> congr_fun (B.tickets.equalizer (by fun_prop) (by fun_prop) (show (fun t:B.station=> inner ℂ t x) ∘ B.seedPorts= (fun t:B.station=> inner ℂ t y) ∘ B.seedPorts from funext he)) b
include p u
/-- BUY spacelike locality on the shared D_point. No operator assertion on its complement in projected G. -/
theorem supported (h:W.Localizes)(x y:V)(f g:Test4)(hf:Fields.causal f g) : (B.pointMap x f).comp (B.pointMap y g)=(B.pointMap y g).comp (B.pointMap x f):=by
 refine B.buds_pt _ _ fun i=> ?_; rw [LinearMap.comp_apply,LinearMap.comp_apply,← B.eval, ← B.eval,← B.eval,← B.eval]; refine Subtype.ext ((B.charged_iff).2 (fun w=>?_)); change inner ℂ (B.evaluate _).val _=inner ℂ (B.evaluate _).val _; rw [← B.literal_gram J F W u p,← B.literal_gram J F W u p]; exact W.before_local h _ _ _ _ _ _ hf
lemma regional {R:Courts V}(h:R.Carriage F)(x y:V)(f g:Test4)(hf:Fields.causal f g)(a:B.citizen) : B.pointMap x f (B.pointMap y g a)=B.pointMap y g (B.pointMap x f a):= LinearMap.congr_fun (B.supported J u p (WView.isLocal u h) x y f g hf) a
end Carton
end YM.SatinWFixed
