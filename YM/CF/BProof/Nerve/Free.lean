import YM.CF.BProof.Nerve.Balance
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
-- Nearby nondegeneracy conditions before hierarchy.
namespace Guard
structure Test (S: Support n)(s:ℕ)(X:Quint n) : Prop where
 spread:Injective X
 crew(i):X i∈ S
 cost(i j):separation (X i) (X j)≤ 2*(Halo*s)
variable {X : Quint n} {S : Support n}
def target(X:Quint n) : Site n:= X (lead X)
abbrev Lines (S:Support n)(s:ℕ)(i:Site n): Finset (Quint n):= univ.filter fun X=> Test S s X∧ target X=i
@[simp] lemma enters(X:Quint n)(x:Site n):X∈Lines S s x↔Test S s X∧ target X=x:=by simp only [Lines,mem_filter,mem_univ,true_and]
lemma cost0 (t:Test S s X)(i j): separation (X i) (X j) ≤ King*s:=(t.cost ..).trans (by unfold King; nlinarith)
lemma drift (f g:Site n→ℝ)(i:Site n)(t:Test S s X)(u:i=target X)(p:Matches (region n i (King*s)) f g) : Drift s X f=Drift s X g:=by
 unfold Drift Mode; apply sum_congr rfl; intro j _; rw [p ((reg_in ..).2 (u.symm ▸ cost0 t _ j))] -- u.symm ▸ try
lemma twist (h:SmallN s n)(r:Signed)(i:Site n)(t:Test S s X): target (facet r i ∘ X)=facet r i (target X):=by unfold target; rw [(fold r i X (fun i=>(cost0 t _ 0).trans (by omega)) h).2]; rfl -- if rw
lemma equate(h:SmallN s n)(r:Signed)(i:Site n)(t:Test S s X)(f:Site n→ℝ): Drift s (facet r i ∘ X) f= Drift s X (f ∘ facet r i) :=by
 unfold Drift Mode; rw [(fold r i X (fun i=>(cost0 t _ 0).trans (by omega)) h).1]; apply sum_congr rfl; intro j _; simp only [Function.comp_apply, reor r _ _ _ ((cost0 t j 0).trans (by omega)) h]
lemma tribute{f g:Site n→ℝ}{i:Fin 6}(p:Injective X)(h:∀ j,j≠i→ f (X j)=g (X j)): Drift s X f-Drift s X g=wind X i*(f (X i)-g (X i)):=by
 unfold Drift Mode; rw [←sum_sub_distrib,sum_eq_single i]; ring; intro j _ t; rw [h j t,sub_self]; simp
variable {U:Field n A (Fin z)}{V:Field n A Prop}
abbrev N(k:ℕ):=k^6
lemma counted (t:Policy.Busy.goodHue V U (King*s))(x:A)(i:Site n): (Lines (crowd V x) s i).card ≤ N z :=by
 let S:=crowd V x; let paint(y:Lines S s i):= U x ∘ y.val
 have he {y:Quint n} (h:y∈ Lines S s i)(j): V x (y j)∧separation (y j) i≤2*(Halo*s):=by obtain ⟨v,p⟩:= enters ..|>.mp h; exact ⟨crowd_in ..|>.1 (v.crew j), p ▸ v.cost j _⟩
 have hp: Injective paint:=by
    intro x' y F; apply Subtype.ext; ext1 j; by_contra h; apply t x _ _ (he x'.property j).1 (he y.property j).1 h _ (congrFun F j); refine (separation_triangle _ i _).trans ((Nat.add_le_add (he x'.property j).2 ((separation_comm i _).le.trans (he y.property j).2)).trans ?_); unfold King; nlinarith
 simpa only [Fintype.card_coe,Fintype.card_fin,Fintype.card_fun,S,N] using Fintype.card_le_of_injective paint hp

-- choose numerals.Pay. Slots ∈ W=N+1.Int.Weight. Define real tap.
def shelf(k:ℕ):ℕ := N k+1
def price(k:ℕ):ℝ :=100 * (shelf k:ℝ)
lemma fund_pos(k:ℕ):0 < shelf k:=Nat.succ_pos _
lemma price_pos(k:ℕ): 1 ≤ price k:=by
 have h:(1:ℝ) ≤ shelf k:=by exact_mod_cast fund_pos k
 unfold price; linarith
-- epsilon(q)=1/price^(q+1)
def slip(k q:ℕ):ℝ:= (price k)⁻¹^(q+1)
def jot(k q:ℕ)(i:Fin (shelf k)):ℝ:= i.val*slip k q
abbrev cap(k q:ℕ):ℝ:= (shelf k:ℝ)*slip k q
lemma price_age(k:ℕ):0< price k:=lt_of_lt_of_le zero_lt_one (price_pos k)
lemma slip_pos(k q:ℕ): 0 < slip k q:=pow_pos (inv_pos.mpr (price_age k)) _
lemma reverse(k:ℕ):Antitone (slip k):=by
 apply antitone_nat_of_succ_le; intro n; let p:=(price k)⁻¹; exact le_of_eq (pow_succ p (n+1))|>.trans (mul_le_of_le_one_right (slip_pos k n).le (inv_le_one_of_one_le₀ (price_pos k))) -- tune names
lemma table (k n:ℕ) (i:Fin (shelf k)):0≤ jot k n i ∧ jot k n i ≤ cap k n:=⟨mul_nonneg (by positivity) (slip_pos ..).le, mul_le_mul_of_nonneg_right (by exact_mod_cast i.2.le) (slip_pos ..).le⟩ -- syntax length
lemma cap_le(k n:ℕ): cap k n ≤ 1 :=by
 apply (mul_le_mul_of_nonneg_left (reverse k (Nat.zero_le n)) (by positivity)).trans; unfold slip; rw [Nat.zero_add,pow_one,←div_eq_mul_inv,div_le_one (price_age k)]; unfold price; linarith [(Nat.cast_nonneg (α:=ℝ) (shelf k))]
lemma after(k n:ℕ): 6* cap k (n+1) ≤ slip k n/6:=by
 unfold cap; rw [show slip k (n+1)= slip k n*(price k)⁻¹ from pow_succ _ _,← mul_assoc,← mul_assoc,← div_eq_mul_inv, div_le_div_iff₀ (price_age k) (by norm_num)]; unfold price; nlinarith [slip_pos k n, Nat.cast_nonneg (α:=ℝ) (shelf k)]
lemma jumps(k n:ℕ)(i j:Fin (shelf k))(h:i≠j) : slip k n ≤ |jot k n i-jot k n j|:=by
 unfold jot; rw [←sub_mul, abs_mul,abs_of_pos (slip_pos ..)]; apply le_mul_of_one_le_left (slip_pos ..).le; rw [le_abs]; have hb:i.val≠j.val:= fun t=>h (Fin.ext t); refine (show i.val≥j.val+1∨ j.val≥i.val+1 from by omega).imp (fun t=>?_) (fun t=>?_); all_goals zify at t; rify at t; grind
end Guard
end YM.CF.BProof.Mesh.Nerve
