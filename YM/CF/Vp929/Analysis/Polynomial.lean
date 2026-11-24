import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! Bounded-coefficient interpolation for the exponential-sample payment, Part 1.
 Ordinary interpolation on (0,1); the IH gets applied to the derivative of the polynomial,
 using Rolle to find (any) interleaved set of sufficiently many nodes of agreement there. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Set Function Complex Polynomial
open Finset (range)
open scoped BigOperators
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
private abbrev B := Set.Ioo (0:ℝ) 1
/-- Simple recursive jet bounds on (0,1), convenient for interpolation. -/
def BJet (A:ℝ) : ℕ → (ℝ→E) → Prop
 | 0,f => ∀ x ∈ B, ‖f x‖ ≤ A
 | n+1,f=> (∀ x ∈ B, ‖f x‖ ≤ A) ∧ ∃ f', (∀ x ∈ B, HasDerivAt f (f' x) x) ∧ BJet A n f'
local notation "J" => BJet
variable {f g : ℝ → E} {a b C : ℝ} {n : ℕ}
lemma BJet.val (h : J a n f) : ∀ x ∈ B, ‖f x‖ ≤ a := by cases n; exact h; exact h.1
lemma BJet.congr (hf : J a n f) (e : EqOn f g B) : J a n g := by
  have A: ∀ x∈ B, ‖g x‖ ≤ a:= fun x p=> e p ▸ hf.val x p
  cases n; exact A; obtain ⟨_,f',Q,H⟩:=hf; exact ⟨A, f', fun x p => (Q x p).congr_of_eventuallyEq (e.symm.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds p)), H⟩
lemma BJet.mono (hf : J a n f) (e : a ≤ b) : J b n f := by
  induction n generalizing f with
  | zero=> exact fun x p=>(hf.val x p).trans e
  | succ n ih=> have ⟨H,f',Q,U⟩:=hf; exact ⟨fun x p=>(H x p).trans e,f',Q,ih U⟩
lemma BJet.add (h : J a n f) (q : J b n g) : J (a+b) n (fun x=> f x + g x) := by
  have p (x)(hx:x∈B):‖f x+g x‖ ≤ a+b:= (norm_add_le ..).trans (add_le_add (h.val x hx) (q.val x hx))
  induction n generalizing f g with
  | zero=> exact p
  | succ n ih=>
    obtain ⟨_,F,H,y⟩:=h; obtain ⟨_,G,Q,z⟩:=q; refine ⟨p,(fun x=> F x + G x),fun x hx=>(H x hx).add (Q x hx),?_⟩; exact ih y z fun x t => (norm_add_le ..).trans (add_le_add (y.val x t) (z.val x t))
lemma BJet.clm (h : J a n f) (L : E →L[ℝ] F) (e : ∀ x, ‖L x‖ ≤ C * ‖x‖) (p:0 ≤ C) : J (C*a) n (fun x=> L (f x)) := by
  induction n generalizing f with
  | zero=> exact fun x hx=>(e _).trans (mul_le_mul_of_nonneg_left (h.val x hx) p)
  | succ n ih=>
    have ⟨H,f',Q,z⟩:=h; exact ⟨fun x hx=>(e _).trans (mul_le_mul_of_nonneg_left (H x hx) p),fun x=> L (f' x),fun x hx=> L.hasFDerivAt.comp_hasDerivAt x (Q x hx), ih z⟩
-- interleaving
variable {s : Finset ℝ} {w : ℝ[X]} {F F' : ℝ→ℝ}
private lemma next_nodes (hs:(s:Set ℝ) ⊆ B) (P:EqOn w.eval F s) (Q:∀ x∈B, HasDerivAt F (F' x) x) :
    ∃ t: Finset ℝ, t.card=s.card-1 ∧ (t:Set ℝ) ⊆ B ∧ EqOn w.derivative.eval F' t := by
  classical
  have hV (x)(hx:x∈s)(y)(hy:y∈s) (h : (x:ℝ)<y) : ∃ z∈ Ioo x y, w.derivative.eval z = F' z := by
    have hu: Icc x y ⊆ B:= fun z hz => ⟨lt_of_lt_of_le (hs (show x∈ (s:Set ℝ) from hx)).1 hz.1, lt_of_le_of_lt hz.2 (hs (show y∈(s:Set ℝ) from hy)).2⟩
    have T (z) (H:z∈Icc x y):HasDerivAt (fun u=> w.eval u - F u) (w.derivative.eval z - F' z) z:= (w.hasDerivAt z).sub (Q z (hu H))
    obtain ⟨z,hz,Q⟩:= exists_hasDerivAt_eq_zero h (fun z p => (T z p).continuousAt.continuousWithinAt) (show w.eval x - F x = w.eval y - F y by exact (sub_eq_zero.mpr (P hx)).trans (sub_eq_zero.mpr (P hy)).symm) (fun z p=>T z (Ioo_subset_Icc_self p)); exact ⟨z,hz,sub_eq_zero.mp Q⟩
  choose! z hz Q using hV
  let s': Finset ℝ:= ((s ×ˢ s).filter (fun p:ℝ×ℝ=> p.1 < p.2)).image (fun p=> z p.1 p.2)
  have U (p)(hP:p∈s'): p∈B ∧ w.derivative.eval p = F' p:= by
    obtain ⟨⟨x,y⟩,h,rfl⟩:= Finset.mem_image.mp hP; rw [Finset.mem_filter,Finset.mem_product] at h
    exact ⟨⟨lt_trans (hs h.1.1).1 (hz x h.1.1 y h.1.2 h.2).1,lt_trans (hz x h.1.1 y h.1.2 h.2).2 (hs h.1.2).2⟩,Q x h.1.1 y h.1.2 h.2⟩
  have H: s.card ≤ (s' \ s).card+1:= Finset.card_le_sdiff_of_interleaved (fun x hx y hy h _=> ⟨z x y, Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,h⟩,rfl⟩, hz x hx y hy h⟩)
  have:= Finset.card_le_card (Finset.sdiff_subset (s:=s') (t:=s)); obtain ⟨t,e,Q⟩:= Finset.exists_subset_card_eq (show s.card-1≤s'.card by omega); exact ⟨t,Q,fun x hx=>(U x (e hx)).1,fun x hx=>(U x (e hx)).2⟩

private lemma jetCoeffAux (N:ℕ): ∃ C:ℝ, 1≤C ∧ ∀ a:ℝ, 0≤a→∀ F:ℝ→ℝ, BJet a N F→ ∀ s:Finset ℝ, ∀ w:ℝ[X], EqOn w.eval F s → w.natDegree < s.card → s.card ≤ N+1 → (s:Set ℝ)⊆ B → ∀ i, |w.coeff i| ≤ C*a := by
  classical
  have Z (C a : ℝ) (h : 1 ≤ C) (hp:0 ≤ a) (F:ℝ→ℝ) (s:Finset ℝ) (w:ℝ[X]) (he : EqOn w.eval F s) (hu:(s:Set ℝ) ⊆ B) (hy : s.Nonempty) (hk:w.natDegree=0) (hc:∀ x∈B, ‖F x‖ ≤ a) (i:ℕ) : |w.coeff i| ≤ C*a:= by
    by_cases e:i=0
    · obtain ⟨x,hx⟩:=hy; subst i; have U:=hc x (hu hx); rw [← he hx,eq_C_of_natDegree_eq_zero hk] at U; simp only [eval_C] at U; exact U.trans (le_mul_of_one_le_left hp h)
    rw [coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]; positivity
  induction N with
  | zero => refine ⟨1,le_rfl,?_⟩; intro a hp F hf s w he q ht hu; apply Z 1 _ le_rfl hp _ _ _ he hu (Finset.card_pos.mp (by omega)) (by omega) hf.val
  | succ N ih=>
    obtain ⟨C,H,V⟩:= ih; refine ⟨1+(N+1:ℝ)*C+C,by nlinarith [show 0≤(N:ℝ) by positivity], ?_⟩
    intro a hp F hf s w he q ht hu; have hy : s.Nonempty:= Finset.card_pos.mp (by omega); have hc:0≤C:=by linarith
    by_cases e:w.natDegree=0; exact Z _ _ (by nlinarith [show 0≤(N:ℝ) by positivity]) hp _ _ _ he hu hy e hf.val
    obtain ⟨U,F',Q,Y⟩:= hf; obtain ⟨t,r,h,u⟩:= next_nodes hu he Q
    have K (i): |w.coeff (i+1)| ≤ C*a:= by
      have:= V a hp F' Y _ _ u (by have:=natDegree_derivative_lt e;omega) (by omega) h i
      rw [coeff_derivative, abs_mul, abs_of_nonneg (show 0 ≤ (i+1:ℝ) by positivity)] at this; nlinarith [show 0≤(i:ℝ) by positivity,abs_nonneg (w.coeff (i+1))]
    rintro (_ | i)
    · obtain ⟨x,hx⟩:=hy; have Fp : w.eval x = F x:=he hx
      rw [eval_eq_sum_range' (n:=N+1+1) (by omega), Finset.sum_range_succ', pow_zero,mul_one] at Fp; rw [show w.coeff 0=F x-_ from eq_sub_of_add_eq' Fp]; refine (abs_sub ..).trans ((add_le_add (U _ (hu hx)) ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (?_ : ∀ i∈range (N+1), _ ≤ C*a)))).trans ?_)
      · intro i hi; rw [abs_mul,abs_of_nonneg (show 0 ≤ x^(i+1) by have:= (hu hx).1; positivity)]; exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (hu hx).1.le (hu hx).2.le)).trans (K i)
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; nlinarith
    refine (K _).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hp)
/-- Use interpolation at arbitrarily close nodes in (0,1); nodes needn't be separated. -/
lemma jetCoeff (N:ℕ) : ∃ C:ℝ, 1 ≤ C ∧ ∀ a:ℝ, 0 ≤ a → ∀ F:ℝ→ℝ, BJet a N F→∀ s:Finset ℝ, s.card ≤ N+1 → (s:Set ℝ) ⊆ B → ∃ w:ℝ[X], EqOn w.eval F s ∧ w.natDegree ≤ N ∧ ∀ i:ℕ, |w.coeff i| ≤ C*a := by
 classical
 obtain ⟨C,H,U⟩:=jetCoeffAux N; refine ⟨C,H,?_⟩; intro a hp F hf s h hs
 rcases s.eq_empty_or_nonempty with e|e; subst s; exact ⟨0, by simp,by simp,by simp;positivity⟩
 let w:= Lagrange.interpolate s id F; have he: EqOn w.eval F s:= fun x hx=>Lagrange.eval_interpolate_at_node _ injective_id.injOn hx
 have q: w.natDegree < s.card:= by
   by_cases q:w=0; simpa [q] using Finset.card_pos.mpr e
   have H: w.degree < (s.card:WithBot ℕ):= Lagrange.degree_interpolate_lt _ injective_id.injOn; rw [degree_eq_natDegree q] at H; exact_mod_cast H
 exact ⟨w,he,by omega, U _ hp _ hf _ _ he q h hs⟩
end
end YM.CF.VolumeRate
