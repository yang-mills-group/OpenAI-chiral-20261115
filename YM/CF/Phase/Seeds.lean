import YM.CF.Phase.Markov
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Tree-compatible assignment kernels with total-site normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Filter MeasureTheory Finset Function
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def rateF (m B : Side) (U : Skin m B) (f : ArrayF m) (a : Spot m) (l : List (Ramp m)) : ℝ := ‖restrain margin (train m B U f a.1 l) (f a).val‖
-- strict > margin even on closure: demand rateF>broad on positive locus
def fundF (m B : Side) (U : Skin m B) (f : ArrayF m) (r : Zone) (a : Spot m) := ∏ l∈permits m a r, expNegInvGlue (rateF m B U f a l-broad)
lemma fund_pos (m B U f r a) : 0 ≤ fundF m B U f r a := prod_nonneg (fun l _=>expNegInvGlue.nonneg _)
lemma pay (m B U f r a) (h : 0<fundF m B U f r a) : ∀ l∈permits m a r,broad<rateF m B U f a l := by
  intro l hl; by_contra! k
  have ht : expNegInvGlue (rateF m B U f a l-broad)=0 := expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr k)
  exact h.ne' (prod_eq_zero hl ht)
lemma pay_check (m B U f r a) (h : ∀ l∈permits m a r, broad≤rateF m B U f a l) : Check m B margin U f r a := fun l hl=>broad_margin.trans_le (h l hl)
lemma fund_cont (m B r a) : Continuous (fun t : FlagU m B=> fundF m B t.1 t.2 r a) :=
  continuous_finsetProd _ fun i _=>(expNegInvGlue.contDiff (n:=0)).continuous.comp ((fee_cont m B a i).sub continuous_const)
lemma fund_sufficient (m B U f r a) (h : ∀ l∈permits m a r,broad < rateF m B U f a l) : 0 < fundF m B U f r a := prod_pos fun l hl => expNegInvGlue.pos_of_pos (sub_pos.mpr (h l hl))
lemma fund_same (m B U s t r a) (h : ∀ i : Spot m, i=a ∨ (Prev m i a ∧ i.2∈r) → s i=t i) : fundF m B U s r a=fundF m B U t r a := by
  unfold fundF; apply prod_congr rfl; intro l hl; unfold rateF
  rw [h a (Or.inl rfl),train_eq m B U t _ _ _ (fun x hx=> h x.1 (Or.inr ⟨move_mem (permits_iff.mp hl).1 _ hx,(permits_iff.mp hl).2 _ hx⟩))]
lemma fund_g (m B U f r a) (k) : fundF m B (gauge k U) (onF k f) r a=fundF m B U f r a := by
  unfold fundF; apply prod_congr rfl; intro l _; unfold rateF
  rw [train_g,show (onF k f a).val=turn _ _ from rfl, strain_turn,turn_norm]

section
variable (m B : Side)
def dry (U : Skin m B) (f : ArrayF m) (s : Zone) (j : Row) (a : Index m) (x : Cue m) := fundF m B U (capRow f j x) (insert j s) (a,j)
-- product discount for families of preceding rims (including empty preceding constraints, captured by one request with r empty)
def draw {I : Type} (S : Finset I) (U : Skin m B) (f : I → ArrayF m) (r : I → Zone) (j : Row) (a : Index m) (x : Cue m) := ∏ i∈S,dry m B U (f i) (r i) j a x
def limitW {I : Type} (S : Finset I) (U : Skin m B) (f : I → ArrayF m) (r : I → Zone) (j : Row) (a : Index m) (x : Cue m) := ∫ t, draw m B S U f r j a (update x a t) ∂cloud
def priceW {I : Type} (S : Finset I) (U : Skin m B) (f : I → ArrayF m) (r : I → Zone) (j : Row) (a : Index m) (x : Cue m) := draw m B S U f r j a x/limitW m B S U f r j a x
def rates {I : Type} (S : Finset I) (U : Skin m B) (f : I → ArrayF m) (r : I → Zone) (j : Row) (x : Cue m) := ∏ a, priceW m B S U f r j a x
variable {I : Type} [Fintype I] [DecidableEq I]
variable (S : Finset I) (U : Skin m B) (f : I→ArrayF m) (r : I→Zone) (j : Row) (a : Index m) (x : Cue m)
lemma draw_pos : 0≤draw m B S U f r j a x := prod_nonneg (fun i _=>fund_pos ..)
lemma draw_strong (h : S.card≤6) : ∃ t, 0<draw m B S U f r j a (update x a t) := by
  obtain ⟨v,H⟩ := choose_tip m B U S (fun i=>capRow (f i) j x) r j h a
  refine ⟨v,prod_pos ?_⟩; intro i hi
  apply fund_sufficient
  intro l hl
  have he : (capRow (f i) j (update x a v) (a,j)).val=v.val := by simp [capRow]
  unfold rateF
  rw [he,train_eq m B U (capRow (f i) j x) a l _]; exact H i hi l hl
  rintro ⟨⟨b,g⟩,o⟩ hb
  have he : (b,g)≠(a,j) := (move_mem (permits_iff.mp hl).1 _ hb).2.2
  unfold capRow; dsimp only; split_ifs with hx
  · subst g; have hg : b≠a := fun h=>he (by rw [h]); rw [Function.update_of_ne hg]
  rfl
lemma draw_cont : Continuous (fun t : Skin m B × (I→ArrayF m) × Cue m=>draw m B S t.1 t.2.1 r j a t.2.2) := by
  unfold draw dry; apply continuous_finsetProd; intro i _
  let F := fun t:Skin m B × (I→ArrayF m) × Cue m=> (t.1,capRow (t.2.1 i) j t.2.2)
  change Continuous ((fun t:FlagU m B=>fundF m B t.1 t.2 (insert j (r i)) (a,j)) ∘ F)
  apply (fund_cont ..).comp
  apply Continuous.prodMk continuous_fst; refine continuous_pi fun x=>?_
  unfold capRow; split <;> fun_prop
lemma updC (a : Index m) : Continuous (fun t:Cue m×Ballot=>update t.1 a t.2) := by
  refine continuous_pi fun i => ?_; by_cases h:i=a
  · subst i; simp; exact continuous_snd
  simp [update_of_ne h]; fun_prop
lemma turn_draw_cont : Continuous (fun w : (Skin m B × (I→ArrayF m) × Cue m) × Ballot =>
      draw m B S w.1.1 w.1.2.1 r j a (update w.1.2.2 a w.2)) := by
  let F := fun t : (Skin m B × (I→ArrayF m) × Cue m) × Ballot => (t.1.1,t.1.2.1,update t.1.2.2 a t.2)
  change Continuous ((fun t:Skin m B × (I→ArrayF m)×Cue m=> draw m B S t.1 t.2.1 r j a t.2.2) ∘ F)
  apply (draw_cont ..).comp
  apply Continuous.prodMk (by fun_prop); apply Continuous.prodMk (by fun_prop)
  exact (updC m a).comp ( (continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
lemma limit_cont : Continuous (fun t : Skin m B × (I→ArrayF m) × Cue m=>limitW m B S t.1 t.2.1 r j a t.2.2) := net_cont _ _ (turn_draw_cont m B S r j a)
lemma limit_pos (h : S.card≤6) : 0 < limitW m B S U f r j a x := by
  obtain ⟨v,hv⟩ := draw_strong m B S U f r j a x h
  let F t := draw m B S U f r j a (update x a t)
  let G := fun t:Ballot => ((U,f,x),t)
  have hg : Continuous G := continuous_const.prodMk continuous_id
  have he : Continuous F := by
    let D := fun w : (Skin m B × (I→ArrayF m) × Cue m) × Ballot => draw m B S w.1.1 w.1.2.1 r j a (update w.1.2.2 a w.2)
    change Continuous (D ∘ G); exact (show Continuous D from turn_draw_cont m B S r j a).comp hg
  change 0 < ∫ t, F t ∂cloud
  exact integral_pos_of_integrable_nonneg_nonzero he (net_compact he) (fun _=>draw_pos ..) hv.ne'
lemma price_pos (h : S.card≤6) : 0≤priceW m B S U f r j a x := div_nonneg (draw_pos ..) (limit_pos _ _ _ _ _ _ _ _ _ h).le
lemma price_live (h : S.card≤6) (H : 0<priceW m B S U f r j a x) : ∀ i∈S, 0<dry m B U (f i) (r i) j a x := by
  have ht : 0 < draw m B S U f r j a x := by
    unfold priceW at H; rw [lt_div_iff₀ (limit_pos m B S U f r j a x h),zero_mul] at H; exact H
  intro i hi
  exact lt_of_le_of_ne (fund_pos ..) (fun g=> ht.ne' (prod_eq_zero hi g.symm))
lemma price_cont (h : S.card≤6) : Continuous (fun t: Skin m B × (I→ArrayF m) × Cue m=>priceW m B S t.1 t.2.1 r j a t.2.2) :=
  (draw_cont m B S r j a).div (limit_cont m B S r j a) (fun t=>(limit_pos m B S _ _ r j a _ h).ne')
lemma price_integral (h : S.card≤6) : (∫ t, priceW m B S U f r j a (update x a t) ∂cloud)=1 := by
  unfold priceW limitW; simp_rw [update_idem]; rw [integral_div,div_self]; exact (limit_pos m B S U f r j a x h).ne'
end
end YM.CF.Phase
