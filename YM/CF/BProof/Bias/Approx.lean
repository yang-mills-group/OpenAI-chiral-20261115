import YM.CF.BProof.Bias.Swipe
import YM.CF.BProof.PL
/-! Uniform inversion-on-sector estimate with time tails, using same exponential
bounds on physical projectors as in support estimates. This replaces a limiting step
in B-bias in our finite-torus exhaustion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Stint Lattice Cube Align Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I][DecidableEq I][Nonempty I]{F:I→Per N}{r t:ℕ}{A B:Op I}
def Near (F:I→Per N)(n:ℕ)(q:ℝ)(A:Op I): Prop:=∃ U:Op I,Span F n U∧ ‖A-U‖≤q
lemma cent_card (t:ℕ): (cent (0:Per N) t).card ≤ 2*t+1:= by
 let R:= Icc (-(t:ℤ)) t; have he : cent (0:Per N) t ⊆ R.image (fun i:ℤ=> (i:Per N)):=by
   intro x h; have ht:= (cent_at ..).1 h; unfold delta1 at ht; rw [sub_zero] at ht; exact mem_image.mpr ⟨x.valMinAbs,mem_Icc.mpr (by omega),ZMod.coe_valMinAbs _⟩
 refine (card_le_card he).trans ((card_image_le).trans ?_); rw [show R.card=_ from Int.card_Icc _ _]; omega
lemma Near.enlarge{d s:ℝ}(h:Near F r d A)(p:r≤t)(g:d≤s):Near F t s A:=by obtain ⟨U,h,e⟩:=h; exact ⟨U,h.up p,e.trans g⟩
def revCost (n:ℕ):ℝ:=2*n+1
lemma slice_limit {n:ℕ}{b:ℝ}{S: Finset (Per N)}(T:Op I → Op I) (h: S ⊆ cent 0 n)(s:0 ≤ b) (q:∀ i∈ S, ‖T (swipe F i A)‖≤b): ‖∑ i∈ S,T (swipe F i A)‖ ≤ revCost n*b:=by
 apply le_trans (norm_sum_le ..) ((sum_le_sum (fun i hi=>q i hi)).trans ?_); rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ s; unfold revCost; exact_mod_cast (card_le_card h).trans (cent_card ..)
abbrev young (N:Side)(t n:ℕ):= cent (0:Per N) n \ cent 0 t
lemma Near.restrict{d s:ℝ}(h:Near F t d A)(g:r ≤ t)(q:0≤d)(p:0≤s)(u:∀ i∈ young N r t, ‖swipe F i A‖≤s): ∃ X:Op I, Span F r X∧ ‖A-X‖ ≤ d + revCost t*(s+d):=by
 obtain ⟨U,h,e⟩:=h; let R:= cent (0:Per N) r; let X:= ∑ i∈R,swipe F i U; refine ⟨X,fun i j v=>?_,?_⟩
 · unfold X; rw [Matrix.sum_apply]; apply sum_eq_zero; intro d hd; rw [swiped,if_neg]; rintro rfl; apply not_le.mpr v; have ht:=(cent_at ..).1 hd; unfold delta1 at ht; rw [sub_zero] at ht; rw [d_sym]; exact ht
 apply (norm_sub_le_norm_sub_add_norm_sub _ U _).trans (add_le_add e ?_); let f:= young N r t; rw [show U-X=∑ i∈ f,swipe F i U from ?_]
 · apply slice_limit (F:=F) (A:=U) id sdiff_subset (add_nonneg p q); intro i z; apply (norm_le_norm_sub_add (swipe F i U) (swipe F i A)).trans; rw [norm_sub_rev,swipe_sub,add_comm]; exact add_le_add (u i z) ((swipe_bill ..).trans e)
 rw [sub_eq_iff_eq_add]; exact ((sum_sdiff (show R ⊆ cent (0:Per N) t from fun i y=> (cent_at ..).2 (((cent_at ..).1 y).trans g))).trans h.swipe).symm -- tune
end YM.CF.BProof.Bias
