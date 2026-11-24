import YM.SU5.Registration.Ink.Railing
import YM.SU5.Selected.RootWitness
import YM.SU5.Registration.LineUp.Forms

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap
abbrev postcard (S : OS.Semigroup H timeAxis) (v:E4) : H.Op:= M S (SEP timeAxis v).val * S.E (YM.time v).toNNReal
lemma add_time (v w:E4) : YM.time (v+w)=YM.time v+YM.time w:=rfl
lemma card_journey (v w:E4) (p:0≤YM.time v)(q:0≤YM.time w): postcard S (v+w)= postcard S v * postcard S w:=by
 unfold postcard; rw [map_add]; change M S ((SEP timeAxis v).val+ (SEP timeAxis w).val) * _=_; rw [←tgo,add_time,Real.toNNReal_add p q,S.time]; let u:= M S (SEP timeAxis v).val; let t:= M S (SEP timeAxis w).val; let c:= S.E (YM.time v).toNNReal; let d:= S.E (YM.time w).toNNReal; change u*t*(c*d) = u*c*(t*d); simp only [mul_assoc]; rw [← mul_assoc t, (SatinRegistration.heat_commutes S _ _).symm.eq, mul_assoc c] -- let aliases
lemma card_zero : postcard S 0=1:=by unfold postcard; rw [show YM.time 0=0 from rfl,map_zero]; simp [tini,S.eZero]; try rfl
lemma card_norm (v:E4) : ‖postcard S v‖ ≤ 1:= (norm_mul_le ..).trans (by exact (mul_le_of_le_one_left (norm_nonneg _) (tcostO S _)).trans (S.shrinks ..))
lemma action_pc (v:E4)(y:H): ‖postcard S v y‖=‖S.E (YM.time v).toNNReal y‖:=tcost ..
lemma heat_point (v:H)(t:ℝ≥0): ‖S.E t v‖≤‖v‖:=by simpa using (S.E t).le_of_opNorm_le (S.shrinks t) v
lemma heat_antitone (v:H)(r s:ℝ≥0)(h:r≤ s) : ‖S.E s v‖≤‖S.E r v‖:=by rw [← tsub_add_cancel_of_le h,S.time]; exact heat_point ..
private lemma heat_horiz {v:H} {s:ℝ≥0}(hs:0<s)(h:‖S.E s v‖=‖v‖) : ∀ t,S.E t v = v:=by
 have he(u:ℝ≥0)(h':u≤ s): ‖S.E u v‖=‖v‖:= (heat_point S _ u).antisymm (by nth_rw 1 [←h]; exact heat_antitone S _ u s h')
 have hp(u:ℝ≥0)(h':u≤ s) : S.E u v=v:=by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) (heat_point ..)
    have hu:= he (u/2) ((half_le_self (zero_le)).trans h'); -- ℝ≥0 lemma
    rw [← add_halves u, S.time, ContinuousLinearMap.comp_apply,S.swing, inner_self_eq_norm_sq,hu]
 have hi (n:ℕ) : ∀ t:ℝ≥0,t≤ n • s → S.E t v=v:=by
    induction n with
    | zero=> intro t h; rw [zero_smul] at h; rw [h.antisymm zero_le, S.eZero]; rfl
    | succ n ih=>
      intro t h; by_cases z:t≤ s; · exact hp t z
      have hx: t-s≤ n • s:= tsub_le_iff_left.mpr (by rw [add_comm]; simpa [add_smul] using h) -- abb
      rw [← tsub_add_cancel_of_le (le_of_not_ge z), S.time, ContinuousLinearMap.comp_apply,hp s le_rfl]; exact ih (t-s) hx
 intro t; obtain ⟨n,ht⟩:= exists_nat_gt (t/s); apply hi n t; rw [nsmul_eq_mul]; exact (div_le_iff₀ hs).1 ht.le
lemma static_pair (y:H) (r:E4) (p:0<YM.time r) : postcard S r y=y ↔ (∀ v:ℝ≥0, S.E v y=y) ∧ M S (SEP timeAxis r).val y = y:=by
 have he:0 < (YM.time r).toNNReal:= Real.toNNReal_pos.mpr p
 constructor
 · intro t; have h:‖S.E (YM.time r).toNNReal y‖=‖y‖:= (action_pc ..).symm.trans (congrArg norm t); let a:= heat_horiz S he h; refine ⟨a,?_⟩
   nth_rw 1 [← a (YM.time r).toNNReal ]; exact t -- parsing!
 rintro ⟨a,t⟩; change M S _ (S.E _ y)=y; rw [a,t]
/-- Space stabilizer. ignore time coordinate E4 even if pay very large Pe h charges. -/
def unmoved (x:H) : AddSubgroup E4 where
 carrier :={ r | M S (SEP timeAxis r).val x=x }
 add_mem' {a b} p q:=by
    change M S (SEP timeAxis (a+b)).val x=x; rw [map_add]; change M S ((SEP timeAxis a).val+(SEP timeAxis b).val) x=x; rw [←tgo]; change M S _ (M S (SEP timeAxis b).val x)=x; rw [show M S (SEP timeAxis b).val x=x from q]; exact p
 zero_mem':=by change M S (SEP timeAxis 0).val x=x; rw [map_zero]; exact congr($((tini S)) x)
 neg_mem' {a} p:=by
    change M S (SEP timeAxis (-a)).val x=x; let c:= (SEP timeAxis a).val; rw [map_neg]; change M S (-c) x = _; nth_rw 1 [← show M S c x=x from p]; exact DFunLike.congr_fun ((tgo S (-c) c).trans ((congrArg (M S) (neg_add_cancel c)).trans (tini S))) x
lemma unmoved_closed (x:H): IsClosed (S |> fun _ =>(unmoved S x:Set E4)):= isClosed_eq ((S.unit.moves x).comp (continuous_subtype_val.comp (SEP timeAxis).continuous)) continuous_const
section mean
variable {I:Type}[Fintype I][Nonempty I]
abbrev Priced (f:I→E4):= Dense (AddSubgroup.closure (range f):Set E4)
def collection (f:I→E4) : H.Op:=(Fintype.card I :ℂ)⁻¹ • ∑ i,postcard S (f i)
local notation "C" f:max=> collection S f
local notation "n"=> Fintype.card I
lemma collection_norm (f:I→E4) : ‖C f‖≤1:= by
 classical
 have hn:0<(n:ℝ):= by exact_mod_cast Fintype.card_pos
 unfold collection; rw [norm_smul,norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn, mul_one]; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> card_norm S (f i))).trans_eq (by simp))
lemma collection_here (f:I→E4)(x:H): (C f) x=(n:ℂ)⁻¹ • ∑ i, postcard S (f i) x:=by classical rw [collection,smul_apply, ContinuousLinearMap.sum_apply]
lemma collection_fixes (f:I→E4)(x:H) : (C f) x=x ↔ ∀ i,postcard S (f i) x=x := by
 classical
 have h(i:I): ‖postcard S (f i) x‖ ≤ ‖x‖:= (action_pc ..).trans_le (heat_point ..)
 have hx:n≠0:= Fintype.card_pos.ne'; have he:(n:ℂ)≠0:= Nat.cast_ne_zero.mpr hx
 rw [collection_here, inv_smul_eq_iff₀ he]
 constructor
 · intro t i; apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) (h i)
   let c:=‖x‖^2; let z(i:I):= (inner ℂ (postcard S (f i) x) x).re; change z i = c
   have hz(i:I) : z i ≤ c:= (Complex.re_le_norm _).trans ((norm_inner_le_norm (postcard S (f i) x) x).trans ((mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)).trans_eq (pow_two ‖x‖).symm))
   have ht : ∑ i,z i = n*c:= by
      unfold z; rw [← Complex.re_sum,← sum_inner, t, inner_smul_left]; simp only [map_natCast]; simp_rw [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]; rw [show (inner ℂ x x).re= ‖x‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _]
   by_contra k; apply ne_of_lt (?_ : (∑ i,z i)<n*c) ht
   exact lt_of_lt_of_le (Finset.sum_lt_sum (s:=Finset.univ) (g:=fun _=>c) (fun j _=> hz j) ⟨i,Finset.mem_univ i,(hz i).lt_of_ne k⟩) (by simp)
 intro t; simp_rw[t]; simp [Nat.cast_smul_eq_nsmul]
-- ground criterion along these visits, exact before measure
local notation "Λ" => E4
structure Moored (x:H) : Prop where
  fixed (t): S.E t x=x
  space (t:E4): M S (SEP timeAxis t).val x=x
lemma collection_rest (f:I→E4) (p:Priced f)(h:∀ i,0<YM.time (f i))(x:H): x∈ (C f).eqLocus (1:H.Op) ↔ Moored S x:=by
 change (C f) x=x↔_; rw [collection_fixes]; constructor
 · intro u; refine ⟨((static_pair S x _ (h (Classical.arbitrary I))).1 (u _)).1,?_ ⟩
   intro t; have ht : AddSubgroup.closure (range f) ≤ unmoved S x := (AddSubgroup.closure_le _).mpr (by rintro a ⟨i,rfl⟩; exact ((static_pair S x _ (h i)).1 (u i)).2)
   exact closure_minimal (SetLike.coe_subset_coe.mpr ht) (unmoved_closed S x) (p t)
 intro e i; exact (static_pair S x _ (h i)).2 ⟨e.fixed,e.space _⟩
end mean
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms collection_rest
#print axioms collection_norm
