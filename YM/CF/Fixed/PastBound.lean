import YM.CF.Fixed.MatchAngle

/-!
# Pressure with explicit pivot-Haar costs off Lace

Both `totalTitle` and `flagTitle` are exponents. The latter saves one half
flag cost. Also still pays all the indicated face costs, simultaneously. The
result has an explicit residual count of at most four missing Haar powers.
No replicated positivity is assumed here. Nor is `past` a probability density.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Extensive
open Function Filter MeasureTheory Lattice Finset Wilson
open scoped BigOperators Topology ENNReal InnerProductSpace Matrix.Norms.Frobenius
open Lat SU Cube Fock Skye Scree Girt Graph Pivots RG Precision PathData
variable {N:Side} {P:GramM N}{u t v k a b m x d h c:ℝ}
section lower
variable {F:Clip}{β T:ℝ}(p:0 ≤ T)(V:0 ≤ β)(i:0<u)(e:k≤β*(F.direct*u^2/2))(l:k≤β*(F.linear*T*u))(z:0≤k)
include p V i e l z
lemma local_slot (r:ℝ)(h:0≤r) : k*(r/u)-k ≤ β*clipped F T r := by
  unfold clipped; by_cases g:r≤u
  · have he:= (div_le_one i).2 g; have H:k*(r/u)≤k:=mul_le_of_le_one_right z he; apply (sub_nonpos.mpr H).trans; split_ifs
    · exact mul_nonneg V (div_nonneg (mul_nonneg F.quadratic_pos.le (by positivity)) (by positivity))
    exact mul_nonneg V (mul_nonneg (mul_nonneg F.tail_pos.le p) h)
  split_ifs
  · refine (sub_le_self _ z).trans ((mul_le_mul_of_nonneg_right e (by positivity)).trans ?_)
    have ht : u ≤ r:= le_of_lt (lt_of_not_ge g |> id) -- tune g not≤, lt
    calc β*(F.direct*u^2/2)*(r/u)= β*(F.direct*(u*r)/2) := by field_simp
         _ ≤ β*(F.direct*r^2/2) := by rw [sq]; gcongr; exact F.quadratic_pos.le
  exact (sub_le_self _ z).trans ((mul_le_mul_of_nonneg_right l (by positivity)).trans_eq (by field_simp))
end lower
section principle
variable {G:Gauge}{F:Clip}{T:BudgetPoint}{R:PathData G}{B C L K β w:ℝ}
local notation "H_" => Fintype.card (Face (Per N))

def totals (G:Gauge) (U: Config G N)(u:ℝ):ℝ:= ∑ i:Face (Per N), G.chord (faceValue U i)/u
lemma totals_pull (U:Config G N)(u:ℝ)(s:Signed) : totals G (pull s 0 U) u=totals G U u := by
  simp only [totals, Face.send_price U _ s 0 G.chord G.chord_inv (fun p q=> G.chord_conj q p)]
  let e:Equiv.Perm (Face (Per N)):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send ..,Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩
  exact Equiv.sum_comp e (fun i=> G.chord (faceValue U i)/u)

def totalTitle(n:Side)(k t β C L:ℝ):= (Fintype.card (Face (Per n)):ℝ)*k + taxY n β t C L
def flagTitle(n:Side)(k t β w C L:ℝ):= totalTitle n k t β C L - β*(w*t^2)/2
variable (i:0<u)(X:R.Bounds F B C L)(V:0 ≤ β)(e:k≤β*(F.direct*u^2/2))(l:k≤β*(F.linear*T.threshold*u))(z:0≤k)
include i X V e l z
lemma ownTitle(U:Config G N): k*totals G U u - totalTitle N k T.threshold β C L ≤ R.inChannels F T β U := by
  have hp(H:Config G N)(K:Face (Per N)) : k*(G.chord (faceValue H K)/u)-k≤β*R.baseTerm F T H K := by
    apply le_trans (local_slot T.threshold_pos.le V i e l z _ (G.chord_nonneg _)); apply mul_le_mul_of_nonneg_left _ V; unfold baseTerm; apply le_add_of_nonneg_right; split <;> positivity
  have he(s: Signed) : k*totals G U u-totalTitle N k T.threshold β C L≤R.principal F T β (pull s 0 U) := by
    let H:=pull s 0 U
    have ht:k*totals G H u - ↑(Fintype.card (Face (Per N)))*k≤β*∑ i:Face (Per N),R.baseTerm F T H i:=by
      have he:= sum_le_sum (s:=univ) fun v _=> hp H v; rw [sum_sub_distrib, ←mul_sum,←mul_sum, sum_const,card_univ,nsmul_eq_mul] at he; exact he
    have p':totals G H u=totals G U u:=totals_pull ..; rw [p'] at ht
    obtain ⟨h,h'⟩:= oath X T H; rw [PathData.principal]; unfold totalTitle taxY; apply le_trans _ (add_le_add (mul_le_mul_of_nonneg_left (add_le_add_right (neg_le_of_abs_le h) _) V) (neg_le_of_abs_le h')); linarith [ht] -- tune h explicit ordering and H
  apply le_trans _ (mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) fun v _=> he v) (show 0≤ (Fintype.card Signed:ℝ)⁻¹ by positivity)); simp only [sum_const,nsmul_eq_mul,card_univ]; rw [inv_mul_cancel_left₀ (show (Fintype.card Signed:ℝ)≠0 by positivity)]
omit e l
variable (he:2*k≤β*(F.direct*u^2/2))(hl:2*k≤β*(F.linear*T.threshold*u))(hv:0≤w)(hw:w≤F.linear)
include he hl hv hw
lemma earnFlag(U:Config G N)(h:flags T.threshold U≠∅): k*totals G U u - flagTitle N k T.threshold β w C L ≤ R.inChannels F T β U := by
  have hp:= fullH X T U hv hw V h
  have ht:= ownTitle i X V he hl (show 0≤2*k by positivity) U; unfold flagTitle totalTitle; unfold totalTitle at ht; unfold kinetic at hp; linarith

omit i X V he hl hv hw z
lemma has_axes : Nonempty PlaqAxes:=⟨⟨(0,1),by decide⟩⟩
private def defaultMark (e: Link N) : Face (Per N):= if h:Active e then mark e h else (0, Classical.choice has_axes)
private lemma select_log (U:Config G N) (u:ℝ)(h:0≤u) :
    ∑ i∈pivots N,G.chord (toothMark G i U)/u ≤ totals G U u := by
  classical
  let f(i:Face (Per N)):=G.chord (faceValue U i)/u; let A:= pivots N; let S:= A.image defaultMark
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (f:=f) (subset_univ S) (fun i _ _=> div_nonneg (G.chord_nonneg _) h)); unfold S; rw [sum_image]; swap
  · intro i hi j hj e; unfold defaultMark at e; rw [dif_pos (show Active i from (mem_filter.mp hi).2),dif_pos (show Active j from (mem_filter.mp hj).2)] at e; exact mark_inj _ _ _ _ e
  exact le_of_eq (sum_congr rfl fun i hi=> by unfold f toothMark defaultMark; simp_rw [dif_pos (show Active i from (mem_filter.mp hi).2)])

def diminish (u k:ℝ)(U:Config G N):=∏ i∈pivots N, saltWeight G u k (toothMark G i U)
lemma dim_eye (u k:ℝ) (U:Config G N): 0 ≤ diminish u k U := Finset.prod_nonneg fun _ _=>(Real.exp_pos _).le
lemma dim_cont (u k:ℝ): Continuous (diminish (N:=N) (G:=G) u k):= continuous_finsetProd _ fun i _=> (salt_cont ..).comp (toothMark_cont G i)
lemma dim_title(u Z k:ℝ)(h:0≤u)(c:0≤k)(U:Config G N)(p:k*totals G U u-Z ≤ R.inChannels F T β U):
    Real.exp (-R.inChannels F T β U) ≤ Real.exp Z * diminish u k U:=by
  unfold diminish saltWeight; rw [←Real.exp_sum,←Real.exp_add, ←mul_sum]; exact Real.exp_le_exp.mpr (by nlinarith [select_log U u h])
lemma integrable_dim (u k:ℝ): Integrable (diminish u k) (prior G N):=(dim_cont u k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma mass_dim (H:(∫ x:G.El,saltWeight G u k x∂G.probHaar)≤B) :
    ∫ x:Config G N,diminish u k x∂prior G N ≤ B^(pivots N).card := by
  unfold diminish; rw [mark_integral G _ (salt_cont G u k)]; exact pow_le_pow_left₀ (integral_nonneg (fun x=>(Real.exp_pos _).le)) H _
end principle
end YM.CF.Fixed.Extensive
