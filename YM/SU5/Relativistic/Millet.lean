import YM.SU5.Relativistic.Slicer
import YM.SU5.FiniteGaugeData.Pannier.Majus
/-! # Mileage including full conjugation. Keeps silhouette ℓ¹, dirty-site penalty *not* per call. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Finset Lattice Lat Skye Scree Branch Pastry Cube Rush Pannier Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I] (T:Shaft I)
lemma wordCreed (b:Bool)(x:Ket I): ‖x‖≤2*‖creed b x‖:=by
 let v:=basisKet (∅:Finset I); have hp:‖v‖=1:=by simp [v,basisKet]
 let A:=create x; let B:=Fock.remove x; have he:= Flare.snow x v
 have hf(U:FC I) : ‖acts U v‖≤ ‖U‖:=(Graph.spentS I U v).trans_eq (by rw [hp,mul_one])
 have hg:‖B‖= ‖A‖:=norm_star _; have hu:‖A‖=‖creed b x‖:=by cases b; rfl; exact hg.symm -- tune trivial simp
 rw [← hu]; have hx:‖acts A v‖^2+‖acts B v‖^2= ‖x‖^2:=by rw [hp] at he; simpa only [one_pow, mul_one] using he
 nlinarith only [pow_le_pow_left₀ (norm_nonneg _) (hf A) 2, pow_le_pow_left₀ (norm_nonneg _) ((hf B).trans_eq hg) 2, hx,norm_nonneg x,norm_nonneg A]
variable [Nonempty I]
lemma loomBound (h C:ℝ) (u:‖T.sell‖*2 ≤ h)(g:‖T.buy‖*2 ≤ h) (A:FC I)(t:Pays h A C): ‖T.glow A‖ ≤ C:=by
 let W:=quant T.sell; let Z:=quant T.buy; have hx:W*Z=1:=by unfold W Z; rw [←quant_mul,T.payment,quant_one]
 have hz:Z*W=1:=by unfold W Z; rw [←quant_mul,T.pay,quant_one]
 have hp:0≤h:=(show 0≤ ‖T.sell‖*2 by positivity).trans u
 have he(i:Token I): ‖T.glow (use i)‖≤h:=by
    obtain ⟨⟨b,x⟩,p⟩:=i; have hx: ‖x‖≤2:= (wordCreed b x).trans ((mul_le_mul_of_nonneg_left p zero_le_two).trans_eq (mul_one _)); cases b
    · change ‖T.glow (create x)‖≤_; rw [T.glow_up]; exact ((Flare.cost_pe false _).trans ((Flare.opy ..).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))).trans u
    change ‖T.glow (Fock.remove x)‖≤_; rw [T.glow_down]; have hT:‖star T.buy‖=‖T.buy‖:= norm_star _; exact ((Flare.cost_pe true _).trans ((Flare.opy ..).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))).trans (by rw [hT]; exact g)
 have hl(L:List (Token I)):‖T.glow (rollC use L)‖≤ costs h L:=by
    induction L with
    | nil=> simp [rollC,costs,T.glow_nil]
    | cons i l ih=> change ‖T.glow (use i*rollC use l)‖≤h^_; rw [T.glow_mult,List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (he i) ih (norm_nonneg _) hp)
 have hv(x y:Wave I)(B:FC I): inner ℂ x (acts (T.glow B) y)=inner ℂ (acts (star W) x) (acts B (acts Z y)):=by rw [act_inner,←act_mul,←act_mul]; unfold Shaft.glow W Z; rw [mul_assoc] -- tune assoc
 have hh(x y:Wave I):‖inner ℂ x (acts (T.glow A) y)‖ ≤ C*(‖x‖*‖y‖):=by
    rw [hv x y]; change ‖inner ℂ (acts (star W) x) (acts A _)‖≤_
    apply Yep.val; apply t.2 _ _ _ (by positivity)
    intro L; rw [← hv]; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((Graph.spentS I _ _).trans (mul_le_mul_of_nonneg_right (hl L) (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring))
 rw [←Matrix.l2_opNorm_toEuclideanCLM]; refine ContinuousLinearMap.opNorm_le_bound _ t.1 fun x=>?_
 let V:= acts (T.glow A) x; change ‖V‖≤ C*‖x‖; by_cases l:‖V‖=0; rw [l]; exact mul_nonneg t.1 (norm_nonneg _)
 have H:= hh V x; change ‖inner ℂ V V‖≤_ at H; rw [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)] at H; have hg:=lt_of_le_of_ne (norm_nonneg V) (Ne.symm l); nlinarith -- tune norm
open MeasureTheory
private lemma dust_mul(ε:ℝ)(a:0≤ε)(x:Dough I)(k:ℕ): tier ε (x^k).val ≤ (tier ε x.val)^k:=by
 induction k with
 | zero=> simp [white1]
 | succ n ih=> rw [pow_succ,pow_succ]; change tier ε ((x^n:Dough I).val*x.val)≤ _; exact (tier_mul a (x^n) x).trans (mul_le_mul_of_nonneg_right ih (pitch a _))
lemma dust_exp (ε:ℝ) (x:Dough I)(p:0≤ε) : tier ε (exp x).val ≤ Real.exp (tier ε x.val):=by
 let V(k:ℕ):=(k.factorial:ℝ)⁻¹ • x^k; let y:=tier ε x.val; let S(k:ℕ):=(k.factorial:ℝ)⁻¹*y^k
 have hv:Tendsto (fun k=>∑ i∈range k,V i) atTop (𝓝 (exp x)):=by rw [congrFun (exp_eq_tsum ℝ)]; exact HasSum.tendsto_sum_nat (Summable.hasSum ((norm_expSeries_summable' (𝕂:=ℝ) x).of_norm)) -- tune
 have he:Tendsto (fun k=> ∑ i∈range k,S i) atTop (𝓝 (Real.exp y)):=by rw [Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]; exact HasSum.tendsto_sum_nat (Summable.hasSum (norm_expSeries_summable' (𝕂:=ℝ) y).of_norm) -- tune
 apply le_of_tendsto_of_tendsto (((Bellprep ε).tendsto _).comp hv) he; apply Eventually.of_forall; intro k; change tier ε ((∑ i∈_,V i)).val ≤ _
 let M:=Dough I
 rw [show (∑ i∈range k,V i).val=∑ i∈range k,(V i).val from map_sum (Dough I).subtype V _]; apply (tier_sum p ..).trans; apply sum_le_sum; intro i h; unfold V; rw [show ∀ (A:Dough I)(p:ℝ),(p • A).val=p • A.val from fun _ _=>rfl,whiteℝ,Real.norm_of_nonneg (by positivity)]
 exact mul_le_mul_of_nonneg_left (dust_mul ε p x i) (by positivity)
lemma tank_glow (P:Op I)(h z:ℝ)(S:Finset (LeanV I))(F:ribbon I)(p:0≤h)(g:0≤z)
    (t:∀ i:LeanV I, ‖T.glow (drawT P i)‖≤h*(if i∈S then Real.exp z else 1)) : ‖T.glow (tank P F)‖ ≤ tier h F.val * Real.exp (z*S.card):=by
 let Y(i:LeanV I):= if i∈ S then Real.exp z else 1
 have hp(L:List (LeanV I)):‖T.glow (L.map (drawT P)).prod‖≤ h^L.length*(L.map Y).prod:=by
    induction L with| nil=> simp [T.glow_nil]| cons i l ih=>simp only [List.map_cons,List.prod_cons,List.length_cons,T.glow_mult]; rw [pow_succ']; exact (norm_mul_le ..).trans ((mul_le_mul (t i) ih (norm_nonneg _) ((norm_nonneg _).trans (t i))).trans_eq (by change h*Y i*_= _; ring))
 let K:= T.glow; have H0(M:Type _) [LinearOrder M][Fintype M] (Y:M→ℝ) (S:Finset M)(he:∀ i,Y i=(if i∈S then Real.exp z else 1))(d:Finset M) (L:List M)(e:L=d.sort (·≤·)): (L.map Y).prod ≤ Real.exp (z*S.card):=by
    rw [show (L.map Y).prod=∏ i∈d,Y i from (?_)]
    · simp_rw [he]; rw [prod_ite,prod_const_one,mul_one, prod_const, ←Real.exp_nat_mul, mul_comm z]; apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_right _ g; apply Nat.cast_le.mpr; simp only [filter_mem_eq_inter]; exact card_le_card inter_subset_right
    rw [Finset.prod_eq_multiset_prod,←sort_eq d (·≤·),←e]; rfl
 have H0p(M:Type _) [LinearOrder M][Fintype M] (Y:M→ℝ) (S:Finset M)(he:∀ i,Y i=(if i∈S then Real.exp z else 1))(d:Finset M) (f:M→FC I)(hh:∀ L:List M,‖T.glow (L.map f).prod‖≤ h^L.length*(L.map Y).prod): ‖K (column f d)‖≤ h^d.card*Real.exp (z*S.card):=by
    let L:=d.sort (·≤·); refine (hh L).trans ?_; rw [show L.length=d.card from length_sort (·≤·)]; exact mul_le_mul_of_nonneg_left (H0 M Y S he d L rfl) (by positivity)
 have H(d:Finset (LeanV I)): ‖K (column (I:=LeanV I) (drawT P) d)‖≤ h^d.card*Real.exp (z*S.card):=H0p (LeanV I) Y S (fun _=>rfl) d _ hp
 let V:= (fun s:Finset (LeanV I)=> crumb F.val s • column (I:=LeanV I) (drawT P) s)
 have hs(d:Finset (Finset (LeanV I))):T.glow (∑ i∈d,V i)=∑ i∈d,T.glow (V i):=by induction d using Finset.induction_on with| empty => simp [T.glow_zero]| insert i d l ih=> rw [sum_insert l,T.glow_sum,ih,sum_insert l]
 rw [Scree.tank,show T.glow _= _ from hs univ]; apply (norm_sum_le ..).trans; unfold tier; rw [sum_mul]; apply sum_le_sum; intro i _; unfold V; rw [T.glow_free,norm_smul]; exact (mul_le_mul_of_nonneg_left (H i) (norm_nonneg _)).trans_eq (by ring)
open Graph Peaks Laic RG Tulip
lemma boardG {N:Side}(T':Shaft (Single N))(R:GramM N)(p h v a C:ℝ)(L:Ledger p v h a C R)(A:Op (Single N))(X:Skye.Orbit N)(z:ℝ)(S:Finset (LeanV (Single N)))(u:0 ≤ p)(g:0≤z)(t:∀ i, ‖T'.glow (drawT A i)‖ ≤ p*(if i∈S then Real.exp z else 1)): ‖T'.glow (tank A (R.board X))‖ ≤ Real.exp ((v+v+h)*(Cube.More N).val^4+z*S.card):=by
 let Y:= Graph.actG R X; let F:=fueled R.p R.K X; have he:tier p (R.board X).val ≤ Real.exp ((v+v+h)*(More N).val^4):=by
    change tier p ((exp Y:Dough _).val*F.val)≤ _; rw [add_mul,Real.exp_add]; exact (tier_mul u _ F).trans (mul_le_mul ((dust_exp p Y u).trans (Real.exp_le_exp.mpr (Graph.marks R X L.reg L.slip u))) (Graph.toeF L.force u _) (pitch u F.val) (Real.exp_pos _).le)
 rw [Real.exp_add]; exact (tank_glow T' A p z S _ u g t).trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le)
end YM.CF.Papyrus.Franc
