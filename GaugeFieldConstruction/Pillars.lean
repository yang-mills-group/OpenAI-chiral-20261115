import GaugeFieldConstruction.Pillion
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Fock.Flux
open Finset Function Lattice Wilson RG Branch Skye Scree Cube Tenant Tulip Lat Rush Spire Laic NormedSpace Filter
open YM.Gleam Tree Pastry Vow Rue
open Hake Jet Sault Stax
open Drapes Rill Levier Thera Urn Nacre Flare
open Sour.SliceRoof
open scoped BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
universe u
variable {I:Type u}[Fintype I][LinearOrder I]{P E A B G:Op I}{S:FC I}{U:UNI I}{b h H C D:ℝ}
lemma nilW (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ): translateW P A B U b 1=1:=by unfold translateW; rw [mul_one,wall_couple V h U b]
lemma map_chars (P A B:Op I)(U:UNI I)(b:ℝ) {J:Type*} (s:Finset J)(f:J→FC I): translateW P A B U b (∑ i∈s, f i)=∑ i∈s,translateW P A B U b (f i):=by unfold translateW; rw [mul_sum,sum_mul]
lemma expChar (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(S:FC I): translateW P A B U b (exp S)=exp (translateW P A B U b S):=by
 let L: FC I→+* FC I:=
    { toFun F:= translateW P A B U b F
      map_add' i j:=by unfold translateW; rw [mul_add,add_mul]
      map_zero' :=by unfold translateW; rw [mul_zero,zero_mul]
      map_mul' := translate_prod V h U b
      map_one' := nilW V h U b }
 have ht:Continuous L:= by change Continuous (fun x:FC I=>wall _ _ U b*x*seek _ _ U b); exact (continuous_const.mul continuous_id).mul continuous_const -- tune
 letI : NormedAlgebra ℚ (FC I) := NormedAlgebra.restrictScalars ℚ ℂ (FC I)
 exact map_exp L ht S
lemma char_gauge (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(F:FC I): translateW P A B U b F= translateW P A B 1 b (twist (quantU U) F):=by unfold translateW wall seek; simp only [twist_formula,mul_assoc,show (quantU (1:UNI I)).val=1 from quant_one, star_one,one_mul]; -- tune
lemma act_char (V:Valve P E A B)(h:IsStarProjection P)(b:ℝ)(U:UNI I)(S:FC I)(x:Wave I): acts (wall P A U b) (acts S x)= acts (translateW P A B U b S) (acts (wall P A U b) x):=by rw [←act_mul,←act_mul]; unfold translateW; rw [mul_assoc (wall _ _ _ _*S),couple_wall V h,mul_one]
lemma charter (V:Valve P E A B)(hP:IsStarProjection P){L:Op I} (Z:ribbon I)(p:0≤h)(k:∀ i:LeanV I,‖translateW P A B U b (drawT L i)‖≤h) : ‖translateW P A B U b (tank L Z)‖≤ tier h Z.val:=by
 let F:=translateW P A B U b; have he(L':List (LeanV I)) : ‖F ((L'.map (drawT L)).prod)‖ ≤ h^L'.length:=by
    induction L' with
    | nil=> unfold F; simp [nilW V hP]
    | cons i l ih=> unfold F; rw [List.map_cons,List.prod_cons,translate_prod V hP,List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (k i) ih (norm_nonneg _) p)
 have hz {J:Type u}[Fintype J][LinearOrder J](x:J→FC I)(f:Finset J)(p:∀ l:List J, ‖F (l.map x).prod‖≤h^l.length): ‖F (column x f)‖≤h^f.card:=by have he:=p (f.sort (·≤·)); rw [length_sort] at he; exact he
 have hf(x:Finset (LeanV I)): ‖F (column (I:=LeanV I) (drawT L) x)‖≤ h^x.card:=by
    exact hz (J:=LeanV I) (drawT L) x he
 rw [tank,map_chars]; unfold tier; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [scale_crest,norm_smul]; exact (mul_le_mul_of_nonneg_left (hf i) (norm_nonneg _)).trans_eq (mul_comm ..)
lemma charDG (V:Valve P E A B)(f:IsStarProjection P)(p:0≤h)
  (a:∀ i:I, ‖translateW P A B 1 b (put i)‖≤h)(k:∀ i:I, ‖translateW P A B 1 b (takeF i)‖≤h): ‖translateW P A B U b (dg G)‖≤ h^2*massSite (twist U G):=by
 rw [char_gauge V f,dg_cov]; unfold dg dyad; rw [map_chars]; simp_rw [map_chars _ _ _ (1:UNI I)]; apply (norm_sum_le ..).trans; unfold massSite; rw [mul_sum]; apply sum_le_sum; intro i _; apply (norm_sum_le ..).trans; rw [mul_sum]; apply sum_le_sum; intro j _; rw [scale_crest,norm_smul,translate_prod V f]; exact (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul (a i) (k j) (norm_nonneg _) p)) (norm_nonneg _)).trans_eq (by ring)
lemma charter_bracket (V:Valve P E A B)(f:IsStarProjection P)(p:payFull G C) (k:(1+C)*H ≤ D)(v:0 ≤ H)
 (s:∀ i:I, ‖acts (oneWarp P A U b) (basisKet i)‖ ≤ H)(t:∀ i:I, ‖acts (star (onePeak P B U b)) (basisKet i)‖ ≤ H): ∀ i:LeanV I, ‖translateW P A B U b (drawT G i)‖≤D:=by
 have hf(T:Op I)(i:I)(X:Op I)(h:payFull T C)(u:∀ i:I, ‖acts X (basisKet i)‖≤ H): ‖acts X (acts T (basisKet i))‖ ≤ C*H:=by
    rw [←basis_expand (acts T (basisKet i)),map_sum]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (h.2 i) v); rw [sum_mul]; apply sum_le_sum; intro j _; rw [map_smul,norm_smul,basis_act]; exact mul_le_mul_of_nonneg_left (u j) (norm_nonneg _)
 intro i; unfold drawT; split
 · rw [seekF,prong_p,elevate V f]; apply (cost_pe false _).trans; rw [act_sub,act_one,map_sub]; exact ((norm_sub_le ..).trans (add_le_add (s _) (hf _ _ _ p s))).trans ((by rw [add_mul,one_mul] at k; exact k)) -- tune
 rw [hideF,prong_t,descend V f]; exact ((cost_pe true _).trans (hf _ _ _ p t)).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) v).trans k)
lemma from_local {n:Side}{T:Op (Single n)}(p:PurchB C D b T): ∀ i:Single n, ‖acts T (basisKet i)‖ ≤ D:=by
 intro i; exact (p.1 i.1.1 (basisKet i) (by simp [basisKet]) (fun j x=> by
    rw [basis_apply,if_neg ?_]; intro v; apply x; rw [show j=i from (by tauto)]; exact mem_filter.mpr ⟨mem_univ _,rfl⟩ )).1
lemma charter_creation {n:Side}(i:Single n){P E A B:Op (Single n)}(V:Valve P E A B)(f:IsStarProjection P)
  (p:PurchB C D b (oneWarp P A 1 b))(k:PurchB C D b (star (onePeak P B 1 b))): ‖translateW P A B 1 b (put i)‖≤D∧‖translateW P A B 1 b (takeF i)‖≤D:=by rw [←create_put,←remove_take,elevate V f,descend V f]; exact ⟨(cost_pe false _).trans (from_local p i),(cost_pe true _).trans (from_local k i)⟩

lemma tw_est (T:Op I): |T.trace.re| ≤ massSite T:= by
 apply le_trans (Complex.abs_re_le_norm _); apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; exact single_le_sum (f:=fun j:I=>‖T i j‖) (s:=univ) (fun i _=>norm_nonneg _) (mem_univ i)
lemma tw_mul (T F:Op I)(v:∀ i j, ‖T i j‖≤D) : |(T*F).trace.re| ≤ D*massSite F:=by
 refine (Complex.abs_re_le_norm _).trans ((norm_sum_le ..).trans ?_)
 refine le_trans (sum_le_sum (s:=univ) (g:=fun i:I=>∑ j:I, D*‖F j i‖) (fun i _=>?_)) ?_
 · unfold Matrix.diag; rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j _; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (v i j) (norm_nonneg _)
 rw [sum_comm]; unfold massSite; simp_rw [mul_sum]; rfl -- `rw` leaves ≤ refl?
lemma grams_bound (T:Op I)(p:∀ i, ‖acts T (basisKet i)‖≤D) : ∀ i j:I, ‖(star T*T-1) i j‖≤ D^2+1:=by
 intro i j; have he : (star T*T) i j = inner ℂ (acts T (basisKet i)) (acts T (basisKet j)):= by rw [←basis_act (star T*T) i j, ←basis_inner,act_mul,←act_inner,star_star]
 rw [Matrix.sub_apply,he]; exact (norm_sub_le ..).trans (add_le_add ((norm_inner_le_norm ..).trans (sq D ▸ mul_le_mul (p _) (p _) (norm_nonneg _) ((norm_nonneg _).trans (p j)))) (by simp [Matrix.one_apply, apply_ite]; split <;> simp))
 -- directly gram + one. spectral tax
lemma shot_L {n:Side}{P E A B G:Op (Single n)} {U:UNI (Single n)}(v:Valve P E A B)(h:IsStarProjection P)(a:|b|≤ 1)
  (p:PurchB C D b (oneWarp P A 1 b))(w:D≥0)(x: Wave (Single n))(u:IsStarProjection G)(q:Sea G x): let T:= translateW P A B U b; let Q:= twist U G-P;
  ‖acts (wall P A U b) x‖≤Real.exp (((Real.exp 1 * D)^2+3)* massSite Q):=by
 intro T Q; apply (wall_log v h U b x u q).trans; rw [←Real.exp_add]; apply Real.exp_monotone
 let M:= crownD P A b; let E:= Real.exp 1*D; let L:=star M*M-1; let Z:= massSite Q; have hp(i:Single n) :‖acts M (basisKet i)‖ ≤ E:=by
    unfold M crownD; rw [←Complex.coe_smul,act_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le, show chips P b*A= _ from (show _ = oneWarp P A 1 b by unfold oneWarp; simp)]
    exact mul_le_mul (Real.exp_monotone ((le_abs_self b).trans a)) (from_local p i) (norm_nonneg _) (Real.exp_pos _).le
 have hf: (-b) * Q.trace.re ≤ Z:=by apply le_trans (le_abs_self _) _; rw [abs_mul,abs_neg]; exact (mul_le_mul a (tw_est Q) (abs_nonneg _) zero_le_one).trans_eq (one_mul Z)
 have hx: (L*Q).trace.re ≤ (E^2+1)*Z:= (le_abs_self _).trans (tw_mul _ _ (grams_bound M hp))
 have hi:0≤1+E^2:=by positivity
 have hZ:= usual_mass Q
 change (-b)*Q.trace.re+ (L*Q).trace.re/2 ≤ (E^2+3)*Z; change 0≤Z at hZ
 nlinarith only [hf,hx,hZ,mul_nonneg hi hZ]
section
open Graph
variable [Nonempty I]
-- From Papyrus.Franc.dust_exp. Keep actual tier (50).
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
end
set_option maxHeartbeats 170000 in
lemma charge_struct {N:Side}(R:GramM N)(p h v a C:ℝ)(L:Graph.Ledger p v h a C R)(u:0 ≤ p)(X:Skye.Orbit N): tier p (R.board X).val ≤ Real.exp ((v+v+h)*(More N).val^4):=by
 let Y:= Graph.actG R X; let F:=fueled R.p R.K X; change tier p ((exp Y:Dough _).val*F.val)≤ _; rw [add_mul,Real.exp_add]; exact (tier_mul u _ F).trans (mul_le_mul ((dust_exp p Y u).trans (Real.exp_le_exp.mpr (Graph.marks R X L.reg L.slip u))) (Graph.toeF L.force u _) (pitch u F.val) (Real.exp_pos _).le)
end YM.CF.Fock.Flux
end
