import YM.CF.Phase.Exact

/-! Compact grouping into coarse supports, with payments scaled before B and ε. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Part m B} {W : Scroll m B c}
def spotHit (m B : Side) (y : Index m) := univ.filter fun S:Stamp m B=> y∈pavilion m B S
def cellHit (m B : Side) (d : ℝ) (w : Stamp m B→ℝ) (x : Index m) := ∑ S∈spotHit m B x, rent d (pavilion m B S)*w S
lemma upperH (a : ℝ) (K : Stamp m B→ℝ) (L : ℝ) (G : ∀ i,hitE a K i≤L) (h : ∀ S,0≤K S) (p : 0 ≤ L) (x : Index m) :
    ∑ S∈spotHit m B x, rent a S*K S ≤ 16*(7*(B.val:ℝ)+1)^4*L := by
  let X := bay (terr _) (address m B x) (7*B.val)
  let Y := spotHit m B x
  have H S (e:S∈Y) : ∃ y∈X,S∈hit0 y := by obtain ⟨i,h,v⟩ := pad_hit x (m:=m) (B:=B) (S:=S) (mem_filter.mp e).2; exact ⟨i,(bay_mem _).mpr v,mem_filter.mpr ⟨mem_univ _,h⟩⟩
  let v S := rent a S*K S
  have hp S : 0 ≤ v S := mul_nonneg (rent_pos ..).le (h S)
  have ht : ∑ S∈Y, v S ≤ ∑ i∈X, hitE a K i := by
    calc
      _ ≤ ∑ S∈Y, ∑ i∈X, (if i∈S then v S else 0) := sum_le_sum fun S h=> by
        obtain ⟨y,p,f⟩ := H S h; have he : y∈S := (mem_filter.mp f).2; exact (le_of_eq (if_pos he).symm).trans (single_le_sum (f:=fun i=> if i∈S then v S else 0) (fun i _=>by split <;> simp [hp]) p)
      _ ≤ _ := by
        rw [sum_comm]; apply sum_le_sum; intro i h; rw [←sum_filter]; apply sum_le_sum_of_subset_of_nonneg _ (fun S _ _=> hp S); intro S e; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp e).2⟩
  apply ht.trans ((sum_le_sum (fun i _=>G i)).trans ?_); rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ p; have hk := reach (address m B x) (7*B.val); push_cast at hk; exact hk
lemma pay_scale {r t : ℝ} (g : 0≤r) (p : r*21^4 ≤ t*(B.val:ℝ)) (S : Stamp m B) (h : Branch.Grove (terr _) S) :
    rent r (pavilion m B S) ≤ Real.exp (r*21^4)*rent t S := by
  unfold rent; rw [←Real.exp_add]; apply Real.exp_monotone
  let V := pavilion m B S
  have hf : 0 < (B.val:ℝ) := by exact_mod_cast B.property
  have he : (V.card:ℝ)*B.val≤21^4*(S.card+B.val:ℝ) := by exact_mod_cast pad_small h
  apply le_of_mul_le_mul_right ?_ hf
  calc
    _ = r*(V.card*B.val:ℝ) := mul_assoc ..
    _ ≤ _ := mul_le_mul_of_nonneg_left he g
    _ = r*21^4*B.val + (r*21^4)*S.card := by ring
    _ ≤ (r*21^4+t*S.card)*(B.val:ℝ) := by
      rw [add_mul (r*21^4), mul_right_comm t]; gcongr
lemma hit_transfer {v : Stamp m B→ℝ} {t r u : ℝ} (g : 0≤r) (p : r*21^4 ≤ t*(B.val:ℝ)) (U : ∀ S,v S≠0→ Branch.Grove (terr _) S) (h : ∀ S,0 ≤ v S) (L : ∀ x, hitE t v x ≤ u) (q : 0≤u) : ∀ x, cellHit m B r v x ≤ Real.exp (r*21^4) * (16*(7*(B.val:ℝ)+1)^4 * u) := by
  intro x; unfold cellHit; apply le_trans _ (mul_le_mul_of_nonneg_left (upperH t v u L h q x) (Real.exp_pos _).le); rw [mul_sum]; apply sum_le_sum; intro S e; rw [←mul_assoc]; by_cases he:v S=0
  · simp [he]
  exact mul_le_mul_of_nonneg_right (pay_scale g p S (U S he)) (h S)
-- take factor c = exp(-a/2*scallop)
def quantile (a : ℝ) (B : Side) : ℝ := Real.exp (-a/2*scallop B)
lemma quantile_pos (a : ℝ) (B : Side) : 0<quantile a B := Real.exp_pos _
lemma short_pay {A d e : ℝ} (h : ScaleK A d W) (he : Budget B e (quantile A B)) (hp : 0 < A) (x) :
    hitE (A/2) (dust W (quantile A B)) x ≤ quantile A B * (d+(way B:ℝ)*d) := by
  apply le_trans _ (mul_le_mul_of_nonneg_left (Scroll.covers h x) he.2.1)
  unfold hitE; rw [mul_sum]; apply sum_le_sum; intro S _; unfold dust
  have hh := (currency h he.1 S none).pos
  split_ifs with k
  · calc
      _ ≤ rent A S*(Scroll.mint W S*quantile A B) := mul_le_mul_of_nonneg_right (rent_up (half_le_self hp.le) _) (mul_nonneg hh he.2.1)
      _ = _ := by ring
  rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hh
  unfold quantile rent; rw [←Real.exp_add]; apply Real.exp_monotone
  have hz : ((scallop B):ℝ)≤S.card := by exact_mod_cast (le_of_not_ge k) -- tune
  nlinarith [mul_le_mul_of_nonneg_left hz hp.le]
lemma room_limit (a d v : ℝ) (pv : 0<v) (h : 0<a) (g : 0≤d) (k : ℝ) : ∃ n:ℕ, ∀ B:Side,n≤B.val→
    Real.exp (k*21^4) * (16*(7*(B.val:ℝ)+1)^4 * (quantile a B*(d +(way B:ℝ)*d))) ≤ v := by
  let w := Real.exp (-a/24); have hw : 0<w := Real.exp_pos _; have hW : w <1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq (B:Side) : quantile a B≤Real.exp a*w^B.val := by
    let b := scallop B; have he : (B.val:ℝ)≤12*b+12 := by exact_mod_cast (show B.val ≤ 12*b+12 by unfold b scallop collar; omega)
    unfold quantile w; rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_monotone; change -a/2*b≤_; nlinarith [mul_le_mul_of_nonneg_left he h.le]
  let V : ℝ := (2*(4/low*98))/Dangle
  have he : 0 ≤ V := by have hp := low_p; have he := angle_pos; unfold V; positivity
  have ht B : (way B:ℝ) ≤ V*B.val+2 := by
    have hx := Nat.ceil_lt_add_one (a:=2*variations B / Dangle) (div_nonneg (mul_nonneg (by norm_num) (variation_pos B).le) angle_pos.le)
    unfold way; push_cast
    apply le_trans (add_le_add_left hx.le 1); unfold variations V; exact le_of_eq (by ring)
  let K : ℝ := Real.exp (k*21^4)*(16*(8:ℝ)^4)* (Real.exp a * (d+(V+2)*d))
  let X := fun n:ℕ=> K*((n:ℝ)^5*w^n)
  have hf : Tendsto X atTop (𝓝 0) := ((summable_pow_mul_geometric_of_norm_lt_one 5 (show ‖w‖<1 by rw [Real.norm_of_nonneg hw.le]; exact hW)).mul_left K).tendsto_atTop_zero
  obtain ⟨n,h⟩ := eventually_atTop.mp (hf.eventually (gt_mem_nhds pv))
  refine ⟨n,?_⟩; intro B c
  have hb : 1 ≤ (B.val:ℝ) := by exact_mod_cast B.property
  apply le_trans _ (show X B.val<v from h _ c).le
  have hc : d+(way B:ℝ)*d ≤ (d+(V+2)*d)*B.val := by
    calc _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right (ht B) g) d
         _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hb g]
  calc
    _ ≤ Real.exp (k*21^4) * (16*(8*(B.val:ℝ))^4 * ((Real.exp a*w^B.val)*((d+(V+2)*d)*B.val))) := by
      gcongr
      · unfold quantile; positivity
      · linarith
      · exact hq B
    _ = _ := by unfold X K; ring
lemma lot_size {u d : ℝ} (hu : 0<u) (hd : 0<d) {k ε : ℝ} (hk : 0 < k) (e : 0<ε) : ∃ q:ℕ, ∀ B:Side,q≤B.val → ∃ r:ℝ, 0<r ∧ ∀ v:ℝ,0≤v→v≤r→ Budget B v (quantile u B) ∧
    -- simultaneous reserve expressed before expansion
    k*21^4≤ u/2 * (B.val:ℝ) ∧ Real.exp (k*21^4)*(16*(7*(B.val:ℝ)+1)^4*(quantile u B*(d+(way B:ℝ)*d)))≤ ε := by
  obtain ⟨n₁,H⟩ := room_limit u d ε e hu hd.le k
  obtain ⟨n₂,V⟩ := exists_nat_gt (k*21^4/(u/2))
  obtain ⟨n,W⟩ := all_room
  refine ⟨n+n₁+n₂,?_⟩; intro B hB
  obtain ⟨E,p,X⟩ := W B (by omega); obtain ⟨r,h,Y⟩ := reserved B _ (quantile_pos u B)
  refine ⟨min r E, lt_min h p,?_⟩; intro v g t; have he := X v g (t.trans (min_le_right ..))
  have hh : (n₂:ℝ) ≤ B.val := by exact_mod_cast (show n₂≤B.val by omega)
  exact ⟨⟨he,(quantile_pos _ _).le,Y v (t.trans (min_le_left ..)) he⟩, by rw [mul_comm (u/2)]; exact (div_le_iff₀ (half_pos hu)).mp (V.le.trans hh), H B (by omega)⟩
lemma kit {u d v k ε : ℝ} (hu : 0<u) (hd : 0<d) (h : ScaleK u d W) (p : Budget B v (quantile u B)) (g : 0<k) (L:k*21^4≤ u/2*(B.val:ℝ)) (F : Real.exp (k*21^4)*(16*(7*(B.val:ℝ)+1)^4*(quantile u B*(d+(way B:ℝ)*d)))≤ε) (i) : cellHit m B k (dust W (quantile u B)) i≤ ε := (hit_transfer g.le L (fun S=>(leavings h p S).2.2.2.2.1) (fun S=>(leavings h p S).2.2.1) (fun x=>short_pay h p hu x) (by unfold quantile; positivity) i).trans F
end YM.CF.Phase
