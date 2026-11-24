import YM.SU5.FiniteGaugeData.Tower.GermEngine
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Filter Metric
open scoped Topology NNReal
namespace Carousel
/- Generic (not necessarily a translation action). D_h oriented estimates on a coherent refining geometry with Ratio L. Lap with h^(1+α), α ∈ (0,1), on all sites/directions (choose n beyond any needed readiness by a later credit transfer; here consume ∀ n). From it recover simultaneously all lifted slope estimates, polynomial in the inverse-pad billing because these estimates all *linear* in that input first budget. Does not attempt to estimate heat from Lap. Need bounded operators as another fare. -/
variable (M: Mesh) {α:ℝ} {X G I:Type*} [NormedAddCommGroup X][NormedSpace ℝ X][AddCommGroup G] (D:I→ℕ→G) (u:X) {f:G→X}
variable (C:ℝ)(p:0<α)(e:α<1)
local notation "σ" n:max=> (mill M n:ℝ)
def PaidR : Prop :=∀ (i:I)(n:ℕ), M.L • D i (n+1)= D i n
local notation "Z" => PaidR
structure Spark (A:ℝ)(f:G→X)(α:ℝ):Prop where
 pos : 0≤ A
 norms (x:G) :‖f x‖≤ A
 laps (x:G)(i:I)(v:ℕ) : ‖f (x+D i v)+ f (x-D i v)-(2:ℝ) • f x‖ ≤ A * (σ v)^(1+α:ℝ)
lemma gear_pos (n:ℕ): 0<(mill M n:ℝ):=mill_pos ..
local notation "Λ"=> (M.L:ℝ)
lemma gear_inc :1<(M.L:ℝ):=by exact_mod_cast M.Llarge
lemma speedup (n:ℕ) : (mill M n:ℝ)=Λ*(mill M (n+1):ℝ):=by have v:= mill_finer M n (n+1) (by omega); norm_num at v; exact_mod_cast v.symm
lemma wheelBase (v:ℕ)(r:ℝ): (σ v)^r= (σ 0)^r*(Λ⁻¹^r)^v:=by
 have hx:0<(mill M v:ℝ):=gear_pos ..; have h:=gear_inc M; have ht:0<Λ:=zero_lt_one.trans h
 have p: (mill M v:ℝ)=↑(mill M 0)/(Λ^v):=by simp [mill]
 rw [p,Real.div_rpow (by exact (gear_pos ..).le) (pow_pos ht _).le,Real.inv_rpow (by positivity),←Real.rpow_pow_comm ht.le,inv_pow,div_eq_mul_inv]
abbrev coinB(α:ℝ):ℝ:=(M.L:ℝ)⁻¹^α
local notation "κ" => coinB M α
lemma κpos (α:ℝ):0< coinB M α:= Real.rpow_pos_of_pos (inv_pos.mpr (zero_lt_one.trans (gear_inc M))) _
lemma κ_small (p:0<α):coinB M α<1:= Real.rpow_lt_one (inv_nonneg.mpr (zero_le_one.trans (gear_inc M).le)) (inv_lt_one_of_one_lt₀ (gear_inc _)) p
lemma rez (v j:ℕ)(α:ℝ): (σ (v+j))^α= (σ v)^α*(coinB M α)^j:=by
 rw [wheelBase M, pow_add (Λ⁻¹^α),wheelBase M v α,mul_assoc]
lemma sideScale (v:ℕ) (t:ℝ): (σ v)^t=(Λ)^t*(σ (v+1))^t:=by
 have ht:=gear_pos M (v+1); rw [speedup M v,Real.mul_rpow (by positivity) ht.le]
-- first quotient.
variable (U:PaidR M D) (F:Spark M D C f α)
local notation "d" k:max h:max=> D k h
local notation "AH" h:max=> (σ h)^α
def stroll (F: G→X)(i:I)(v:ℕ)(x:G):X:= F (x+D i v)-F x -- shadow T
local notation "S" F:max i:max v:max=> stroll D F i v
noncomputable abbrev boltDiff (i:I)(v:ℕ)(f:G→X): G→X:= ((σ v)⁻¹:ℝ) • stroll D f i v
local notation "G'" i:max v:max => boltDiff M D i v f
include F
lemma tapV (i:I)(x:G)(v:ℕ): ‖(G' i v) (x+D i v) -(G' i v) x‖≤ C*(σ v)^α:=by
 let h:= D i v; let t:= (σ v); have h0:=gear_pos M v; let X(k):=f k
 have hp: ‖(stroll D f i v (x+D i v))-(stroll D f i v x)‖≤ _:= Eq.trans_le (congrArg norm (show _= f (x+D i v +D i v)+ f (x+D i v-D i v)-(2:ℝ) • f (x+D i v) from by unfold stroll; rw [two_smul ℝ]; simp; abel)) (F.laps (x+D i v) i v)
 unfold boltDiff; simp only [Pi.smul_apply]; rw [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr h0.le)]; refine (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq ?_; rw [Real.rpow_add h0,Real.rpow_one]; field
omit F
lemma creep {G E:Type*}[AddCommGroup G][NormedAddCommGroup E](X:G→E)(a t:G)(p:∀ x,‖X (x+t)-X x‖≤ C)(u:ℕ): ‖X (a+u • t)-X a‖≤ u*C:=by
 induction u with
 | zero=> simp
 | succ j h=>
    refine (norm_sub_le_norm_sub_add_norm_sub _ (X (a+j • t)) _).trans ?_; rw [succ_nsmul,←add_assoc] -- remove placeholder
    have v:=add_le_add (p (a+j • t)) h; exact v.trans_eq (by push_cast; ring)
include U F
local notation "Lap" k:max=>D k
lemma drift_v (i:I)(x:G)(v:ℕ): ‖(G' i v) x-(G' i (v+1)) x‖≤Λ*C* (σ (v+1))^α:=by
 let m:=M.L; let a:=D i (v+1); let A:= (σ v); let r:=(σ (v+1)); have ht:= gear_inc M; have hu:0<Λ:=by positivity
 have h:=speedup M v; have hx:0<A:=gear_pos ..; have hy:0<r:=gear_pos ..; let e:=Λ*C* (AH (v+1)); let g:= boltDiff M D i (v+1) f
 have hg(j:ℕ): ‖g (x+j • a)- g x‖ ≤ (j:ℝ)*(C*(AH (v+1))):= creep _ g x a (fun x=>tapV M D C F i x (v+1)) j
 have hp:Λ • ((G' i v) x)=∑ i∈ Finset.range M.L,g (x+i • a):=by
    have he(j:ℕ): (∑ k∈Finset.range j,g (x+k • a))=(r⁻¹:ℝ) • (f (x+j • a)-f x):=by
       induction j with
       | zero=> simp
       | succ j q=> rw [Finset.sum_range_succ,q]; change _ + r⁻¹ • (f (x+j • a+a)-f (x+j • a))= _; rw [succ_nsmul,←add_assoc,←smul_add]; abel
    rw [he, show M.L • a= D i v from U ..]; change Λ • (A⁻¹ • (f (x+D i v)-f x)) = _; rw [smul_smul, show Λ *A⁻¹=r⁻¹ from (by unfold A; rw [h]; unfold r; field)] 
 have hT:‖Λ • ((G' i v) x-g x)‖ ≤ Λ*e:=by
    rw [smul_sub,hp,Nat.cast_smul_eq_nsmul ℝ, show M.L • g x=∑ i∈Finset.range M.L,(fun _=>g x) i from (by simp only [Finset.sum_const,Finset.card_range]), ←Finset.sum_sub_distrib]
    refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun _=> e) (fun k v=> (hg k).trans ?_)) ?_)
    · exact le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ)|>.mpr (le_of_lt (Finset.mem_range.mp v))) (mul_nonneg F.pos (by positivity))) (mul_assoc _ _ _).symm.le
    simp; -- rw sum_const nat.cast
 rw [norm_smul, Real.norm_of_nonneg hu.le] at hT; exact (mul_le_mul_iff_right₀ hu).mp hT
local notation "Φ" i:max k:max=> boltDiff M D i k f
noncomputable def roseMax (α:ℝ):ℝ:= (M.L:ℝ)/(1-coinB M α)
local notation "fmax" => roseMax M α
omit U F in
lemma rosePos(p:0<α):0<roseMax M α:=div_pos (zero_lt_one.trans (gear_inc M)) (sub_pos.mpr (κ_small M p))
variable [CompleteSpace X]
noncomputable abbrev gradPrice (i:I)(x:G):=limUnder atTop (fun n=> boltDiff M D i n f x)
include p
lemma quorum (i:I)(x:G)(v:ℕ): Tendsto (fun n:ℕ=> boltDiff M D i n f x) atTop (𝓝 (gradPrice (f:=f) M D i x)) ∧ ‖(gradPrice (f:=f) M D i x)-(Φ i v) x‖≤ C*fmax*(σ v)^α:=by
 let A:=fun t=> boltDiff M D i t f x; let E:=Λ*C*AH v
 have ht:= κ_small M p; have hi:0<κ:=κpos ..; have he:= (zero_lt_one.trans (gear_inc M)); have hy:= F.pos;
 let X(n:ℕ):= A (n+v); have H(n:ℕ):dist (X n) (X (n+1))≤ E*κ^n:=by
    unfold X; rw [Nat.add_right_comm n 1 v, dist_eq_norm]; refine (drift_v M D C U F i x (n+v)).trans ?_
    apply le_trans (le_of_eq (?_ : Λ*C*AH (n+v+1)=(Λ*C*AH v)*(κ)^(n+1)))
    · rw [pow_succ]; exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) ht.le) (by have v0:=gear_pos M v; positivity)
    rw [Nat.add_comm n v,Nat.add_assoc,rez,mul_assoc]; ring -- congr 0 ??? remove
 obtain ⟨y,g⟩:= cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric κ E ht H)
 have h':=dist_le_of_le_geometric_of_tendsto₀ κ E ht H g; have hx:Tendsto A atTop (𝓝 y):=(tendsto_add_atTop_iff_nat v).mp g
 change Tendsto A atTop (𝓝 (limUnder atTop A)) ∧ ‖limUnder _ A-A v‖≤_; rw [hx.limUnder_eq,←dist_eq_norm,dist_comm]; constructor; · exact hx
 change dist (A (0+v)) y ≤ _ at h'; rw [zero_add] at h'; calc
    dist ((Φ i v) x) _ ≤ _:= h'
    _ = C*fmax* (AH v):=by unfold E roseMax; ring
-- pay upper constant.T.Out.
noncomputable abbrev expense (α:ℝ):ℝ:= (2/(mill M 0:ℝ))+2*roseMax M α*(mill M 0:ℝ)^α
omit U F in
lemma expense_pos:0<expense M α:= by unfold expense; have h:= gear_pos M 0; have ht:= rosePos M p; positivity
lemma overhead(i:I)(x:G)(v:ℕ): ‖gradPrice (f:=f) M D i x‖≤ C*expense M α∧ ‖(Φ i v) x‖≤ C*expense M α:=by
 let E':= gradPrice (f:=f) M D i x; let t:= (σ 0); have ht:0<t:=gear_pos ..; let w:= fmax; let hx:t>0:=ht; have he:= rosePos M p
 let W(v:ℕ):=(Φ i v) x
 have hV:‖W 0‖≤ C*(2/t):=by
    unfold W boltDiff; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by change 0≤t⁻¹; positivity)]; refine le_trans (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (F.norms _) (F.norms _))) (inv_nonneg.mpr ht.le)) ?_; change t⁻¹*(C+C)≤ _; exact le_of_eq (by ring)
 have hp(v:ℕ): ‖E'-W v‖≤C*w*(t^α):= (quorum M D C p U F i x v).2.trans (by rw [wheelBase]; refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg F.pos he.le); exact mul_le_of_le_one_right (by change 0≤t^α; positivity) (pow_le_one₀ (κpos ..).le (κ_small M p).le))
 have hu(E Y:X):‖E‖≤ ‖E-Y‖+‖Y‖:= Eq.trans_le (congrArg norm (show E=E-Y+Y from (by abel))) (norm_add_le ..)
 let Z':= C*w*t^α; have hf:C*w*(t^α)=Z':=rfl; have hw:‖E'‖≤ Z'+C*(2/t):=(hu E' (W 0)).trans (add_le_add (hp 0) hV)
 have h:‖W v‖≤ Z'+‖E'‖:= (hu (W v) E').trans (add_le_add_left (((norm_sub_rev (W v) E').le).trans (hp v)) _) -- le order tune
 unfold E' Z' t w at hw; unfold W E' Z' t w at h; unfold expense; have u:0≤C*fmax*(AH 0):= mul_nonneg (mul_nonneg F.pos he.le) (by unfold t at ht; positivity); constructor<;> linarith
#print axioms overhead
end Carousel
end YM.CF.Buffered.Afterglow.Tower.MeshClock
