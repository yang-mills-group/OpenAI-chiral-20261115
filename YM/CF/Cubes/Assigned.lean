import YM.CF.Cubes.Projection

/-! Dependence of both assignments on face. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U V : Bkg (Domain m B)} {e : ℝ} (a : Index m)
lemma paint_near {x : Site (Domain m B)} (h : slab m B a x) (s : ArrayF m) (g : Guard U e) (p : 0≤e) (q : Sq) (k : prob q) :
    ‖paint m B U s q x-turn (aligner a U x) (paint m B U s q (snap m B a x))‖ ≤ pot B e := by
  unfold paint; rw [turn_sum]
  let y := snap m B a x; let t := aligner a U x
  have he z : cash m B (snap m B a x) q z=cash m B x q z := by
    unfold cash ticks; simp_rw [picked_iff, voted_slab h]
  simp_rw [he,turn_mul]
  rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans
  have hh (r) (hF:r∈active m B x) (v : Ballot) : ‖freight m B U x r v-turn t (freight m B U y r v)‖≤pot B e := by
    let n := (Fintype.card Lattice.Order:ℝ); have hp : 0<n := Nat.cast_pos.mpr Fintype.card_pos
    unfold freight; rw [turn_mul,turn_sum, ←smul_sub, ←sum_sub_distrib,norm_smul]; change ‖n⁻¹‖*_ ≤ _; rw [Real.norm_of_nonneg (by positivity)]
    apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>show ‖launch m B U x r i v- turn t (launch m B U y r i v)‖ ≤ pot B e by rw [norm_sub_rev]; exact align_one a h hF g p v i))) (by positivity)).trans
    simp only [sum_const,card_univ,nsmul_eq_mul]; change n⁻¹*(n*_)≤_; rw [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]
  calc
    _ ≤ ∑ i, cash m B x q i * pot B e := sum_le_sum fun i _=> by
      have Hp := cash_nonneg m B x q i; by_cases H : i∈bandS m B x q
      · rw [←smul_sub,norm_smul,Real.norm_of_nonneg Hp]; exact mul_le_mul_of_nonneg_left (hh i.1 (spot_hit H) (s i)) Hp
      simp [outside H]
    _ = _ := by rw [←sum_mul, cash_sum _ _ _ _ k,one_mul]
lemma painting_near {x : Site (Domain m B)} (h : slab m B a x) {s : ArrayF m} (g : Guard U e) (p : 0≤e) {q : Sq} (k : prob q) {r : Finset Row}
    (l : Verified m B margin U s r) (s₁ : ∀ i ∉ r,q i=0) (E : pot B e*7≤low/2) :
    ‖paintV m B U s q x-turn (aligner a U x) (paintV m B U s q (snap m B a x))‖ ≤ 4/low*pot B e := by
  unfold paintV; rw [turn_ren]
  apply le_trans (ren_near (prism_nonzero _ k p g l s₁ E _) (by rw [turn_norm]; exact prism_nonzero _ k p g l s₁ E _))
  exact mul_le_mul_of_nonneg_left (paint_near a h s g p q k) (div_nonneg (by norm_num) low_p.le)
lemma rep_local (z : Index m) {x : Site (Domain m B)} (h : snap m B z x∈room m B a) (i : Axis) (e : snap m B z (x+step i) ∈ room m B a) (g : Agrees (room m B a) U V) : replica m B z U (x,i)=replica m B z V (x,i) := by
  by_cases k: OddAxis m (z i)
  · simp only [replica,k,ite_true]; rw [snap_fwd,if_pos k] at e; exact g _ h e
  simp [replica,k]
-- paint dependency in one face, reduced primitives
lemma paint_local {x : Site (Domain m B)} (h : x∈room m B a) (q : Sq) {s t : ArrayF m} (e : Agrees (room m B a) U V) (k : ∀ i:Spot m, i.1∈active m B x→s i=t i) : paintV m B U s q x = paintV m B V t q x := by
  unfold paintV; apply congrArg ren; unfold paint; refine sum_congr rfl ?_; intro i _; by_cases g:i∈bandS m B x q
  · have hx := spot_hit g; rw [k i hx]; apply congrArg
    unfold freight; apply congrArg; apply sum_congr rfl; intro j _; unfold launch tax; rw [traverse h (room_in (room_active h hx) (raddr m B i.1)) ((separation_comm ..).trans_le (node_dist hx).le) j e]
  simp [outside g]
lemma train_local {a₁ : Spot m} (g : Fits m a₁.1 a) (p : List (Ramp m)) (h : Moves m a₁ p) {s t : ArrayF m} (he : Agrees (room m B a) U V) (hs : ∀ i∈p,s i.1=t i.1) : train m B U s a₁.1 p=train m B V t a₁.1 p := by
  induction p generalizing a₁ with
  | nil => rfl
  | cons w p ih =>
    rcases w with ⟨x,b⟩; have hx : Fits m x.1 a₁.1 := h.1.1; have hk := fits_trans hx g
    have hp : s x=t x := hs _ List.mem_cons_self
    rw [train,train, hp, ih hk h.2 (fun i hi=>hs i (List.mem_cons_of_mem _ hi)), parcel,parcel,
        traverse (room_in g (raddr m B _)) (room_in hk (raddr m B _)) ((separation_comm ..).trans_le (chain_near hx B)) b he]
end YM.CF.Cube
