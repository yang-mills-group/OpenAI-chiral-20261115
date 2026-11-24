import YM.CF.Cubes.Extend
import YM.CF.Cubes.Cascade

/-! Output interpolation on the refined lattice in covariant frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U : Bkg (Domain m B)} {e : ℝ}

lemma lifts_far {x y : Site (Domain m B)} (h : separation x y < B.val) (i : Axis) : (lift (x-y) i).natAbs < B.val := lt_of_le_of_lt (component_le _ i) h
lemma moves_lift {x y z : Site (Domain m B)} (h : separation x z < B.val) (g : separation y z < B.val) : lift (y-x)=lift (y-z)-lift (x-z) := by
  rw [lift_eq_iff]; refine ⟨by rw [map_sub,wrap_lift,wrap_lift]; abel, ?_⟩
  intro i; simp only [Pi.sub_apply]; have hx := lifts_far h i; have hy := lifts_far g i; have he := enough m B; omega
lemma stop_trans (x y : Cover) (l : Walk) : stop (x+y) l=x+stop y l := by induction l generalizing x y <;> simp_all [stop,add_assoc]
lemma c_align {x y z : Site (Domain m B)} (h : separation x z < B.val) (g : separation y z < B.val) (o o') :
    stop (0:Cover) (march z x o++march x y o')=lift (y-z) := by
  rw [march,march,stop_append,route_end]
  have hx := stop_trans (lift (x-z)) 0 (route 0 (lift (y-x)) o'); rw [route_end,moves_lift h g,add_sub_cancel, add_zero] at hx; rw [moves_lift h g,hx]
lemma turn_price (g h : E) (x : Vect) : ‖turn g x-turn h x‖ ≤ cmp firstF g h * ‖x‖ := by
  unfold turn; rw [← act_sub]; unfold cmp
  rw [← Matrix.l2_opNorm_toEuclideanCLM]; exact (acts (fund g-fund h)).le_opNorm _
def pot (B : Side) (e : ℝ) := 320*(B.val:ℝ)^2*e
def tax (m B : Side) (U : Bkg (Domain m B)) (z : Site (Domain m B)) (a : Index m) (o : Lattice.Order) :=
  travel U z (march z (address m B a) o)
def launch (m B : Side) (U : Bkg (Domain m B)) (z : Site (Domain m B)) (a : Index m) (o : Lattice.Order) (v : Ballot) := turn (tax m B U z a o) v.val
lemma launch_cont (m B z a o) : Continuous (fun t : Bkg (Domain m B)×Ballot => launch m B t.1 z a o t.2) :=
  by
    have H : Continuous (fun t : Bkg (Domain m B)×Ballot=>tax m B t.1 z a o) := (travel_cont (K:=E) z (march z (address m B a) o)).comp continuous_fst
    have Hq : Continuous (fun t : Bkg (Domain m B) × Ballot => (tax m B t.1 z a o,(t.2 : Vect))) := H.prodMk (continuous_subtype_val.comp continuous_snd)
    unfold launch
    let J := fun t : Bkg (Domain m B) × Ballot => (tax m B t.1 z a o,(t.2 : Vect))
    change Continuous ((fun x:E×Vect=>turn x.1 x.2) ∘ J)
    exact turn_cont.comp (show Continuous J from Hq)
lemma launch_norm (m B U z a o v) : ‖launch m B U z a o v‖=1 := by rw [launch,turn_norm,vote_unit]
lemma parcel_gap (he : 0≤e) (h : Guard U e) {z a b} (g : a ∈ active m B z) (u : b ∈ active m B z) (hb : Fits m b a) (v : Vect) (o p l) :
    ‖turn (tax m B U z a o) (turn (parcel m B U a b p) v)-turn (tax m B U z b l) v‖ ≤ pot B e*‖v‖ := by
  let x := address m B a; let y := address m B b
  have hx : separation x z<B.val := by rw [separation_comm]; exact node_dist g
  have hy : separation y z<B.val := by rw [separation_comm]; exact node_dist u
  have hk : separation y x≤B.val := by rw [separation_comm]; exact chain_near hb B
  rw [← turn_seq]; apply (turn_price ..).trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
  unfold tax parcel; change cmp firstF (travel U z (march z x o)*travel U x (march x y p)) (travel U z (march z y l)) ≤ _
  have heq : stop (0:Cover) (march z x o++march x y p)=stop (0:Cover) (march z y l) := (c_align hx hy o p).trans (route_end ..).symm
  have hi := near_hop he h.1 z _ _ heq; rw [travel_append,arrive] at hi; apply hi.trans
  simp only [List.length_append]; unfold pot
  let C (w : Walk) := (w.length:ℝ)
  have hg₁ : C (march z x o)+C (march x y p)≤8*B.val := by
    have H₁ : C (march z x o)≤4*B.val := by unfold C; exact_mod_cast march_len z x o hx.le
    have H₂ : C (march x y p)≤4*B.val := by unfold C; exact_mod_cast march_len x y p hk
    linarith
  have hg₂ : C (march z y l)≤4*B.val := by unfold C; exact_mod_cast march_len z y l hy.le
  unfold C at *; rw [← add_mul,Nat.cast_add]
  apply mul_le_mul_of_nonneg_right _ he
  nlinarith [pow_le_pow_left₀ (by positivity) hg₁ 2,pow_le_pow_left₀ (by positivity) hg₂ 2]
lemma launch_gap (he : 0≤e) (h : Guard U e) {z a} (g : a∈active m B z) (v : Ballot) (o p) :
    ‖launch m B U z a o v-launch m B U z a p v‖≤ pot B e := by
  have heq : lift (0:Site (Domain m B))=0 := by funext i; simp [lift]; rfl -- tune
  have H : parcel m B U a a 1=1 := by unfold parcel march; rw [sub_self, heq,route_same,travel]
  have ht := parcel_gap he h g g (fits_id _ _) v.val o 1 p
  rw [H,vote_unit,mul_one,show turn 1 v.val=v.val by rw [turn,fund_one,act_one]] at ht; exact ht

def freight (m B : Side) (U : Bkg (Domain m B)) (z : Site (Domain m B)) (a : Index m) (v : Ballot) : Vect :=
    (Fintype.card Lattice.Order : ℝ)⁻¹ • ∑ o, launch m B U z a o v
lemma avg_bound {K : Type*} [Fintype K] [Nonempty K] (a : K → Vect) (v : Vect) (e : ℝ) (H : ∀ k, ‖a k-v‖ ≤ e) :
    ‖(Fintype.card K:ℝ)⁻¹ • (∑ i, a i)-v‖ ≤ e := by -- precedence
  let n := (Fintype.card K:ℝ)
  have he : 0<n := Nat.cast_pos.mpr Fintype.card_pos
  change ‖n⁻¹ • _-v‖ ≤ _
  have hv : ∑ i:K, (fun _ => v) i=n • v := by simp [n,Nat.cast_smul_eq_nsmul]
  rw [show n⁻¹ • (∑ i, a i) - v=n⁻¹ • ∑ i, (a i-v) by rw [sum_sub_distrib,smul_sub,hv,smul_smul, inv_mul_cancel₀ he.ne',one_smul] -- tune
       , norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _ => H i))) (by positivity)).trans
  rw [sum_const,card_univ,nsmul_eq_mul,← mul_assoc,show n⁻¹ * _=1 from inv_mul_cancel₀ he.ne',one_mul]

end YM.CF.Cube
