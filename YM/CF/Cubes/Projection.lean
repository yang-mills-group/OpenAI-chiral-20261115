import YM.CF.Cubes.Inside
import YM.CF.Lattice.Local

/-! Replica on a face-cylinder. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U : Bkg (Domain m B)} {e : ℝ} (a : Index m)
lemma snap_fwd (x : Site (Domain m B)) (i : Axis) : snap m B a (x+step i)=if OddAxis m (a i) then snap m B a x+step i else snap m B a x := by
  split_ifs with h <;> (funext j; by_cases g:j=i <;> simp [snap,g,h])
def replica (m B : Side) (a : Index m) (U : Bkg (Domain m B)) : Bkg (Domain m B) := fun ⟨x,i⟩=> if OddAxis m (a i) then U (snap m B a x,i) else 1
lemma replica_cont : Continuous (replica m B a) := by
  apply continuous_pi; rintro ⟨x,i⟩; by_cases l:OddAxis m (a i) <;> simp [replica,l,continuous_apply]
  exact continuous_const
lemma replica_g (U : Bkg (Domain m B)) (g : Site (Domain m B)→E) : replica m B a (gauge g U) = gauge (g ∘ snap m B a) (replica m B a U) := by
  funext ⟨x,i⟩; by_cases h:OddAxis m (a i) <;> simp [replica,Lattice.gauge,snap_fwd,h]
lemma tile_plaq {I : Type*} [Fintype I] [DecidableEq I] (R : E →* UNI I) (h : PlaqBound R U e) (g : 0 ≤ e) : PlaqBound R (replica m B a U) e := by
  intro x i j he
  have ht (U : Bkg (Domain m B)) (x : Site (Domain m B)) : travel U x (square i j) = U (x,i)* U (x+step i,j)*(U (x+step j,i))⁻¹*(U (x,j))⁻¹ := by
    simp only [square, travel, Step.pos_read, Step.vec_pos, Step.vec_neg, Step.neg_read]; rw [show x+step i+step j-step i=x+step j by abel, show x+step i+step j+ -step i-step j=x by abel]; group
  by_cases l : OddAxis m (a i) <;> by_cases k : OddAxis m (a j)
  · rw [ht]; simp only [replica,l,k,ite_true,snap_fwd]; rw [←ht]; exact h _ _ _ he
  all_goals
    rw [ht]; simpa [replica,snap_fwd,l,k] using g
lemma tile_guard (h : Guard U e) (g : 0 ≤ e) : Guard (replica m B a U) e := ⟨tile_plaq a _ h.1 g, tile_plaq a _ h.2 g⟩
lemma tile_slow (x : Site (Domain m B)→Vect) (h : Slow U x e) (g : 0<e) : Slow (replica m B a U) (x ∘ snap m B a) e := by
  intro y i; unfold replica; by_cases l:OddAxis m (a i) <;> simp only [Function.comp_apply,snap_fwd,l,ite_true,ite_false]
  · exact h _ _
  simpa [turn,fund_one] using g
-- compare in aligned frames only along the indicated collar sites.
def aligner (U : Bkg (Domain m B)) (x : Site (Domain m B)) := travel U x (march x (snap m B a x) 1)
lemma summit_stop (z x y : Site (Domain m B)) (l q : Walk) (h : stop (0:Cover) l=lift (x-z)) (g : stop (0:Cover) q=lift (y-x)) (L : separation x z≤B.val) (J : separation y z≤B.val) (T : separation y x≤B.val) :
    stop (0:Cover) (l++q)=lift (y-z) := by
  rw [stop_append,h]; nth_rw 1 [←add_zero (lift _)]; rw [stop_trans,g,triangle_lift L J T,add_sub_cancel]
lemma compare_align {x : Site (Domain m B)} (he : slab m B a x) (i : Axis) (hk : slab m B a (x+step i)) (g : 0≤e) {I : Type*} [Fintype I] [DecidableEq I] (R : E →* UNI I) (h : PlaqBound R U e) :
    cmp R (U (x,i)) (gauge (aligner a U) (replica m B a U) (x,i)) ≤ pot B e := by
  let y := x+step (S:=Per (Domain m B)) i; let s := snap m B a
  let k := aligner a U; let X := march x (s x) 1; let Y := march y (s y) 1
  let L : Walk := if OddAxis m (a i) then [posDir i] else []
  let J : Walk := [posDir i] ++ Y; let T := X++L
  have ho (x : Site (Domain m B)) : stop (0:Cover) [posDir i]=lift (x+step i-x) := by
    rw [stop,stop,Step.vec_pos,zero_add,add_sub_cancel_left,lift_step]; have h := enough m B; have he : 0 < B.val := B.property; omega
  have hx := snap_sharp he; have hy := snap_sharp hk
  have ha : separation x y≤1 := oneTouch x i
  have heB := collar_lt B; have hb := B.property
  have heq : separation x (s y) ≤ B.val := by apply (separation_triangle x y (s y)).trans; exact (Nat.add_le_add ha hy).trans (by omega)
  have hL : travel U (s x) L=replica m B a U (x,i) := by by_cases h:OddAxis m (a i) <;> simp [L,h,travel,replica,s]
  have hY : stop (0:Cover) L=lift (s y-s x) ∧ separation (s x) (s y)≤B.val := by
    unfold s L y; rw [snap_fwd]; split_ifs with l
    · exact ⟨ho _, (oneTouch ..).trans hb⟩
    rw [sub_self,stop,separation_self]; exact ⟨by funext i; symm; exact ZMod.valMinAbs_zero .. , Nat.zero_le _⟩
  have hT : stop (0:Cover) J=stop (0:Cover) T := by
    calc _ = lift (s y-x) := summit_stop x y (s y) _ _ (ho _) (route_end ..) ((separation_comm ..).trans_le (ha.trans hb)) ((separation_comm ..).trans_le heq) ((separation_comm (s y) y).trans_le (hy.trans heB.le))
         _ = _ := (summit_stop x (s x) (s y) _ _ (route_end ..) hY.1 ((separation_comm (s x) x).trans_le (hx.trans heB.le)) ((separation_comm ..).trans_le heq) ((separation_comm ..).trans_le hY.2)).symm
  change cmp R _ (k x * replica m B a U (x,i) * (k y)⁻¹)≤_
  rw [←cmp_right _ _ _ (k y),mul_assoc,inv_mul_cancel,mul_one,←hL,show travel U (s x) L=travel U (stop x X) L by unfold X; rw [arrive],show k x=travel U x X from rfl, ←travel_append,show U (x,i)*k y=travel U x J from rfl]
  apply (near_hop g h x J T hT).trans
  have hz : X.length≤4*B.val := march_len _ _ _ ((separation_comm ..).trans_le (hx.trans heB.le)); have hh : Y.length≤4*B.val := march_len _ _ _ ((separation_comm ..).trans_le (hy.trans heB.le))
  have hJ : (J.length:ℝ) ≤ 5*(B.val:ℝ) := by exact_mod_cast (show J.length≤5*B.val by change Y.length+1≤_; omega)
  have hQ : (T.length:ℝ) ≤ 5*(B.val:ℝ) := by
    have hl : L.length≤1 := by unfold L; split <;> simp
    exact_mod_cast (show T.length ≤ 5*B.val from by unfold T; rw [List.length_append]; omega)
  rw [←add_mul]; unfold pot -- 4*25+4*25 ≤320
  apply mul_le_mul_of_nonneg_right _ g
  nlinarith [pow_le_pow_left₀ (by positivity) hJ 2,pow_le_pow_left₀ (by positivity) hQ 2]
lemma align_one {x : Site (Domain m B)} (he : slab m B a x) {b : Index m} (ht : b∈active m B x) (h : Guard U e) (g : 0≤e) (k : Ballot) (o) :
    ‖turn (aligner a U x) (launch m B U (snap m B a x) b o k)-launch m B U x b o k‖ ≤ pot B e := by
  rw [launch, launch,←turn_seq]; apply (turn_price ..).trans; rw [vote_unit,mul_one,tax,tax,aligner]
  let z := snap m B a x; let y := address m B b; let s := march z y o; let r := march x z 1; let l := march x y o
  have hx : separation z x ≤ B.val := (separation_comm _ _).trans_le ((snap_sharp he).trans (collar_lt B).le)
  have hy : separation y x ≤ B.val := (separation_comm _ _).trans_le (node_dist ht).le
  have hz : separation y z ≤ B.val := (separation_comm _ _).trans_le (node_dist (a:=b) (z:=z) (slab_act he ▸ ht)).le
  have heq : stop (0:Cover) (r++s)=stop (0:Cover) l := (summit_stop _ _ _ _ _ (route_end ..) (route_end ..) hx hy hz).trans (route_end ..).symm
  have hi := near_hop g h.1 x _ _ heq
  rw [travel_append, show stop x r=z from arrive ..] at hi
  apply hi.trans
  have hr : (r.length:ℝ)≤4*B.val := by exact_mod_cast march_len x z 1 hx
  have hS : (s.length:ℝ)≤4*B.val := by exact_mod_cast march_len z y o hz
  have hP : (l.length:ℝ)≤4*B.val := by exact_mod_cast march_len x y o hy
  rw [←add_mul, List.length_append,Nat.cast_add]; unfold pot; apply mul_le_mul_of_nonneg_right _ g
  nlinarith [pow_le_pow_left₀ (by positivity) (add_le_add hr hS) 2,pow_le_pow_left₀ (by positivity) hP 2]
end YM.CF.Cube
