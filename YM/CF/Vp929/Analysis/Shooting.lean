import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-! Finite backward-dependent shooting with initially free parameters at each level. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Complex Set Function Filter Metric Topology
open Finset (range)
open scoped NNReal
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {V : Set E} {F : ℂ → E → E}
  {K : ℝ≥0} (hk : K < 1)
  {s : Set ℂ} {x : E} (hv : x ∈ V) (hm : ∀ z ∈ s, MapsTo (F z) V V) (h : ∀ z ∈ s, LipschitzOnWith K (F z) V)
include hk hv hm h

lemma fix_holo (hs : IsOpen s) (hc : IsClosed V) (hb : Bornology.IsBounded V)
    (hd : ∀ g : ℂ → E, MapsTo g s V → DifferentiableOn ℂ g s → DifferentiableOn ℂ (fun z=> F z (g z)) s) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g s ∧ ∀ z ∈ s, g z ∈ V ∧ IsFixedPt (F z) (g z) ∧
         (∀ w ∈ V, IsFixedPt (F z) w → w = g z) ∧ Tendsto (fun i : ℕ=> (F z)^[i] x) atTop (𝓝 (g z)) := by
  classical
  let X : V := ⟨x,hv⟩; letI : Nonempty V := ⟨X⟩; letI : CompleteSpace V := hc.completeSpace_coe
  let G (z : s) (y : V) : V := ⟨F z y, hm z z.prop y.prop⟩
  have Y (z : s) : ContractingWith K (G z) := ⟨hk, LipschitzWith.of_dist_le_mul fun x y=> (h z z.prop).dist_le_mul _ x.prop _ y.prop⟩
  let g (z : ℂ) := if e : z ∈ s then ((Y ⟨z,e⟩).fixedPoint (G ⟨z,e⟩)).val else x
  let φ (n : ℕ) (z : ℂ) := (F z)^[n] x
  have hx (z : s) (n) : φ n z = ((G z)^[n] X : E) := by
    unfold φ; induction n with | zero=> rfl | succ n ih=> rw [iterate_succ_apply',iterate_succ_apply',ih]
  have hd' (n : ℕ) : DifferentiableOn ℂ (φ n) s := by
    induction n with
    | zero => exact differentiableOn_const _
    | succ n ih => unfold φ; simp only [iterate_succ_apply']; exact hd (φ n) (fun z p => (hm z p).iterate _ hv) ih
  have hU : TendstoUniformlyOn φ g atTop s := by
    simp_rw [Metric.tendstoUniformlyOn_iff]
    let b:= diam V; have l:= NNReal.coe_lt_coe.mpr hk
    have he : Tendsto (fun i:ℕ=> b * (K:ℝ)^i / (1-(K:ℝ))) atTop (𝓝 0) := by
      simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one K.prop l).const_mul b).div_const (1-(K:ℝ)))
    intro ε hp; filter_upwards [he.eventually (gt_mem_nhds hp)] with i p z h; rw [dist_comm, hx ⟨z,h⟩ i]
    have H:= (Y ⟨z,h⟩).apriori_dist_iterate_fixedPoint_le X i; unfold g; rw [dif_pos h]
    refine lt_of_le_of_lt (H.trans ?_) p; change _ ≤ b*_/(1-K:ℝ); gcongr
    · exact dist_le_diam_of_mem hb hv (G ⟨z,h⟩ X).prop
  refine ⟨g,hU.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hd') hs,fun z p=> ⟨?_,?_,?_,hU.tendsto_at p⟩⟩
  all_goals simp only [g,p,↓reduceDIte]
  · exact Subtype.prop _
  · exact congrArg Subtype.val (show G ⟨z,p⟩ _ = _ from (Y ⟨z,p⟩).fixedPoint_isFixedPt)
  intro w hw P; exact congrArg Subtype.val ((Y ⟨z,p⟩).fixedPoint_unique (show IsFixedPt (G ⟨z,p⟩) ⟨w,hw⟩ from Subtype.ext P))
end

/-- A guessed shooting vector, incl value at 0 (fixed by the shooting map). -/
abbrev Bet (k : ℕ) := Fin (k+1) → ℂ
def Bet.read {k : ℕ} (v : Bet k) (i : ℕ) := v ⟨min i k, Nat.lt_succ_of_le (min_le_right ..)⟩
lemma Bet.read_of_le {k i : ℕ} (b : Bet k) (h : i ≤ k) : b.read i = b ⟨i,by omega⟩ := by simp [Bet.read,min_eq_left h]
lemma Bet.read_val {k : ℕ} (b : Bet k) (i : Fin (k+1)) : b.read i = b i := read_of_le b (by omega)

variable {k : ℕ} (r d B : ℕ → ℝ) (Δ : ℕ → Bet k → ℂ)
/-- Section of guess-cylinder (tail). -/
def area (a : ℝ) (l : ℕ) := {b : Bet k | ∀ i, l ≤ i → i ≤ k → ‖b.read i-(B i:ℂ)‖ ≤ a*r i}
structure Posts : Prop where
  pos (i) : 0 < r i
  fee (i) : 0 ≤ d i
  mono : Monotone r
  fast (i) : 4*d i ≤ r (i+1)-r i
  small : ∀ i : ℕ, ∑ j∈range i, d j/r (j+1) ≤ 1/400
  bound (i) : i < k → ∀ b ∈ area r B 3 (i+1), ‖Δ i b‖ ≤ d i
  real (i) (hi : i < k) : ∀ b ∈ area r B 3 (i+1), (∀ j, i<j → j ≤ k → (b.read j).im=0) → (Δ i b).im=0
  holo (s : Set ℂ) : IsOpen s → ∀ i < k, ∀ f : ℂ → Bet k, MapsTo f s (area r B 3 (i+1)) → DifferentiableOn ℂ f s → DifferentiableOn ℂ (fun z=> Δ i (f z)) s

def updateBet (z : ℂ) (b : Bet k) : Bet k := fun i=> (B i:ℂ)+z+ ∑ j∈range i.val, Δ j b
abbrev Bet.Real {k} (b : Bet k) := ∀ i, i ≤ k → (b.read i).im=0

namespace Posts
variable {r d B Δ} (A : Posts r d B (k:=k) Δ) {z : ℂ}
local notation "V" => area (k:=k) r B 1 0
include A
lemma expand_area {b} (h : b ∈ V) (i : ℕ) : b ∈ area r B 3 i := by
  intro j _ p; exact (h j (by omega) p).trans (mul_le_mul_of_nonneg_right (by norm_num) (A.pos j).le)

lemma into {b} (h : b ∈ V) (hp : ‖z‖ ≤ r 0 / 8) : updateBet B Δ z b ∈ area r B (1/4) 0 := by
  have H (i) : ∑ u∈range i, d u ≤ (r i-r 0)/4 := by
    induction i with | zero=>simp | succ i ih=> rw [Finset.sum_range_succ]; linarith [A.fast i]
  intro i _ hi; rw [Bet.read_of_le _ hi]; unfold updateBet; dsimp only
  rw [add_assoc,add_comm (B i:ℂ),add_sub_cancel_right]; refine (norm_add_le ..).trans (le_trans (add_le_add hp ((norm_sum_le ..).trans (?_ : _ ≤ (r i-r 0)/4))) ?_)
  · exact (Finset.sum_le_sum (fun j p=> A.bound j ((Finset.mem_range.mp p).trans_le hi) b (A.expand_area h (j+1)))).trans (H i)
  linarith [A.pos 0]

lemma keep {z : ℂ} (e : ‖z‖ ≤ r 0/8) : MapsTo (updateBet B Δ z) V V := fun _ h i a p =>
  (A.into h e i a p).trans (mul_le_mul_of_nonneg_right (by norm_num) (A.pos i).le)

private lemma fare {i : ℕ} (hi : i < k) {x y} (hx : x ∈ V) (hy : y ∈ V) :
    ‖Δ i x - Δ i y‖ ≤ d i / r (i+1) * ‖x-y‖ := by
  by_cases e:x=y; simp [e]
  let a:=r (i+1); let b:=‖x-y‖; have ha:0<a:= A.pos _; have hb:0<b:= norm_pos_iff.mpr (sub_ne_zero.mpr e)
  let t:= a/b; have hp:0<t:=div_pos ha hb
  let u (z:ℂ) : Bet k := y + z • (x-y)
  let f:= Δ i ∘ u; let W:= segment ℝ (0:ℂ) 1
  have hu (z) (zh : z∈ W) : u z∈ V := by
    rw [show W= _ from segment_eq_image_lineMap ℝ (0:ℂ) 1] at zh
    obtain ⟨m,hm,rfl⟩:= zh; intro j hJ p; rw [← mem_closedBall_iff_norm]; have q:= (convex_closedBall (B j:ℂ) (1*r j)).mapsTo_lineMap (mem_closedBall_iff_norm.mpr (hy _ hJ p)) (mem_closedBall_iff_norm.mpr (hx _ hJ p)) hm
    convert q using 1
    simp [Bet.read,u,AffineMap.lineMap_apply, Complex.real_smul]; ring
  have hB (z) (hz:z∈W) : MapsTo u (ball z (2*t)) (area r B 3 (i+1)) := by
    intro w hw j hJ hj
    let e:= (u z).read j
    have p : (u w).read j - (B j:ℂ) = (e- (B j:ℂ)) + (w-z) * (x.read j-y.read j) := by simp [u,Bet.read,e]; ring
    rw [p]; have H:‖x.read j-y.read j‖≤b:= norm_le_pi_norm (x-y) _
    have hW:= mul_le_mul (mem_ball_iff_norm.mp hw).le H (norm_nonneg _) (by positivity)
    rw [show 2*t*b=2*a by unfold t; field_simp] at hW; refine (norm_add_le ..).trans ?_; rw [norm_mul]; linarith [A.mono hJ, show ‖e-(B j:ℂ)‖ ≤ 1*r j from hu z hz j (by omega) hj]
  have hd z (hz : z∈ W) : DifferentiableOn ℂ f (ball z (2*t)):= A.holo _ isOpen_ball i hi u (hB _ hz) (Differentiable.differentiableOn (by unfold u; fun_prop))
  have hg z (hz:z∈W) : ‖deriv f z‖ ≤ d i/t := by
    have v:= closedBall_subset_ball (x:=z) (by linarith : t < 2*t)
    rw [← cderiv_eq_deriv isOpen_ball (hd z hz) hp v]
    exact norm_cderiv_le hp (fun a p => A.bound i hi (u a) (hB z hz (v (sphere_subset_closedBall p))))
  have p:= (convex_segment (0:ℂ) (1:ℂ)).norm_image_sub_le_of_norm_deriv_le
             (fun z hz=>(hd z hz).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))) hg
             (left_mem_segment ℝ (0:ℂ) 1) (right_mem_segment ℝ (0:ℂ) 1)
  rw [show d i / r (i+1)*‖x-y‖=d i/t by dsimp [t,a,b]; ring_nf; rw [inv_inv]]; simpa [f,u, add_sub_cancel] using p

lemma contract (z : ℂ) : LipschitzOnWith (1/4 : ℝ≥0) (updateBet B Δ z) V := by
  apply LipschitzOnWith.of_dist_le_mul; intro x hx y hy; push_cast
  simp only [dist_eq_norm]; refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=>?_
  simp only [Pi.sub_apply,updateBet,add_sub_add_left_eq_sub,←Finset.sum_sub_distrib]
  refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (fun u w=> A.fare (lt_of_lt_of_le
           (Finset.mem_range.mp w) (Nat.le_of_lt_succ i.prop)) hx hy)) ?_)
  rw [←Finset.sum_mul]; refine mul_le_mul_of_nonneg_right ((A.small i.val).trans (by norm_num)) (norm_nonneg _)

lemma solve : ∃ g : ℂ → Bet k, DifferentiableOn ℂ g (ball 0 (r 0/8)) ∧
    ∀ z ∈ ball 0 (r 0/8), g z ∈ area r B (1/4) 0 ∧ g z ∈ V ∧ IsFixedPt (updateBet B Δ z) (g z) ∧
       (∀ w∈V, IsFixedPt (updateBet B Δ z) w → w=g z) ∧ (z.im=0 → (g z).Real) := by
  let x : Bet k := fun i=> (B i:ℂ)
  have Hx : x∈ V := by intro i _ hi; rw [Bet.read_of_le x hi]; simp [x,(A.pos i).le]
  have hc : V = Set.pi Set.univ (fun i : Fin (k+1)=> closedBall (B i:ℂ) (1*r i)) := by
    ext z; simp only [Set.mem_pi,mem_univ,forall_const]; constructor
    · exact fun h i=> mem_closedBall_iff_norm.mpr (by rw [← Bet.read_val z]; exact h _ (by omega) (by omega))
    intro h i _ hi; rw [Bet.read_of_le _ hi]; exact mem_closedBall_iff_norm.mp (h _)
  have hm z (hz:z∈ball (0:ℂ) (r 0/8)):= A.keep (mem_ball_zero_iff.mp hz).le
  obtain ⟨g,hd,P⟩:= fix_holo (F:=updateBet B Δ) (by norm_num : (1/4:ℝ≥0)<1) Hx hm
    (fun z _=> A.contract z) isOpen_ball (hc ▸ (isClosed_set_pi fun i _=> isClosed_closedBall))
    ((hc ▸ (isCompact_univ_pi fun i=> isCompact_closedBall _ _)).isBounded) (by
       intro p hp hd; unfold updateBet; refine differentiableOn_pi.mpr fun i=> DifferentiableOn.add
                   ((differentiableOn_const _).add differentiableOn_id) (DifferentiableOn.fun_sum fun j hj=>?_)
       exact A.holo _ isOpen_ball j (lt_of_lt_of_le (Finset.mem_range.mp hj) (by omega)) p
            (fun z hz=> A.expand_area (hp hz) (j+1)) hd)
  refine ⟨g,hd, fun z p=>?_⟩; obtain ⟨h,P,Q,L⟩:= P z p
  refine ⟨P ▸ A.into h (mem_ball_zero_iff.mp p).le,h,P,Q,fun e i w=>?_⟩
  let j : Fin (k+1):= ⟨i,by omega⟩
  have H : ∀ n, ((updateBet B Δ z)^[n] x).Real := by
    intro n; induction n with
    | zero=> exact fun _ _ => Complex.ofReal_im _
    | succ n ih=>
      intro i hi; rw [iterate_succ_apply', Bet.read_of_le _ hi]; unfold updateBet; simp only [add_im,im_sum,zero_add,e,ofReal_im,add_zero]; exact Finset.sum_eq_zero fun k p'=> A.real k (lt_of_lt_of_le (Finset.mem_range.mp p') hi) _ (A.expand_area ((hm z p).iterate n Hx) _) fun i _ t=> ih i t
  rw [Bet.read_of_le _ w]; refine tendsto_nhds_unique (((Complex.continuous_im.comp (continuous_apply j)).tendsto (g z)).comp L) (tendsto_const_nhds.congr fun n=>?_)
  have := H n i w; rw [Bet.read_of_le _ w] at this; exact this.symm
end Posts
end YM.CF.VolumeRate
