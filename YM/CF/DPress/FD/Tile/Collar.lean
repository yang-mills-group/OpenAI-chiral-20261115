import YM.CF.DPress.FD.Tile.Sun
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory Ramp Row Frame
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I K:Type*}[Fintype I][Fintype K]{m:ℕ}
namespace Ramp
variable (S:Finset I)(H:S.Nonempty) (x y:Ramp I m) (e:0 < m)
abbrev low (x:Ramp I m):= S.inf' H fun i=> (x i).val
lemma top_K(i:I)(v:i∈S): low S H x ≤ (x i).val:=Finset.inf'_le _ v
lemma repr :∃ i∈ S,low S H x=(x i).val:= Finset.exists_mem_eq_inf' H _
lemma near : low S H x ≤ low S H y + d x y:= by obtain ⟨i,v,h⟩:= repr S H y; apply (top_K S H x i v).trans; rw [h]; have hx:= tick x y i; unfold DistU at hx; omega
-- discrete radial projection cheap even parity exact on boundary
abbrev peg :Ramp I m:=fun i=> ⟨min (x i).val (2*((x i).val-low S H x)),Nat.lt_succ_iff.mpr ((min_le_left ..).trans (Nat.lt_succ_iff.mp (x i).isLt))⟩
include e
lemma peg_l(v:x∈boundary S): peg S H x=x:=by
 have hp:low S H x=0:=by obtain ⟨i,w,t⟩:= Finset.exists_of_ssubset v.2; have hx:= top_K S H x i w; rw [dark (show On x (supportT x) from Warm.limUnit e _ v) t] at hx; exact Nat.eq_zero_of_le_zero hx -- maybe include e Warm
 ext i; change min (x i).val _= (x i).val; omega
lemma peg_H(p:Ramp.On x S)(c: 2*low S H x ≤ m) : peg S H x∈boundary S:=by
 obtain ⟨i,u,v⟩:= exists_right e p; obtain ⟨j,t,s⟩:=repr S H x; refine ⟨⟨i,?_⟩, Finset.ssubset_iff_subset_ne.mpr ⟨?_,fun h=> ?_⟩⟩
 · apply Fin.ext; change min (x i).val (2*((x i).val-low S H x))= m; rw [v]; change min m (2*(m- low S H x)) = m; omega
 · intro b t; by_contra g; have hx:= (mem_h _).mp t; apply hx; apply Fin.ext; change min (x b).val _=0; rw [dark p g]; simp
 have he:peg S H x j ≠ 0:= (mem_h _).1 (h.symm ▸ t); apply he; apply Fin.ext; change min (x j).val (2* _)=0; rw [s]; omega
omit e
lemma peg_cost : d (peg S H x) (peg S H y) ≤ 4*d x y:=by
 have ht := near S H x y; have hp:=near S H y x; rw [symmetry y x] at hp; apply (Ramp.dusk ..).2; intro i
 let a:=(x i).val; let b:=(y i).val; let p:=low S H x; let q:=low S H y; let c:= d x y; have h1:p≤ q+c:=ht; have h2:q≤p+c:=hp; let s:= min a (2*(a-p)); let r:= min b (2*(b-q)); have h3:a-b+(b-a)≤c:= tick x y i; change s-r+(r-s) ≤ 4*c; unfold s r; omega
lemma thick : δR (peg S H x) (peg S H y) ≤4*δR x y:= by
 unfold δR; refine (div_le_div_of_nonneg_right (Nat.cast_le.mpr (peg_cost S H x y)) (Nat.cast_nonneg _)).trans_eq ?_; push_cast; ring
abbrev kappa := 4* ((low S H x:ℝ)/(m:ℝ))
abbrev gain := min 1 (kappa S H x)
abbrev lower:= max 0 (min 1 (2-kappa S H x))
include e
lemma cut (p:2*low S H x>m): gain S H x=1 ∧ lower S H x=0:=by
 have ht':2*(low S H x:ℝ) > (m:ℝ):= by exact_mod_cast p
 have hp:0 < (m:ℝ):= by positivity
 have ht:kappa S H x>2:=by unfold kappa; rw [←mul_div_assoc,gt_iff_lt, lt_div_iff₀ hp]; linarith
 constructor; · unfold gain; rw [min_eq_left]; linarith
 unfold lower; rw [max_eq_left]; exact le_trans (min_le_right ..) (by linarith)
omit e
lemma pay : gain S H x ∈ budget ∧ lower S H x∈ budget ∧ (gain S H x=1 ∨ lower S H x=1):=by
 have ht:0≤ kappa S H x:=by unfold kappa; positivity
 refine ⟨⟨le_min zero_le_one ht,min_le_left ..⟩,⟨le_max_left ..,max_le zero_le_one (min_le_left ..)⟩,?_⟩; unfold gain lower; rcases le_total (kappa S H x) 1 with k|k; swap; exact Or.inl (min_eq_left k)
 exact Or.inr (by rw [min_eq_left (show 1≤ 2 - kappa S H x by linarith),max_eq_right zero_le_one])
lemma κ_cost : kappa S H x≤ kappa S H y+4*δR x y:=by
 have hh:(low S H x:ℝ)≤ (low S H y:ℝ)+(d x y:ℝ):=by exact_mod_cast near S H x y
 unfold kappa δR; rw [←mul_add, ←add_div]; refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)) (by positivity)
private lemma live_cost (a b u:ℝ)(p:a ≤ b+u)(t:b≤ a+u) : |min 1 a-min 1 b|≤u ∧ |max 0 (min 1 (2-a)) -max 0 (min 1 (2-b))|≤ u:=by
 constructor <;> rw [abs_le] <;> grind -- grind
lemma gain_cost : |gain S H x - gain S H y|≤ 4*δR x y ∧|lower S H x-lower S H y|≤ 4*δR x y := live_cost _ _ _ (κ_cost S H x y) (δs (y:=x) (x:=y) ▸ κ_cost S H y x)
include e
lemma begin_ (p:x∈boundary S): gain S H x=0 ∧ lower S H x =1:=by
 have hp:low S H x=0:=by obtain ⟨i,w,t⟩:= Finset.exists_of_ssubset p.2; have hx:= top_K S H x i w; rw [dark (show On x (supportT x) from Warm.limUnit e _ p) t] at hx; exact Nat.eq_zero_of_le_zero hx
 unfold gain lower kappa; rw [hp]; norm_num
end Ramp
end YM.CF.DPress.FD
