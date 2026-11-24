import YM.CF.BProof.Grid.Patch
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Generic price for walking piecewise cubical grids. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Entity
open Lattice Cube Function Set Finset
open scoped Topology BigOperators
variable {n : ℕ} {c s : Side} (g : Ratio c s) (p : Entity n c)

lemma local_distance {x y : Cubic n s}(h:p.Mem g x)(u:p.Mem g y)(hc:4≤c.val)(i:Fin n):
    delta1 s (x i) (y i) = max (p.coord g x i) (p.coord g y i)-min (p.coord g x i) (p.coord g y i) := by
 let a(x:Cubic n s) := p.coord g x i; have he (x:Cubic n s) : p.first g i + a x=x i:=add_along ..
 have ht {x y:Cubic n s}(h:p.Mem g x)(u:p.Mem g y) (j:a x≤a y): delta1 s (y i) (x i)=a y-a x:=by
   have hz:= count_small g hc; have hk:a y ≤ g.count.val:= (u i).trans (p.width g i); have hl := count_tiny g hc
   rw [delta_eq]; have e : along (x i) (y i)=a y-a x:= by
     conv_lhs => rw [← he x,← he y];
     exact offset_dist _ j (by change _ < s.val; omega)
   rw [e]; change min _ (s.val-_) = _; omega
 rcases le_total (a x) (a y) with e|e; rw [max_eq_right e,min_eq_left e,d_sym]; exact ht h u e
 rw [max_eq_left e,min_eq_right e]; exact ht u h e

private abbrev gap (x y : ℕ) := max x y-min x y
def steps (x y : Cubic n s) := ∑ i, delta1 s (x i) (y i)
lemma steps_symm (x y:Cubic n s):steps x y=steps y x:= sum_congr rfl fun i _=> d_sym ..
lemma steps_le (x y:Cubic n s):steps x y ≤ n * Grid.dist x y:= (sum_le_sum (fun i _=>Grid.dist_axis x y i)).trans_eq (by simp)

/-- distance in ticks over same entity's standard coordinates. -/
abbrev total (x y : Tick (n:=n)) := ∑ i, gap (x i) (y i)
lemma steps_coord (hc:4≤c.val){x y:Cubic n s}(h:p.Mem g x)(u:p.Mem g y): steps x y= total (p.coord g x) (p.coord g y):= sum_congr rfl fun i _=>local_distance g p h u hc i
lemma steps_put (hc:4≤c.val){x y:Tick (n:=n)}(h:x≤p.len g)(u:y≤p.len g): steps (p.put g x) (p.put g y)=total x y:= by rw [steps_coord g p hc (p.mem_put g hc h) (p.mem_put g hc u),p.coord_put g hc h,p.coord_put g hc u] -- field order?
lemma total_le (x y:Tick (n:=n))(k:ℕ)(h:∀ i,gap (x i) (y i) ≤ k) : total x y ≤ n*k := (sum_le_sum (fun i _=> h i)).trans_eq (by simp)

lemma total_step {x y:Tick (n:=n)} {i:Fin n}(h:x i<y i) : total (update x i (x i+1)) y+1=total x y:=by
 unfold total; rw [←add_sum_erase _ _ (Finset.mem_univ i),←add_sum_erase _ (fun k=> gap (x k) (y k)) (Finset.mem_univ i),update_self,add_right_comm]; refine congrArg₂ _ ?_ (sum_congr rfl fun i g=>by rw [update_of_ne (ne_of_mem_erase g)]); unfold gap; omega
lemma total_symm (x y: Tick (n:=n)) : total x y=total y x:=sum_congr rfl fun i _=>by unfold gap; omega

/-- arbitrary ambient distance price (even not separating points). -/
theorem tick_telescopes {a : Tick (n:=n)} {f : Tick (n:=n)→Tick (n:=n)→ℝ} {δ : ℝ}
    (ht:∀ x,f x x=0)(hg:∀ x y,f x y=f y x)(hl:∀ x y z,f x z ≤ f x y+f y z)
    (h : ∀ x≤a,∀ i,x i<a i → f x (update x i (x i+1)) ≤ δ) : ∀ x≤a,∀ y≤a, f x y ≤ δ*total x y := by
 suffices hh:∀ k:ℕ,∀ x≤a,∀ y≤a,total x y=k → f x y ≤ δ*(k:ℝ) from fun x hx y hy=> hh _ _ hx _ hy rfl
 intro k; induction k using Nat.strong_induction_on with
 | h k ih=>
   have hv (x y : Tick (n:=n))(hx:x≤a)(hy:y≤a)(he:total x y=k)(u:∃ i,x i<y i):f x y≤δ*k:=by
     obtain ⟨i,hu⟩:=u; let X:=update x i (x i+1); have hi:X≤a:=by intro j; by_cases h:j=i; subst j; unfold X; rw [update_self]; exact hu.trans_le (hy i); unfold X; rw [update_of_ne h]; exact hx j
     have hj : total X y+1=k:= (total_step hu).trans he
     apply (hl x X y).trans; refine (add_le_add (h x hx i (hu.trans_le (hy i))) (ih _ (by omega : total X y<k) _ hi _ hy rfl)).trans (by rw [← hj]; push_cast; exact le_of_eq (by ring))
   intro x hx y hy he
   by_cases h:∃ i,x i < y i; exact hv x y hx hy he h
   by_cases u:∃ i,y i < x i; exact (hg x y).trans_le (hv y x hy hx ((total_symm ..).trans he) u)
   push Not at h u; rw [←he,show x=y from funext (fun i=>(u i).antisymm (h i)),ht]; simp [total,gap]

theorem bound_of_step {Y : Type*} (d : Y→Y→ℝ)(F:Cubic n s→Y) {δ : ℝ}
    (ht:∀ x,d x x=0)(hg:∀ x y,d x y=d y x)(hl:∀ x y z,d x z ≤ d x y+d y z)
    (h:∀ x i,p.Mem g x→p.Mem g (slide x i)→ d (F x) (F (slide x i)) ≤ δ)
    (hc:4≤c.val){x y:Cubic n s} (hx:p.Mem g x)(hy:p.Mem g y) : d (F x) (F y)≤δ*steps x y:=by
 have hp:= tick_telescopes (a:=p.len g) (δ:=δ) (f:=fun a b=> d (F (p.put g a)) (F (p.put g b)))
    (fun a=>ht _) (fun a b=>hg ..) (fun a b c=>hl ..) (fun x hx i g'=>by rw [put_step]; refine h _ _ (p.mem_put g hc hx) (put_step .. ▸ p.mem_put g hc (p.inside_put_step g x i hx g'))) _ hx _ hy
 simpa only [put_coord,← steps_coord g p hc hx hy] using hp

lemma small_metric (x y:Cubic n s)(hx:p.Mem g x)(hy:p.Mem g y):steps x y≤ n*(2*g.count.val) := by
 apply (steps_le x y).trans; apply Nat.mul_le_mul_left; have hv:= Grid.triangle x (p.first g) y; rw [Grid.dist_symm (p.first g) y] at hv; exact le_trans hv ((Nat.add_le_add (p.diameter g x hx) (p.diameter g y hy)).trans_eq (by omega))
end YM.CF.BProof.Grid.Entity
