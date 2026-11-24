import YM.CF.Cubes.Slide

/-! Volume-independent short-path transport bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open YM.Lattice Lat
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {I K : Type*} [Group K] [Fintype I] [DecidableEq I]
variable {R : K →* UNI I} {U : Links ℤ K} {e : ℝ}
lemma carry_step (U : Links ℤ K) (x : Cover) (p : Step) (j : ℤ) :
    travel U x (straight p.dir (j+p.vec p.dir)) = travel U x (straight p.dir j++[p]) := by
  rcases p with ⟨i,d|d⟩
  · change travel U x (straight i (j+(step i:Cover) i))=_
    rw [step_apply,if_pos rfl,carry_succ, travel_append,straight_stop,travel,travel,mul_one]; rfl
  change travel U x (straight i (j+(-step i:Cover) i)) = travel U x (straight i j ++ [negDir i]); rw [travel_append,straight_stop]
  simp only [Pi.neg_apply,step_apply,ite_true, travel, Step.neg_read, mul_one, ← sub_eq_add_neg]
  rw [show travel U x (straight i j) = travel U x (straight i (j-1)) * U (x+(j-1) • step i,i) by simpa using carry_succ U x i (j-1)]
  rw [show x+j • step i-step i=x+(j-1) • step i by rw [sub_smul,one_smul]; abel]; group
lemma carry_stop (x : Cover) (p : Step) (j : ℤ) :
    stop x (straight p.dir (j+p.vec p.dir))=stop x (straight p.dir j++[p]) := by
  simp only [stop_append,straight_stop,stop,add_smul]
  rw [show (p.vec p.dir:ℤ) • (step p.dir : Cover)=p.vec by cases p with
    | mk i n => cases n <;> simp [Step.vec]]; abel
lemma endCost (he : 0≤e) (h : Covered R U e) (x y : Cover) (o : Lattice.Order) (i : Step) :
    compareW R U x (route x (y+i.vec) o) (route x y o++[i]) ≤ (route x y o).length*e := by
  have hm : i.dir ∈ allAxes o := List.mem_map.mpr ⟨o.symm i.dir,by simp,by simp⟩
  have hn : (allAxes o).Nodup := (List.nodup_finRange _).map o.injective
  obtain ⟨a,b,f⟩ := List.append_of_mem hm
  rw [f,List.nodup_append] at hn
  have ha : i.dir∉a := fun l => hn.2.2 _ l _ (List.mem_cons_self) rfl
  have hb : i.dir∉b := (List.nodup_cons.mp hn.2.1).1
  let A := axisRoute x y a; let B := axisRoute x y b; let C := y i.dir-x i.dir; let D := straight i.dir C
  have gy (l : List Axis) (hl : i.dir∉l) : axisRoute x (y+i.vec) l=axisRoute x y l := by
    apply axis_route_support; intro k g; have he : k ≠ i.dir := fun hh => hl (hh ▸ g)
    simp only [Step.vec]; split <;> simp [he]
  have hp : route x y o=A ++ D ++ B := by rw [route,f,axisRoute_append,List.append_assoc]; rfl
  have hq : route x (y+i.vec) o=(A ++ straight i.dir (C+i.vec i.dir)) ++ B := by
    rw [route,f,axisRoute_append,gy _ ha, List.append_assoc]
    change _ ++ (straight _ (_-_) ++ axisRoute x (y+i.vec) b)=_; rw [gy _ hb]
    change _ ++ (straight _ (y i.dir+i.vec i.dir-x i.dir) ++ B)=_; unfold C; rw [add_sub_right_comm]
  unfold compareW; rw [hp,hq,travel_append, stop_append,travel_append,carry_stop,carry_step]
  let w := stop (stop x A) D
  rw [show stop (stop x A) (straight i.dir C ++ [i])=w+i.vec from (stop_append ..),
    show travel U (stop x A) (straight i.dir C ++[i]) = travel U (stop x A) D * travel U w [i] from travel_append ..,
    List.append_assoc (A++D), travel_append U x (A++D), stop_append,travel_append,
    ← mul_assoc, mul_assoc _ (travel U w [i]),show travel U w [i] * travel U (w+i.vec) B=travel U w (i::B) from (travel_append U w [i] B).symm,cmp_left]
  apply (slide he h w B i).trans
  apply mul_le_mul_of_nonneg_right _ he; simp
  exact le_trans (le_add_of_nonneg_left (by positivity)) (le_add_of_nonneg_left (by positivity))
lemma coord_size (x : Cover) (l : Walk) (i : Axis) : ((stop x l) i - x i).natAbs ≤ l.length := by
  induction l generalizing x with
  | nil => simp [stop]
  | cons j l ih =>
    have h : (j.vec i:ℤ).natAbs≤1 := by unfold Step.vec; split <;> (simp [step_apply] <;> split <;> simp) -- tune
    have he := Nat.add_le_add (ih (x+j.vec)) h
    rw [stop,show (stop (x+j.vec) l) i-x i=(stop (x+j.vec) l) i-(x+j.vec:Cover) i+j.vec i by rw [Pi.add_apply]; abel]
    exact (Int.natAbs_add_le ..).trans he
lemma route_size (x y : Cover) (o : Lattice.Order) (m : ℕ) (g : ∀ i, (y i-x i).natAbs≤m) :
    (route x y o).length ≤ 4*m := by
  have h (l : List Axis) : (axisRoute x y l).length ≤ l.length*m := by
    induction l with
    | nil => simp [axisRoute]
    | cons a l ih =>
      rw [show axisRoute x y (a::l) = straight _ (_-_)++axisRoute x y l from rfl,List.length_append,
        straight,List.length_replicate,List.length_cons,add_mul,one_mul,add_comm (_*m)]
      exact Nat.add_le_add (g a) ih
  simpa [route,allAxes] using h (allAxes o)
lemma move_path (he : 0≤e) (h : Covered R U e) (x : Cover) (o : Lattice.Order) (l : Walk) :
    compareW R U x (route x (stop x l) o) l ≤ (4*(l.length:ℝ)^2)*e := by
  induction l using List.reverseRecOn with
  | nil => simp [compareW,stop,cmp_id]
  | append_singleton l i ih =>
    let y := stop x l; let B := route x y o
    unfold compareW; rw [stop_append,stop,stop]; change cmp R (travel U x (route x (y+i.vec) o)) _≤_
    apply (cmp_triangle R _ (travel U x (B++[i])) _).trans
    apply (add_le_add (endCost he h x y o i) (show cmp R (travel U x (B++[i])) (travel U x (l++[i])) ≤ 4*_ * e by
      rw [travel_append,travel_append,show stop x B=stop x l from route_end ..,cmp_right]; exact ih)).trans
    have hk := route_size x y o _ (coord_size x l)
    simp only [List.length_append,List.length_singleton]
    have hg : (B.length:ℝ)≤4*(l.length:ℝ) := by exact_mod_cast hk
    push_cast; change (B.length:ℝ)*e+_≤_; nlinarith [mul_le_mul_of_nonneg_right hg he]
lemma near_walk (he : 0≤e) (h : Covered R U e) (x : Cover) (l w : Walk) (g : stop x l=stop x w) :
    compareW R U x l w ≤ 4*(l.length:ℝ)^2*e+4*(w.length:ℝ)^2*e := by
  unfold compareW
  apply (cmp_triangle R _ (travel U x (route x (stop x l) 1)) _).trans
  apply add_le_add
  · rw [cmp_sym]; exact move_path he h x 1 l
  rw [g]; exact move_path he h x 1 w
lemma taurus {N : Side} {U : RLink N K} (h : PlaqBound R U e) (b : Site N) : Covered R (expandAt b U) e := by
  intro x i j hi; rw [travel_at]; unfold cmp; rw [map_one]; exact h _ _ _ hi
lemma near_hop {N : Side} {U : RLink N K} (he : 0≤e) (h : PlaqBound R U e) (b : Site N) (l w : Walk) (g : stop (0:Cover) l=stop (0:Cover) w) :
    cmp R (travel U b l) (travel U b w) ≤ 4*(l.length:ℝ)^2*e+4*(w.length:ℝ)^2*e := by
  simpa only [compareW,travel_at,map_zero,zero_add] using near_walk he (taurus h b) _ l w g
end YM.CF.Cube
