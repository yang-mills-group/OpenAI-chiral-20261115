import YM.CF.BPress.Grid.Rim
/-! Parallel comparison in the scaled entity by <= d*b plaquette exchanges per edge. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice
open scoped BigOperators Classical
variable {G:Gauge} {d : ℕ}{s : Side}{k : Tiling s}
-- W(x,i) at stride r, NOT a unit link (unless r=1). Flat on entity stencils as indicated.
namespace Entity
variable (J : Entity k d) (W : GaugeField G d s)
def along (x:Coord d) (i:Fin d):= W (J.heart x,i)
def flat (m:ℝ) := ∀ a i j, J.Valid a → J.Valid (tick a i) → J.Valid (tick a j) → J.Valid (tick (tick a i) j) → i≠j →
    chord (J.along W a i* J.along W (tick a i) j) (J.along W a j * J.along W (tick a j) i) ≤ m
lemma flat_of_stride {m:ℝ} (V : GaugeField G d s) (h: Flat V m) (p : W=fun x=> line V x.1 x.2 k.r.val): J.flat W (↑k.r.val*↑k.r.val*m):= by
  subst W; intro a i j _ _ _ _ _; unfold along; simp_rw [step_eq]; exact h.rect .. -- tune m variable
lemma valid_tick {a:Coord d}{i : Fin d} (p : J.Valid (tick a i)) : J.Valid a:= by intro j; have h:=p j; by_cases e:j=i; subst j; rw [tick_self] at h; omega; rwa [tick_ne _ e] at h
def weight (x:Coord d):=∑ i,x i
def fall (x:Coord d)(i:Fin d): Coord d := Function.update x i (x i-1)
@[simp] lemma weight_zero : weight (0:Coord d)=0:= by simp [weight]
@[simp] lemma weight_tick (a:Coord d)(i:Fin d): weight (tick a i)=weight a+1:=by rw [weight,weight, ← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]; rw [tick_self,sum_congr rfl (fun j hj=>tick_ne _ (mem_erase.mp hj).1)]; omega
@[simp] lemma down_tick (a:Coord d)(i:Fin d) : fall (tick a i) i=a:= by ext j; by_cases h:j=i <;> simp [h,fall]
lemma tick_down {a:Coord d}{i:Fin d} (p:0<a i): tick (fall a i) i=a:=by ext j; by_cases h:j=i <;> simp [h,fall] <;> omega
lemma tick_comm (x:Coord d)(i j:Fin d):tick (tick x i) j=tick (tick x j) i:= by ext k; by_cases p:i=j; subst i; rfl; by_cases h:k=i <;> by_cases g:k=j <;> simp_all
private def first (a:Coord d)(g:a≠0): Fin d := (univ.filter fun i=>0<a i).min' (by by_contra h; simp only [not_nonempty_iff_eq_empty,filter_eq_empty_iff,mem_univ,true_implies,Nat.not_lt,Nat.le_zero] at h; exact g (funext h))
private lemma min_pos (a:Coord d)(g:a≠0) : 0<a (first a g):= (mem_filter.mp (show first a g ∈ univ.filter (fun i=>0<a i) from min'_mem ..)).2
private lemma min_le (a:Coord d)(g:a≠0)(i:Fin d)(p:0<a i): first a g ≤ i:= min'_le _ _ (by simp [p])
private lemma not_tick (a:Coord d)(i): tick a i≠0:=fun h=>Nat.succ_ne_zero (a i) ((tick_self ..).symm.trans (congrFun h i))

def carry (a : Coord d) : G.El := if h:a=0 then 1 else
    let i:= first a h
    carry (fall a i)* J.along W (fall a i) i
 termination_by weight a
 decreasing_by
    have he:= tick_down (min_pos a h)
    apply Nat.lt_of_succ_le; exact ((weight_tick (fall a i) i).symm.trans (congrArg weight he)).le
private lemma carry_up (a:Coord d)(i:Fin d)(p:i= first (tick a i) (not_tick _ _)) : J.carry W (tick a i)=J.carry W a*J.along W a i:=by
 rw [carry,dif_neg (not_tick _ _),←p]; simp
lemma carry_defect {m:ℝ} (h:J.flat W m) (e : 0≤m) (a:Coord d)(i:Fin d)(p:J.Valid (tick a i)) :
   chord (J.carry W (tick a i)) (J.carry W a*J.along W a i) ≤ weight a * m := by
 suffices ∀ n:ℕ, ∀ (a:Coord d), weight a ≤ n →∀ i, J.Valid (tick a i) → chord (J.carry W (tick a i)) (J.carry W a* J.along W a i) ≤ weight a * m from this _ _ le_rfl _ p
 intro n; induction n using Nat.strong_induction_on with| h n ih =>
  intro a l i ha; let j:=first (tick a i) (not_tick _ _); by_cases hj:i=j; rw [J.carry_up W a i hj,chord.refl]; positivity
  have he := min_pos (tick a i) (not_tick _ _); change 0<tick a i j at he; rw [tick_ne _ (Ne.symm hj)] at he
  let b:=fall a j; have hz:tick b j=a:=tick_down he; have vb:weight b+1=weight a:=(weight_tick b j).symm.trans (congrArg weight hz); have hB:J.Valid a:=J.valid_tick ha; let x:=tick b i; have hw: tick x j=tick a i:=by rw [show x=tick b i from rfl,tick_comm,hz]
  have hx:j=first a (fun h=>by rw [h] at he; exact lt_irrefl 0 he):= by
    let oo:= first a (fun h=>by rw [h] at he; exact lt_irrefl 0 he); apply le_antisymm _ (min_le a _ j he); apply min_le; have hp:=min_pos a (fun h=>by rw [h] at he; exact lt_irrefl 0 he); by_cases p:i=oo; change 0<tick a i oo; rw [←p,tick_self]; omega; rw [tick_ne]; exact hp; exact Ne.symm p
  have u:J.Valid x:= J.valid_tick (hw.symm ▸ ha)
  have dx:=ih (weight b) (by omega) b le_rfl i u
  have hy:J.carry W (tick a i)= J.carry W x* J.along W x j:=hw ▸ J.carry_up W x j (by simp only [hw]; rfl)
  have hk:J.carry W a= J.carry W b*J.along W b j:=by
    have h':j= first (tick b j) (not_tick _ _):= by simpa only [hz] using hx -- tune dependent
    exact (congrArg (J.carry W) hz).symm.trans (J.carry_up W b j h')
  rw [hy,hk]; let Y:= J.carry W b; apply (chord.triangle _ ((Y*J.along W b i)*J.along W x j) _).trans; refine (add_le_add (by rw [chord.right]; exact dx) (b:=↑(weight b)*m) (d:=m) ?_).trans_eq ?_; -- args tune
  · rw [mul_assoc,mul_assoc, chord.left]; exact hz ▸ h b i j (J.valid_tick u) u (hz.symm ▸ hB) (hw.symm ▸ ha) hj
  rw [←vb]; push_cast; ring
end Entity
end YM.CF.BPress.Grid
