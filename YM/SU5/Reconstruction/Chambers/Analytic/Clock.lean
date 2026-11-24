import YM.SU5.Reconstruction.Chambers.Node
/-!
# Interior phase on multi-point compass clocks. Cost inside each axis cone of orders.

Can use with either side of a Hermitian pairing. Positive real parts required
on all active gaps, spacetime domains are finite probes already.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
open Function Filter Metric Set Analysis SelectionAnalysis OS
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal Classical
open Schedule Fixture Compose
open OS.Semigroup

variable {α : Type} {Γ : AddSubgroup ℝ} {j : Axis} {H : Hilbert}
local notation "R" => (Axis→ℝ)
local notation "M" => (Axis→Γ)
variable (S : OS.Semigroup H j) (G : Fixture Γ α) (W : α → H.Op)
variable (p : α→(Axis→ℝ)) (q : Axis→ℝ)
-- only spatial directions of p,q needed for creative launch.
variable (z : α → ℂ) (e : ℂ) (l : List α)

def go (j : Axis) (z : α→ℂ) (i:α) : ℂ:= z i + (((G.low i j):ℝ):ℂ)
def halt (j : Axis) (z : α→ℂ) (i:α) : ℂ:= go G j z i + (((G.width i j):ℝ):ℂ)

def ferry (p : (Axis→ℝ) × ℂ) : H.Op := (S.F p.2).comp (S.U (diameter p.1))

def curve : H.Op := roll (fun _ => ferry S) W (fun i=> (p i,go G j z i)) (fun i=>(p i,halt G j z i)) (q,e) l
lemma order_step (i : α) : curve S G W p q z e (i::l)=
    ( ( S.F (go G j z i - e)).comp (S.U (diameter (p i-q)))).comp ((W i).comp (curve S G W p (p i) z (halt G j z i) l)) := rfl

variable {z}
def ProperCone (j : Axis) (z : α→ℂ) : ℂ → List α→ Prop
| _,[] => True
| e,i::l=> 0 < (go G j z i - e).re ∧ ProperCone j z (halt G j z i) l

def upright : ℝ := (l.map (fun i=>‖W i‖)).prod
lemma cost_pos : 0 ≤ upright W l := List.prod_nonneg (s:=l.map fun i=>‖W i‖) (by intro x e; obtain ⟨i,v,rfl⟩:=List.mem_map.mp e; exact norm_nonneg _) -- name
local notation "C" => curve S G W

lemma spin_price (z : α→ℂ) (w : ProperCone G j z e l) (x:H) : ‖curve S G W p q z e l x‖ ≤ upright W l * ‖x‖ := by
  induction l generalizing q e with
  | nil => rw [upright,List.map_nil,List.prod_nil,one_mul]; exact le_rfl
  | cons i l ih =>
    obtain ⟨r,t⟩:= w; rw [order_step]; let f:= curve S G W p (p i) z (halt G j z i) l x
    let v:=S.U (diameter (p i-q)) (W i f)
    refine ((S.F (go G j z i - e)).le_opNorm v |>.trans (mul_le_of_le_one_left (norm_nonneg v) (S.norm_row r))).trans ?_
    change ‖(S.U _) _‖ ≤ (‖W i‖*upright W l) * ‖x‖; rw [S.unitary, mul_assoc]; exact ((W i).le_opNorm f).trans (mul_le_mul_of_nonneg_left (ih _ _ t -- tune
       ) (norm_nonneg _))

lemma curve_diff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] (x : H) (k:A)
   {z:A→α→ℂ} (e:A→ℂ) (dz : ∀ i, DifferentiableAt ℂ (fun a=> z a i) k) (de : DifferentiableAt ℂ e k)
   (w : ProperCone G j (z k) (e k) l) : DifferentiableAt ℂ (fun a=> curve S G W p q (z a) (e a) l x) k := by
  induction l generalizing q e with
  | nil=> exact differentiableAt_const _
  | cons i l ih=>
    have s : DifferentiableAt ℂ (fun a=>go G j (z a) i) k := (dz _).add_const _
    obtain ⟨r,t⟩ := w
    have h : DifferentiableAt ℂ (fun a=>S.F (go G j (z a) i - e a)) k := by
      apply DifferentiableAt.comp (f:=(fun a=>go G j (z a) i)-e) (g:=S.F) k ((S.localHeat _ r).differentiableAt); exact s.sub de
    simp_rw [order_step,ContinuousLinearMap.comp_apply]; refine h.clm_apply ?_
    exact (S.U _).differentiableAt.comp _ ((W i).differentiableAt.comp _ (ih _ (fun a=>halt G j (z a) i) (s.add_const _) t))

private lemma go_real(i:α) (w : ∀ i:α,z i=p i j) : go G j z i = (((G.start j p i j):ℝ):ℂ) := by
  simp only [go, w, start,Pi.add_apply,Pi.single_eq_same]; push_cast; rfl
private lemma halt_real (i : α) (w : ∀ i:α,z i=p i j) : halt G j z i= (((G.stop j p i j):ℝ):ℂ) := by
  simp [halt, go_real G p i w, stop]

lemma diameter_eq {v q : Axis→ℝ} (h : ∀ i: Axis,i≠j→ v i=q i) :
    diameter (a:=j) q = diameter v := by
  apply Subtype.ext; ext i; by_cases b:i=j
  · subst i; exact (diameter (a:=j) q).property.trans (diameter (a:=j) v).property.symm -- E4 notation proof orientation
  exact ((diameter_at q _ b).trans (h i b).symm).trans (diameter_at v _ b).symm

-- cone can use any update of t_i, keeping spectator sets. q time arbitrary.
variable (p' : α→Axis→ℝ) (q' : Axis→ℝ)
lemma real_points (h : G.permission j true p' q' l)
    (w : ∀ k:Axis, k≠j → q k=q' k ∧ ∀ i:α,p i k=p' i k) (t : ∀ i : α,z i=p' i j) :
    curve S G W p q z (q' j) l=pointsOp S G W p' q' l := by
  induction l generalizing q q' with
  | nil=>rfl
  | cons i l ih=>
    have ht : ∀ k:Axis,k≠ j → p i k=G.stop j p' i k ∧ ∀ i:α,p i k=p' i k := by
       intro k b; refine ⟨?_, (w k b).2⟩; simpa [stop,start,b] using (w k b).2 i
    rw [permission_step] at h; have hh : 0 < (G.start j p' i-q') j := h.1
    let a := (G.start j p' i-q') j; let u:=a.toNNReal
    have he : go G j z i - ((q' j:ℝ):ℂ) = duration u := by rw [go_real G p' i t]; unfold u a duration; rw [Real.coe_toNNReal _ hh.le,Pi.sub_apply,Complex.ofReal_sub] -- Pi sub
    rw [order_step,halt_real G p' i t,ih _ _ h.2 ht,he,S.roots_heat (Real.toNNReal_pos.mpr hh)]
    have hp: diameter (a:=j) (G.start j p' i-q')=diameter (a:=j) (p i-q) := by apply diameter_eq; intro k b; simp [start,b,(w k b).1,(w k b).2]
    unfold pointsOp route; rw [roll_step]; rw [hp]

lemma can_go (h : G.permission j true p q l) (s : ∀ i:α,(z i).re=p i j) : ProperCone G j z (q j:ℂ) l := by
  suffices t : ∀ u:ℂ, u.re=q j → ProperCone G j z u l by exact t _ (Complex.ofReal_re _)
  intro u v; induction l generalizing u q with
  | nil=> trivial
  | cons i l ih=>
    have he : (go G j z i).re=G.start j p i j := by simp [go,start,s]
    rw [permission_step] at h; refine ⟨?_, ih _ h.2 _ ?_⟩
    · rw [Complex.sub_re,he,v]; exact h.1
    simp [halt,he,stop]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
