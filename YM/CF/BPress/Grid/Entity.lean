import YM.CF.BPress.Grid.Line
/-!
Entities of the r*b scaffold and their (b+1)-grid, including all boundary points.
Works with wraparound. Need r*b <s; NO unidentified seam.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice Cube MeasureTheory
open scoped BigOperators Classical
variable {d : ℕ} {s : Side}

/-- r-sized grid inside (r*b) mesh tiles. -/
structure Tiling (s : Side) where
  r : Side
  b : Side
  divides : (r*b).val ∣ s.val
  strict : (r*b).val < s.val
namespace Tiling
variable (k : Tiling s)
def R : ℕ := k.r.val * k.b.val
lemma R_pos : 0<k.R := Nat.mul_pos k.r.property k.b.property
lemma dvds : k.r.val ∣ s.val:=dvd_trans (show k.r.val ∣ k.R from dvd_mul_right ..) k.divides
end Tiling
variable {k:Tiling s}
structure Entity (k : Tiling s)(d:ℕ) where
  origin : Space d s
  coarse : origin∈mesh k.R
  axes : Finset (Fin d)
attribute [ext] Entity
noncomputable instance : Fintype (Entity k d):=by
  let f : Entity k d→ _ := fun x=> (x.origin,x.axes)
  letI : Finite (Entity k d):= Finite.of_injective f <| fun i j h=> Entity.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact Fintype.ofFinite _

abbrev Coord (d:ℕ) := Fin d→ℕ
def tick (x: Coord d)(i:Fin d) : Coord d:= Function.update x i (x i+1)
@[simp] lemma tick_self (x:Coord d)(i:Fin d): tick x i i=x i+1:= update_self ..
@[simp] lemma tick_ne (x:Coord d){i j:Fin d}(p:i≠j): tick x j i=x i:= update_of_ne p ..

namespace Entity
variable (J:Entity k d){a b:Coord d}{i:Fin d}
def Valid (a:Coord d) := ∀ i, a i ≤ if i∈J.axes then k.b.val else 0
def heart (a:Coord d): Space d s := fun i=> J.origin i+ ↑(k.r.val*a i)
def contains (x:Space d s) := ∃ a, J.Valid a ∧ J.heart a=x
def hull : Finset (Space d s) := univ.filter J.contains -- tune Seal
@[simp] lemma valid_zero : J.Valid 0:= fun _=>Nat.zero_le _
@[simp] lemma heart_zero : J.heart 0=J.origin:=by ext; simp [heart]
lemma dim_off (h:J.Valid a) (p:i∉J.axes): a i=0:= by have he:=h i; rw [if_neg p] at he; omega
lemma dim_max (h:J.Valid a)(i:Fin d) : a i≤k.b.val:= (h i).trans (by split; rfl; omega)
lemma cost_coord (p:J.Valid a)(i:Fin d): k.r.val*a i ≤ k.R:= Nat.mul_le_mul_left _ (J.dim_max p i)
lemma on_grid (a: Coord d) : J.heart a ∈ mesh k.r.val := by
 intro i; apply aligned_add k.dvds _ ((align_subdiv _ J.coarse (show k.r.val ∣ k.R from dvd_mul_right ..)) i) (dvd_mul_right ..)
lemma step_eq (a:Coord d)(i:Fin d): J.heart (tick a i)=hop (J.heart a) i k.r.val:=by
 funext j; by_cases p:j=i <;> simp [p,heart,mul_add,add_assoc]
lemma span (p:J.Valid a) : delta J.origin (J.heart a)≤k.R:= by refine delta_le.mpr fun i=>?_ ; rw [d_sym]; exact (delta_nat ..).trans (J.cost_coord p i)
lemma inject (p:J.Valid a)(h:J.Valid b)(e:J.heart a=J.heart b): a=b:=by
 funext i; have he:=congrFun e i; unfold heart at he; have ht:=congrArg ZMod.val (add_left_cancel he); rw [ZMod.val_natCast_of_lt ((J.cost_coord p i).trans_lt k.strict),ZMod.val_natCast_of_lt ((J.cost_coord h i).trans_lt k.strict)] at ht; exact Nat.eq_of_mul_eq_mul_left k.r.property ht
/-- One coordinate at a boundary. -/
def OnFace (a:Coord d)(i:Fin d)(t:Bool):Prop:= i∈J.axes ∧ a i=if t then k.b.val else 0
def Boundary (a:Coord d):= ∃ i t, J.OnFace a i t
lemma when_align (p:J.Valid a)(i:Fin d) : aligned (J.heart a i) k.R ↔ a i=0 ∨ a i=k.b.val:=by
 rw [heart,aligned_add_iff (r:=k.R) k.divides _ (J.coarse i)]; constructor
 · intro h; by_cases g:a i=0; · exact Or.inl g
   have ht:=Nat.le_of_dvd (Nat.mul_pos k.r.property (Nat.pos_of_ne_zero g)) h; exact Or.inr (le_antisymm (J.dim_max p i) (Nat.le_of_mul_le_mul_left ht k.r.property))
 rintro (h|h) <;> rw [h]; simp; rfl

def wall (i : Fin d)(t:Bool) : Entity k d where
  origin := if t then hop J.origin i k.R else J.origin
  coarse := by split; exact mesh_hop J.coarse k.divides (dvd_refl _) _; exact J.coarse
  axes := J.axes.erase i
lemma wall_axes (i t) : (J.wall i t).axes⊆ J.axes:= erase_subset _ _
lemma wall_mo (h:i∈J.axes)(t): (J.wall i t).axes.card+1=J.axes.card:= card_erase_add_one h
lemma wall_coord {t:Bool} (p : J.OnFace a i t)(h:J.Valid a):
    (J.wall i t).Valid (Function.update a i 0) ∧ (J.wall i t).heart (Function.update a i 0)=J.heart a := by
  constructor
  · intro l; by_cases g:l=i
    · simp [g]
    rw [Function.update_of_ne g]; simpa [wall,g] using h l
  ext l; by_cases e:l=i; subst l; cases t <;> simp [p.2,heart,wall,Tiling.R]
  unfold heart; cases t <;> simp [wall,e]
end Entity
-- rank
variable (k)
def rankSet (x : Space d s) := univ.filter fun i=> ¬ aligned (x i) k.R
@[simp] lemma rankSet_mem (x : Space d s) (i): i∈rankSet k x ↔ ¬ aligned (x i) k.R:=by simp [rankSet]
variable (J : Entity k d){i:Fin d}{a : Coord d}
lemma rank_le (p:J.Valid a) : rankSet k (J.heart a) ⊆ J.axes:=by
 intro i h; by_contra e; exact ((rankSet_mem ..).mp h) ((J.when_align p i).mpr (.inl (J.dim_off p e)))
lemma rank_eq (p:J.Valid a): rankSet k (J.heart a)=J.axes ↔ ¬ J.Boundary a:=by
  constructor
  · rintro h ⟨i,t,u,e⟩; have hv:= (rankSet_mem ..).mp (h.symm ▸ u); apply hv; apply (J.when_align p i).mpr; cases t <;> tauto
  intro h; refine Finset.Subset.antisymm (rank_le k J p) ?_; intro i t; rw [rankSet_mem]; intro u; rcases (J.when_align p i).mp u with x|x; exact h ⟨i,false,t,x⟩; exact h ⟨i,true,t,x⟩
-- uniqueness of enclosing tile on each nonaligned coordinate
private lemma unique_axis {x y : Per s}(p : aligned x k.R)(t : aligned y k.R)(u v : ℕ) (h:u<k.R)(l:v<k.R)
    (g : x + ↑u=y + (v:Per s)):u=v:=by
  have asymm (x y:Per s) (p:aligned x k.R)(t: aligned y k.R)(u v:ℕ)(h:u<k.R)(l:v<u) (g:x+ ↑u=y+(v:Per s)) : False:=by
    have he:x+(↑(u-v):Per s)=y:= by rw [Nat.cast_sub l.le ,←add_sub_assoc,← eq_sub_of_add_eq (a:=y) g.symm]
    have hv:u-v<k.R:=by omega
    exact hv.not_ge (Nat.le_of_dvd (by omega) ((aligned_add_iff k.divides _ p _).mp (he.symm ▸ t)))
  exact le_antisymm (le_of_not_gt fun e=> asymm x y p t u v h e g) (le_of_not_gt fun e=>asymm y x t p v u l e g.symm)
lemma interior_unique (A:Entity k d){b : Coord d}(u:J.Valid a)(v:A.Valid b)(p:¬J.Boundary a)(q:¬A.Boundary b)(e:J.heart a=A.heart b): J=A:= by
  apply Entity.ext ?_ ((rank_eq _ J u).2 p|>.symm.trans ((congrArg _ e).trans ((rank_eq _ A v).2 q)))
  ext i; have he (J:Entity k d)(a:Coord d)(h:J.Valid a)(p:¬J.Boundary a): k.r.val*a i<k.R:= by
    apply Nat.mul_lt_mul_of_pos_left _ k.r.property; refine lt_of_le_of_ne (J.dim_max h i) (fun e=>?_); by_cases g:i∈J.axes; exact p ⟨i,true,g,e⟩; have t:=J.dim_off h g; have hh:k.b.val≠0:=Nat.ne_of_gt k.b.property; omega
  have hk:=congrFun e i; have hh:= unique_axis _ (J.coarse i) (A.coarse i) _ _ (he J a u p) (he A b v q) hk; unfold Entity.heart at hk; rw [hh] at hk; exact add_right_cancel hk

/-- every forward r-edge of mesh is some entity edge. -/
lemma mesh_coord {x:Space d s} (t:x∈mesh k.r.val) : ∃ J : Entity k d, ∃ a : Coord d, J.heart a=x ∧ ∀ i, J.Valid (tick a i) ∧ a i < k.b.val ∧ J.Valid a :=by
 have he(i:Fin d): ∃ y:Per s,∃ a:ℕ, aligned y k.R ∧ a < k.b.val ∧ x i=y+ ↑(k.r.val*a):=by
    obtain ⟨y,h,j,p,H⟩:=mesh_arises x (k.r*k.b) k.divides i; have hg:k.r.val∣j:=(aligned_add_iff k.dvds y (dvd_trans (show k.r.val∣ k.R from dvd_mul_right ..) h) j).mp (H ▸ t i)
    obtain ⟨a,hg⟩:=hg; subst j; exact ⟨y,a,h,lt_of_mul_lt_mul_left p (by omega : 0≤k.r.val),H⟩
 choose y a h p v using he; let J:Entity k d:=⟨y,h,univ⟩; have ht:J.Valid a:=fun i=>by rw [if_pos (show i∈ J.axes from mem_univ _)]; exact (p i).le
 refine ⟨J,a,funext fun i=>(v i).symm, fun i=>⟨?_,p i,ht⟩⟩; intro j; change tick a i j ≤ if j∈ univ then _ else _; by_cases g:j=i; rw [g,tick_self,if_pos (mem_univ _)]; exact p i; rw [tick_ne _ g]; exact ht j
-- note `mesh_coord` if d=0 use ht separately in uses, conclusion edge property is empty.
end YM.CF.BPress.Grid
