import YM.CF.BPress.Bands
import YM.CF.Support.Grove
import Mathlib.Data.Int.Interval
/-!
Strides on periodic meshes. All spans in the SAME sup metric as micro
 lattice distance, even when using strides r>1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice Cube Branch
open scoped BigOperators Classical
abbrev Space (d : ℕ)(s:Side):= Fin d → Per s
variable {d k r : ℕ} {s : Side}
def field (d:ℕ)(s:Side) : Branch.Field (Space d s) where
  span x y:= univ.sup fun i=> delta1 s (x i) (y i)
  reflex x:= by simp [delta1]
  sym x y:=congrArg (sup univ) (funext fun i=>d_sym (y i) (x i))
  tri x y z:= Finset.sup_le fun i _=> (d_one_triangle _ (y i) _).trans (add_le_add (le_sup (f:=fun i=>delta1 s (x i) (y i)) (mem_univ i)) (le_sup (f:=fun i=>delta1 s (y i) (z i)) (mem_univ i)))
abbrev delta (x y : Space d s) := (field d s).span x y
@[simp] lemma field_four (x y : Site s) : delta x y= Lattice.separation x y:= rfl
@[simp] lemma delta_same (x : Space d s) : delta x x=0:=(field d s).reflex x
lemma delta_triangle (x y z : Space d s) : delta x z ≤ delta x y+delta y z:=(field d s).tri x y z
lemma delta_comm (x y : Space d s) : delta x y=delta y x:=(field d s).sym x y
lemma delta_le {x y : Space d s} : delta x y ≤ k ↔ ∀ i, delta1 s (x i) (y i)≤ k:=by simp [delta,field]
lemma delta_at (x y : Space d s) (i) : delta1 s (x i) (y i) ≤ delta x y := delta_le.mp le_rfl i
lemma eq_of_delta (x y : Space d s)(p:delta x y=0): x=y:= funext fun i=> d_equal _ _ (Nat.eq_zero_of_le_zero ((delta_at ..).trans p.le))
lemma delta_nat (i : Per s) (k:ℕ) : delta1 s (i+(k:Per s)) i ≤ k := by rw [delta1,add_sub_cancel_left,ZMod.valMinAbs_natAbs_eq_min]; apply (min_le_left ..).trans; rw [ZMod.val_natCast]; exact Nat.mod_le ..

/-- step forward k -/
def hop (x : Space d s) (i : Fin d) (k:ℕ) := x + Pi.single i (k:Per s)
/-- j-th coordinate is unchanged unless j=i -/
lemma hop_at (x : Space d s)(i : Fin d)(k:ℕ)(j : Fin d) : hop x i k j = if j=i then x j+↑k else x j:=by by_cases p:j=i<;>simp [hop,p,Pi.single_apply]
@[simp] lemma hop_same (x : Space d s) (i : Fin d)(k:ℕ) : hop x i k i=x i+ ↑k :=by rw [hop_at,if_pos rfl]
@[simp] lemma hop_diff (x : Space d s)(i j : Fin d)(h:j≠i)(k:ℕ) : hop x i k j=x j:=by rw [hop_at,if_neg h]
@[simp] lemma hop_zero (x : Space d s) (i : Fin d) : hop x i 0=x:=by simp [hop]
lemma hop_one (x : Site s) (i : Axis) : hop x i 1=x+ step i:= by unfold hop step; simp
lemma hop_glide (x : Tri s) (i : Fin 3) : hop x i 1=glide i x:=by funext j; rw [hop_at]; simp [glide,Fin.tail]; split <;> simp
lemma hop_comm (x : Space d s) (i j : Fin d)(p q:ℕ) : hop (hop x i p) j q=hop (hop x j q) i p:= by unfold hop; abel
@[simp] lemma hop_hop (x : Space d s) (i : Fin d)(p q:ℕ) : hop (hop x i p) i q=hop x i (p+q):=by
  ext j; by_cases t:j=i <;> simp [t,add_assoc]
lemma delta_hop (x : Space d s)(i : Fin d)(p:ℕ) : delta x (hop x i p)≤ p:= by rw [delta_comm]; refine delta_le.mpr fun j=>?_ ; by_cases k:j=i; subst j; rw [hop_same]; exact delta_nat ..; rw [hop_diff _ _ _ k,d_id]; omega

def aligned (b : Per s)(r:ℕ) := r ∣ b.val
def mesh (r:ℕ) := {x:Space d s| ∀ i, aligned (x i) r}
lemma align_zero(r:ℕ) : aligned (0:Per s) r:=by simp [aligned]
lemma align_subdiv (x : Space d s)(h:x∈mesh r)(t:k∣r) : x∈mesh k:= fun i=> dvd_trans t ((show ∀ i, aligned (x i) r from h) i)
lemma aligned_add (p:r∣s.val)(i:Per s)(h:aligned i r)(g:r∣k) : aligned (i+(k:Per s)) r:= by unfold aligned; rw [ZMod.val_add,ZMod.val_natCast]; exact (Nat.dvd_mod_iff p).mpr (Nat.dvd_add h ((Nat.dvd_mod_iff p).mpr g))
lemma aligned_add_iff (p:r∣s.val)(i:Per s)(h:aligned i r)(k:ℕ) : aligned (i+(k:Per s)) r ↔ r∣k:= by
 refine ⟨fun t=> ?_,aligned_add p i h⟩; unfold aligned at *; rw [ZMod.val_add,ZMod.val_natCast,Nat.add_mod_mod] at t; exact (Nat.dvd_add_right h).mp ((Nat.dvd_mod_iff p).mp t) -- tune
lemma aligned_of_add (p:r∣s.val)(i:Per s)(h:aligned (i+(k:Per s)) r)(t:r∣k) : aligned i r:=by unfold aligned at *; rw [ZMod.val_add,ZMod.val_natCast,Nat.add_mod_mod] at h; exact (Nat.dvd_add_left t).mp ((Nat.dvd_mod_iff p).mp h)
lemma mesh_hop {x:Space d s}(h:x∈mesh r)(p:r∣s.val)(t:r∣k)(i:Fin d): hop x i k∈mesh r:= by
  intro j; change aligned (hop x i k j) r; by_cases g:j=i; subst j; rw [hop_same]; exact aligned_add p _ ((show ∀ i,_ from h) i) t -- tune subst
  rw [hop_diff x _ _ g]; exact h j

def backs (x : Space d s)(i : Fin d)(k:ℕ):= x-Pi.single i (k:Per s)
@[simp] lemma hop_backs (x : Space d s)(i : Fin d)(k:ℕ): hop (backs x i k) i k=x:=by rw [hop,backs]; abel
@[simp] lemma backs_hop (x : Space d s)(i : Fin d)(k:ℕ): backs (hop x i k) i k=x:=by rw [backs,hop]; abel
lemma backs_eq (x y : Space d s)(i:Fin d)(k:ℕ):hop x i k=y ↔ x=backs y i k:=by constructor; intro h; rw [←h]; simp; intro h; rw [h,hop_backs]
lemma hop_fixed_iff (x : Space d s)(i : Fin d)(p q:ℕ)(h : p < s.val)(t : q < s.val) : hop x i p=hop x i q ↔ p=q:=by
  refine ⟨fun e=>?_,fun p=>congrArg _ p⟩; have he:=congrFun e i; rw [hop_same,hop_same] at he; have ht:=congrArg ZMod.val (add_left_cancel he); rwa [ZMod.val_natCast_of_lt h,ZMod.val_natCast_of_lt t] at ht
lemma mesh_arises (x : Space d s)(r:Side)(h:r.val∣s.val) (i : Fin d) : ∃ u : Per s, aligned u r.val ∧ ∃ k, k<r.val ∧ x i = u+ ↑k:=by
 let a:= (x i).val; let q:=r.val *(a/r.val); have hp:q+a%r.val=a:=Nat.div_add_mod a r.val; refine ⟨(q:Per s),?_, a%r.val,Nat.mod_lt _ r.property,?_⟩
 · unfold aligned; rw [ZMod.val_natCast]; exact (Nat.dvd_mod_iff h).mpr (dvd_mul_right ..)
 rw [← Nat.cast_add,hp]; exact (ZMod.natCast_zmod_val _).symm
end YM.CF.BPress.Grid
