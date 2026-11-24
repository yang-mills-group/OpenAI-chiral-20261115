import YM.CF.BProof.Circle

/-! Anisotropic tori and mesh coordinates (for micro and block support bounds).
We specialize to the d-torus at common side for the grid refinements. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Function Cube Finset
variable {n : ℕ} {s : Fin n → Side}
abbrev Vertex (s : Fin n→ Side) := (i:Fin n)→ Per (s i)
abbrev Cubic (n:ℕ)(s:Side):= Vertex (fun _ : Fin n=>s)

section Metric
def dist (x y : Vertex s) := univ.sup (fun i=> delta1 (s i) (x i) (y i))
lemma dist_le {x y : Vertex s} {r : ℕ} : dist x y ≤ r ↔ ∀ i,delta1 (s i) (x i) (y i) ≤ r := by simp [dist]
lemma dist_axis (x y : Vertex s) (i) : delta1 (s i) (x i) (y i) ≤ dist x y:=dist_le.mp le_rfl i
lemma dist_symm (x y : Vertex s) : dist x y=dist y x := by unfold dist; exact congrArg _ (funext fun i => d_sym ..) -- tune
@[simp] lemma dist_self (x : Vertex s) : dist x x=0 := Nat.eq_zero_of_le_zero (dist_le.mpr fun i=> (d_id _).le)
lemma triangle (x y z : Vertex s) : dist x z ≤ dist x y + dist y z:= dist_le.mpr fun i=> (d_one_triangle ..).trans (Nat.add_le_add (dist_axis x y i) (dist_axis y z i))
lemma dist_zero {x y:Vertex s} (h: dist x y=0) : x=y:=funext fun i=> d_equal _ _ (Nat.eq_zero_of_le_zero (dist_le.mp h.le i))

def slide (x : Vertex s) (i : Fin n) := update x i (x i+1)
@[simp] lemma slide_i (x:Vertex s)(i:Fin n) : slide x i i=x i+1:=by simp [slide]
lemma slide_at (x:Vertex s){i j:Fin n} (h:j≠i) : slide x i j=x j:=by rw [slide,update_of_ne h]
lemma slide_slide (x:Vertex s)(i j:Fin n): slide (slide x i) j= slide (slide x j) i:=by
 by_cases h:i=j; rw [h]
 ext k; by_cases g:k=i; subst k; rw [slide_at _ h,slide_i,slide_i, slide_at _ h]
 by_cases v:k=j; subst k; rw [slide_at _ (Ne.symm h),slide_i,slide_i, slide_at _ (Ne.symm h)]
 rw [slide_at _ v,slide_at _ g,slide_at _ g,slide_at _ v]
@[simp] lemma near_slide (x:Vertex s)(i:Fin n) : dist x (slide x i) ≤ 1:=by
 rw [dist_symm]; apply dist_le.mpr; intro j; by_cases h:j=i
 · subst j; rw [slide_i, delta1,add_sub_cancel_left,ZMod.valMinAbs_natAbs_eq_min]; exact (min_le_left ..).trans (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le ..)
 rw [slide_at _ h,d_id]; decide
end Metric
section Mesh
variable {c s f : Side} (g : Ratio c s) (u : Ratio s f)

def grow (x : Cubic n c) : Cubic n s := fun i=> base g (x i)
lemma highest (x y:Cubic n c)(i) : delta1 s (grow g x i) (grow g y i)=delta1 c (x i) (y i)*g.count.val:=by
 let a:=x i; let b:=y i
 change delta1 _ (base g a) (base g b)=delta1 c a b*_
 let p : Site c:=fun _=>a; let q : Site c:=fun _=>b
 have h : base g a-base g b=(g.embed (p-q)) 0:=by
    rw [← Ratio.root_embed,map_sub]; rfl
 rw [delta1,h]; change (lift (g.embed _) 0).natAbs=_
 rw [Ratio.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul]; rw [mul_comm]; rfl
lemma reach (x y : Cubic n c) : dist (grow g x) (grow g y)=dist x y * g.count.val:=by
 simp_rw [dist,highest]
 have h (f:Fin n→ℕ)(i:Finset (Fin n))(k:ℕ): (i.sup fun i=> f i*k)=i.sup f*k:=by
    induction i using Finset.induction_on with| empty=>simp| @insert j i h ih=> rw [sup_insert,sup_insert,ih]; exact (max_mul_mul_right ..) -- tune
 exact h _ _ _

def elder (x:Cubic n s):Cubic n c:=fun i=> block g (x i)
def here (x:Cubic n s)(i:Fin n):= part g (x i)
lemma close (x : Cubic n s) : dist x (grow g (elder g x)) ≤ g.count.val:= dist_le.mpr fun i=>by
 let a:= elder g x; let b:=here g x i; have ht:b.val<s.val:=b.isLt.trans_le (count_le g)
 have hh : grow g a i + b.val=x i:= glue_block g (x i)
 apply le_trans ((delta_eq _ _).trans_le (min_le_left ..))
 conv_lhs => rw [← hh,along_add _ ht]
 exact b.isLt.le
@[simp] lemma elder_grow (x:Cubic n c):elder g (grow g x)=x:=funext fun i=>by simpa only [elder,grow,Nat.cast_zero,add_zero] using block_add g (x i) (ha:=g.count.property)

def nest : Ratio c f:=⟨g.count*u.count,by rw [u.exact_size,g.exact_size,PNat.mul_coe,Nat.mul_assoc]⟩
@[simp] lemma nest_base (x:Per c): base (nest g u) x=base u (base g x):=by rw [← ZMod.natCast_zmod_val x,base_nat,base_nat,← Nat.cast_mul (α:=Per s),base_nat,show (nest g u).count.val=g.count.val*u.count.val from rfl]; push_cast; ring
@[simp] lemma grow_nest (x:Cubic n c): grow (nest g u) x=grow u (grow g x):=funext fun i=> nest_base g u _

def jump (x:Cubic n s)(i:Fin n)(a:ℕ):Cubic n s:=update x i (x i+a)
@[simp] lemma jump_at (x:Cubic n s)(i:Fin n)(a:ℕ) : jump x i a i=x i+a:=by simp [jump]
@[simp] lemma jump_off (x:Cubic n s){i j:Fin n}(a:ℕ)(h:j≠i):jump x i a j=x j:=by rw [jump,update_of_ne h]
@[simp] lemma jump_zero (x:Cubic n s)(i:Fin n) : jump x i 0=x:=by simp [jump]
@[simp] lemma jump_one (x:Cubic n s)(i:Fin n) : jump x i 1=slide x i:=by simp [jump,slide]
lemma jump_add (x:Cubic n s)(i:Fin n)(a b:ℕ) : jump x i (a+b)=jump (jump x i a) i b:=by simp [jump, add_assoc]
lemma jump_jump (x:Cubic n s)(i j:Fin n)(a b:ℕ) : jump (jump x i a) j b=jump (jump x j b) i a:=by
 by_cases h:i=j; subst i; rw [←jump_add,←jump_add,add_comm];
 ext k; by_cases g:k=i; subst k; simp [h];
 by_cases v:k=j; subst k; simp [Ne.symm h]; simp [g,v]
lemma slide_jump (x:Cubic n s)(i j:Fin n)(a:ℕ): slide (jump x i a) j=jump (slide x j) i a := by rw [← jump_one,←jump_one,jump_jump]
lemma jump_succ (x:Cubic n s)(i:Fin n)(a:ℕ): jump x i (a+1)=slide (jump x i a) i:=by rw [jump_add,jump_one]
lemma grow_jump (x:Cubic n c)(i:Fin n)(a:ℕ):grow g (jump x i a)=jump (grow g x) i (a*g.count.val):=by
 ext j; unfold grow; by_cases h:j=i; subst j; simp [mul_comm]
 simp [h]
lemma grow_step (x:Cubic n c)(i:Fin n):grow g (slide x i)=jump (grow g x) i g.count.val:=by rw [←jump_one,grow_jump,one_mul]
lemma near_jump (x:Cubic n s)(i:Fin n)(a:ℕ) : dist x (jump x i a) ≤ a:=by
 induction a with |zero=>simp|succ a ih=> rw [jump_succ]; exact (triangle x (jump x i a) _).trans (Nat.add_le_add ih (near_slide ..))
end Mesh
end YM.CF.BProof.Grid
