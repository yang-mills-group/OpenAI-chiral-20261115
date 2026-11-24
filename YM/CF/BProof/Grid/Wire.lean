import YM.CF.BProof.Grid.Entity
import YM.CF.BProof.Chord
/-! Plaquette transport from the actual links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Function Gauge Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n : ℕ} (s : Side)
abbrev Link (n : ℕ) (s : Side) := (Cubic n s) × Fin n
abbrev Wire (G : Gauge) (n : ℕ) (s : Side):= Link n s → G.El

variable {G : Gauge} {c f : Side} {s}
namespace Wire
variable (G) (U : Wire G n s)
def Flat (V : Set (Cubic n s)) (m : ℝ): Prop := ∀ x i j,x∈V→ slide x i∈ V→slide x j∈V→slide (slide x i) j∈V→ cd G (U (x,i)*U (slide x i,j)) (U (x,j)*U (slide x j,i)) ≤ m

def Along (F : Set (Cubic n s)) (i : Link n s) := i.1∈F ∧ slide i.1 i.2 ∈ F

def Agrees (V: Set (Cubic n s)) (U U' : Wire G n s) := ∀ i,Along V i → U i=U' i -- G argument implicit? command variable (G) gives explicit

def line (x : Cubic n s) (i : Fin n) : ℕ→ G.El
 | 0 => 1
 | a+1 => line x i a * U (jump x i a,i) -- parameter G U before rw
@[simp] lemma line_zero (x:Cubic n s)(i): line G U x i 0=1:=rfl
@[simp] lemma line_one (x:Cubic n s)(i): line G U x i 1=U (x,i):=by simp [line]
lemma line_add (x:Cubic n s)(i)(a b) : line G U x i (a+b)=line G U x i a*line G U (jump x i a) i b:=by
 induction b with |zero=>simp|succ b ih=> rw [←Nat.add_assoc,line,line,ih,jump_add,mul_assoc]
@[fun_prop] lemma continuous_line (x:Cubic n s)(i a): Continuous (fun U: Wire G n s=> line G U x i a):=by induction a with|zero=> exact continuous_const|succ a ih=> exact ih.mul (continuous_apply _)
lemma line_eq (W: Wire G n s) {V : Set (Cubic n s)}(x:Cubic n s)(i a) (h : ∀ j≤a,jump x i j∈V)(p: Wire.Agrees G V U W): line G U x i a=line G W x i a:=by
 induction a with |zero=>rfl|succ a ih=> rw [line, line, ih (fun j hj=> h j (by omega)), p _ ⟨h a (by omega),show slide (jump x i a) i∈ _ from jump_succ .. ▸ h (a+1) le_rfl⟩]

lemma translate (x : Cubic n s) (i j:Fin n)(a : ℕ)(V : Set (Cubic n s)) (m:ℝ) (p : Flat G U V m)
    (h : ∀ k≤a,jump x i k∈V ∧ slide (jump x i k) j∈ V) : cd G
    (line G U x i a*U (jump x i a,j)) (U (x,j)*line G U (slide x j) i a) ≤ a*m := by
 induction a with
 | zero => simp
 | succ a ih =>
   let u:= jump x i a; let l:= line G U x i a
   have hp:slide u i∈ V ∧ slide (slide u i) j ∈ V :=by rw [show slide u i=_ from (jump_succ x i a).symm]; exact h _ le_rfl
   let L:= U (slide u j,i); have he := ih fun k hk=> h k (by omega)
   rw [line,line,jump_succ x i,← slide_jump]; apply le_trans (cd_triangle G _ (l*U (u,j)*L) _)
   rw [mul_assoc (U (x,j)) (line G U (slide x j) i a) L |>.symm]; nth_rw 1 [mul_assoc]; nth_rw 1 [mul_assoc l (U (u,j))]; rw [cd_mul_left,cd_mul_right]; push_cast; rw [add_mul,one_mul,add_comm ((_ : ℝ)*m)]
   exact add_le_add (p _ i j (h a (by omega)).1 hp.1 (h a (by omega)).2 hp.2) he

lemma rectangle (x : Cubic n s) (i j : Fin n) (a b : ℕ) (m : ℝ) (p : Flat G U Set.univ m) :
    cd G (line G U x i a*line G U (jump x i a) j b) (line G U x j b*line G U (jump x j b) i a) ≤ a*b*m := by
 induction b with
 | zero=> simp
 | succ b ih=>
   let y:=jump x j b; let T:=U (jump y i a,j)
   rw [line,line,jump_jump (i:=i) (j:=j),jump_succ x j]
   apply le_trans (cd_triangle G _ ((line G U x j b*line G U y i a)*T) _)
   have he:cd G (line G U y i a * T) (U (y,j)*line G U (slide y j) i a)≤a*m:= translate G U y i j a univ m p (fun _ _ => ⟨trivial,trivial⟩) -- tune
   nth_rw 1 [← mul_assoc]; nth_rw 2 [mul_assoc (line G U x j b)]; rw [cd_mul_right,mul_assoc (line G U x j b),cd_mul_left]; push_cast; linarith
variable (g:Ratio c s)
def long : Wire G n c:=fun i=> line G U (grow g i.1) i.2 g.count.val
lemma coarse_flat (m:ℝ)(p:Flat G U univ m): Flat G (long G U g) univ ((g.count.val:ℝ)^2*m):=by
 intro x i j _ _ _ _; unfold long; dsimp only; rw [grow_step,grow_step,pow_two]; exact rectangle G U (grow g x) i j _ _ m p
lemma long_line (x:Cubic n c)(i:Fin n)(a:ℕ): line G (long G U g) x i a=line G U (grow g x) i (a*g.count.val):=by
 induction a with
 | zero=>simp
 | succ a h=>
    rw [line,Nat.succ_mul,line_add,h]; congr 2; unfold long; dsimp only; rw [grow_jump]
lemma long_nest (h : Ratio f c) : long G (long G U g) h=long G U (nest h g):=by
 ext1 i; change line G _ _ _ _ =_; rw [long_line,long,grow_nest]; rfl
end Wire
end YM.CF.BProof.Grid
