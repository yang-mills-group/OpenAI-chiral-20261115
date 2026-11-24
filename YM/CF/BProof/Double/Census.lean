import YM.CF.BProof.Stint.Functional
import YM.CF.BProof.Double.Oblong
/-! Rooted doubled prices. These are still costs for parameter-dependent, possibly
far-reaching functions. Exponential uniformly positive. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Stint Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I D G Y:Type}[Fintype I][DecidableEq I][Fintype Y][DecidableEq Y]{b:Stage Y I D G}
def mirror (b:Stage Y I D G):Stage Y (Tree I) D G := {b with home:=Sum.elim b.home b.home }
def signs (u v : Tag b): Tag (mirror b) where
 run i:= ⟨bill (u.run i).val 0 0 (v.run i).val,Join.both_unitary (u.run i).property (v.run i).property⟩ -- tune
 keeps i x y p:=by rcases x with x|x <;> rcases y with y|y; exact u.keeps i x y p; rfl; rfl; exact v.keeps i x y p -- tune
lemma doubled {C:ℝ}(p:Capacity b C)(h:0≤C): Capacity (mirror b) (C+C):=by
 refine ⟨p.grove,fun i j=>(p.ball i j).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h) (by positivity)),fun i j=>?_⟩; rw [show board (mirror b) _=(board b (bay b.F i j)).disjSum (board b (bay b.F i j)) from ?_, Finset.card_disjSum,Nat.cast_add,add_mul]; exact add_le_add (p.place i j) (p.place i j); ext (p|p) <;> simp [board,mirror]
-- extraction
variable {X Y' Z: Tag b}
lemma sandwich (A:M I)(S T:Op I): A*bill S 0 0 T=bill (A.toBlocks₁₁*S) (A.toBlocks₁₂*T) (A.toBlocks₂₁*S) (A.toBlocks₂₂*T):=by
 conv_lhs=> rw [← Matrix.fromBlocks_toBlocks A]; simp [bill,Matrix.fromBlocks_multiply]
lemma sandwichL (A:M I)(S T:Op I) : bill S 0 0 T*A=bill (S*A.toBlocks₁₁) (S*A.toBlocks₁₂) (T*A.toBlocks₂₁) (T*A.toBlocks₂₂):=by
 conv_lhs=> rw [← Matrix.fromBlocks_toBlocks A]; simp [bill,Matrix.fromBlocks_multiply]
-- Bool notation in this tooling: true=inl.
def bind (b:Bool)(i:I): Tree I:= if b then Sum.inl i else Sum.inr i
def letter (x y: Bool)(A:M I): Op I:= A.submatrix (bind x) (bind y)
def bank (u v:Tag b)(a:Bool): Tag b:=if a then u else v
lemma bind_inj (k:Bool): Injective (bind (I:=I) k):= by cases k; exact Sum.inr_injective; exact Sum.inl_injective -- tune
lemma seat_h(u:Bool)(i:I): (mirror b).home (bind u i)= b.home i:= by cases u<;> rfl
lemma plateR(x y:Bool)(A:M I)(S T:Op I): letter x y (A*bill S 0 0 T)=letter x y A*(if y then S else T):=by rw [sandwich]; cases x <;> cases y <;> rfl
lemma plateL(x y:Bool)(A:M I)(S T:Op I): letter x y (bill S 0 0 T*A)=(if x then S else T)*letter x y A:=by rw [sandwichL]; cases x <;> cases y <;> rfl
lemma account [TopologicalSpace D] (x y:Bool) {A:D→M I}{p:Pay}{X Y Z W:Tag b}(h:Earn p (signs X Y) (signs Z W) A): Earn p (bank X Y x) (bank Z W y) (fun i=>letter x y (A i)):=by
 obtain ⟨P,U,t,g,F⟩:= h.holds; refine ⟨fun S i=>letter x y (P S i),fun S i j=>U S (bind x i) (bind y j),fun S=> ⟨?_,?_⟩, ⟨g.posP,fun i=>?_,fun i=>?_⟩,fun z=>?_⟩
 · intro i v; have hz:= congrArg (letter (I:=I) x y) ((t S).frame i v); dsimp only [signs] at hz; rw [plateR,plateL] at hz; cases x<;>cases y<;> exact hz
 · intro i j; let u:= (t S).expo (bind x i) (bind y j); refine ⟨u.positive,fun g=>?_,u.bounded,u.variation,u.connected⟩; obtain ⟨r,a,c⟩:=u.triggered g; exact ⟨r,by rwa [seat_h] at a,by rwa [seat_h] at c⟩
 · apply le_trans _ (g.rows (bind x i)); let f(j):=saleM p.rate U (bind x i) j; change ∑ j:I, f (bind y j)≤_; rw [← Finset.sum_image (g:=bind y) (s:=univ) (by exact fun _ _ _ _ h=>bind_inj y h)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> sale_nn (fun i j k=>(t i).nonn j k) ..)
 · apply le_trans _ (g.cols (bind y i)); let f(j):=saleM p.rate U j (bind y i); change ∑ j:I, f (bind x j)≤_; rw [← Finset.sum_image (g:=bind x) (s:=univ) (by exact fun _ _ _ _ h=>bind_inj x h)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> sale_nn (fun i j k=>(t i).nonn j k) ..)
 dsimp only; rw [F z]; ext i j; unfold letter; rw [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.sum_apply]; rfl
end YM.CF.BProof.Double
