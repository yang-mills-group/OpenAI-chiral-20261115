import YM.CF.BProof.Double.Census
/-! build without quadratic costs in side. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Stint Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I D G Y:Type}[Fintype I][DecidableEq I][Fintype Y][DecidableEq Y]{b:Stage Y I D G}
variable [TopologicalSpace D]{p q r s:Pay} {A B C E: Raw D I} {X Z U W: Tag b}
lemma family (h:Earn p X U A)(u:Earn p X W B)(v:Earn p Z U C)(g:Earn p Z W E) : Earn (p.wage 2) (signs X Z) (signs U W) (fun x=> bill (A x) (B x) (C x) (E x)):=by
 obtain ⟨A',T,H,V,e⟩:=h; obtain ⟨B',S,L,M',y⟩:=u; obtain ⟨C',F,K,N,n⟩:=v; obtain ⟨E',U',I',D',d⟩:=g; let t(i:Seal Y)(x):= bill (A' i x) (B' i x) (C' i x) (E' i x); let f(i:Seal Y): Toll (Tree I):=Matrix.fromBlocks (Matrix.of (T i)) (Matrix.of (S i)) (Matrix.of (F i)) (Matrix.of (U' i)); refine ⟨t,f,fun i=> ⟨?_,?_⟩,⟨(p.wage 2).funding.le,?_,?_⟩,?_⟩
 · intro a k; unfold signs; simp only [t,bill,mirror, Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,(H i).frame a k,(L i).frame a k,(K i).frame a k,(I' i).frame a k]
 · have ht {x y : Tree I} {u v : I} (h:(mirror b).home x=b.home u) (j:(mirror b).home y=b.home v) {F:D→ℂ}{z}(p: Expo b i u v z F): Expo (mirror b) i x y z F:= by refine ⟨p.positive,?_,p.bounded,p.variation,p.connected⟩; rw [h,j]; exact p.triggered
   rintro (x|x) (u|u); exact ht rfl rfl ((H i).expo x u); exact ht rfl rfl ((L i).expo x u); exact ht rfl rfl ((K i).expo x u); exact ht rfl rfl ((I' i).expo x u)
 · intro i; rw [Fintype.sum_sum_type]; apply le_trans (b:=p.cash+p.cash); swap; · rw [←two_mul]; exact le_max_right ..
   cases i<;> rename_i i; exact add_le_add (V.rows i) (M'.rows i); exact add_le_add (N.rows i) (D'.rows i)
 · intro i; rw [Fintype.sum_sum_type]; apply le_trans (b:=p.cash+p.cash); swap; · rw [←two_mul]; exact le_max_right ..
   cases i<;> rename_i i; exact add_le_add (V.cols i) (N.cols i); exact add_le_add (M'.cols i) (D'.cols i)
 intro x; dsimp only; rw [e x,y x,n x,d x]; ext (i|i) (j|j)<;> simp only [t,bill, Matrix.sum_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂]
lemma billing (h:Earn p X U A)(u:Earn q X W B)(v:Earn r Z U C)(g:Earn s Z W E) : Earn (((p.lodge q).lodge (r.lodge s)).wage 2) (signs X Z) (signs U W) (fun x=> bill (A x) (B x) (C x) (E x)):=by
 let m:=p.lodge q; let H:=r.lodge s; exact family (h.change (Pay.Wide (m.lodge_left H) (p.lodge_left q))) (u.change (Pay.Wide (m.lodge_left H) (p.lodge_right q))) (v.change (Pay.Wide (m.lodge_right H) (r.lodge_left s))) (g.change (Pay.Wide (m.lodge_right H) (r.lodge_right s)))
abbrev dye (u:Tag b):= signs u u.reverseV
omit [TopologicalSpace D] in
@[local ext] lemma Tag.ext {a p:Tag b}(g:a.run=p.run): a=p:=by cases a; cases p; congr
lemma restore (u:Tag b): u.reverseV.reverseV=u:=by ext g x y; change cc (cc _) _ _=_; rw [cc_cc]
lemma elevate (u:Tag b) : signs u.reverseV u=(dye u).reverseV:=by ext g (i|i) (j|j) <;> first|rfl|exact (star_zero ℂ).symm|exact (star_star _).symm -- tune
end YM.CF.BProof.Double
