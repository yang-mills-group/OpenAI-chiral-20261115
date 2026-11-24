import YM.CF.BPress.Pf.Vowels
import YM.CF.BPress.Pf.Carve
/-! eq:B-Wick quotient moments without any replacement of the oriented relative amplitudes. Products in L-R sorted type order in later use. `dues` implements row expansion (sign/erase) of that ordered Pfaffian, workable on any list. -/
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A T L C D:Op I}{u:Wave I}{X Y : Finset I}{c d r:ℝ}

structure Arrange (S W: Finset I)(L A C:Op I)(c r:ℝ):Prop where
 gap:Pass (cutM S) (cutM W) L A c
 skit: PairBoard (cutM S) (cutM W) L C
 cover: Disjoint S W
 bore : Bore (cutM S+ramp L (cutM S) A) C r
-- all are proof, define Prop
namespace Arrange
variable (Xw : Arrange X Y L A C c r)
include Xw
lemma backB : Bore (ramp L (cutM X) A) C r:=⟨Xw.gap.ramp_star,Xw.bore.unit,Xw.bore.sk, Dual.toll_exit Xw.skit Xw.gap ▸ Xw.bore.low, Xw.bore.hi⟩
lemma realP (h: Top A u): inner ℂ (braC X Y C) u≠0:=by
 rw [bra_ref h Xw.gap Xw.cover]; let t:=h.spread (Xw.gap.enjoy 0 (by simp)); apply (show Bore (smoothP _ _ _ _ (0:ℝ)) C r from (by rw [Xw.gap.mark_exit]; exact Xw.bore)).cleanA t -- tune
omit Xw in
lemma regular (h: Bore A C r): Arrange ∅ ∅ 1 A C 1 r:=by
 let P:=cutM (∅:Finset I); have ht:P=0:=by unfold P cutM; simp
 constructor
 · have f : Empties (0:Op I) 0 1:= ⟨by exact IsStarProjection.zero _, by exact IsStarProjection.zero _, by simp, zero_mul _⟩; change Pass P P 1 A 1; rw [ht]; exact ⟨f,h.p,one_pos,le_rfl,by simp,by simp⟩
 · change PairBoard P P 1 C; rw [ht]; exact ⟨⟨by exact IsStarProjection.zero _, by exact IsStarProjection.zero _, by simp,zero_mul _⟩,cc_zero,cc_zero,by simp,by simp⟩
 · simp
 change Bore (P+ramp 1 P A) C r; rw [ht,zero_add, show ramp 1 0 A=A from ?_]; exact h
 unfold ramp; have he: rent0 (0:Op I) A=A:=by simp [rent0,rent1,Trans.beam]
 rw [he,one_mul]; exact (Trans.Ready.atSelf h.p).2
end Arrange

/-- Wick functional (complex), always paired against an actual bra. -/
def wick (b k:Wave I) (A:FC I):= inner ℂ b (acts A k)/inner ℂ b k
namespace wick
variable {b k: Wave I}
lemma termSum {J:Type*}(S:Finset J)(f:J→FC I): wick b k (∑ i∈S,f i)=∑ i∈S,wick b k (f i):=by rw [wick,act_sum, inner_sum,Finset.sum_div]; rfl
lemma termScale(z:ℂ)(A:FC I): wick b k (z • A)=z*wick b k A:=by rw [wick,act_smul,inner_smul_right,wick,mul_div_assoc]
lemma one(h:inner ℂ b k≠0): wick b k 1=1:=by rw [wick,act_one,div_self h]
lemma add(A B:FC I): wick b k (A+B)=wick b k A+wick b k B:=by simp only [wick,act_add,inner_add_right,add_div]
lemma sub(A B:FC I): wick b k (A-B)=wick b k A-wick b k B:=by simp only [wick,act_sub,inner_sub_right,sub_div]
lemma rt0 {A:FC I}(h:acts A k=0)(B:FC I): wick b k (B*A)=0:=by rw [wick,act_mul,h,map_zero,inner_zero_right,zero_div]
lemma lt0 {A:FC I}(h: acts (star A) b=0)(B:FC I): wick b k (A*B)=0:=by rw [wick,act_mul,←act_inner,h,inner_zero_left,zero_div]
end wick
abbrev letters (A B:Op I) (x: Ket I):= letterV (acts A x) (acts B x)
abbrev introW (A B: Op I)(i:I):= letters A B (basisKet i)
def contextM (P Q L A C U V E T: Op I):= (fitW P Q L A C U V)ᵀ*E + (fitP P Q L A C U V)ᵀ*T
lemma soundM (A B:Op I)(i j:I):inner ℂ (echo (acts A (basisKet i))) (acts B (basisKet j))=(Aᵀ* B) i j:=by simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct, Matrix.mul_apply, mul_comm]
def fee {J:Type*}(C:J→ℂ)(f:List J→ℂ)(t:List J):List J→ℂ
 | []=>0
 | a::l=> C a*f (t++l)-fee C f (t++[a]) l -- prefix included
-- expanded Pf equality, recursive characterization for this use
abbrev dues {J:Type*}(C:J→ℂ)(f:List J→ℂ)(t l:List J):= fee C f t l -- private? exposing ok?

section
variable (R:Arrange X Y L A C c r)(h: Top A u) (S W:Op I)
local notation "U" => braC X Y C
local notation "P" => cutM X
local notation "Q" => cutM Y
local notation "T'" => fitP P Q L A C S W
local notation "D'" => fitW P Q L A C S W
include R h
lemma annih (i:I): let a:=introW T' D' i; let b:=introW S W i; acts a u=0∧acts (star (b-a)) U=0:=by
 let G:= R.gap; let V:= solution G R.skit R.backB S W; intro a b
 let v:= basisKet (n:=I) i; refine ⟨Top.strike h ?_ ?_,?_⟩; rw [← act_mul,V.paid]; rw [← act_mul,V.joins,act_zero]
 let X':= S-T'; let Y':= W-D'
 have he: b-a=letters X' Y' v:=by unfold a b introW letters X' Y'; rw [act_sub,act_sub,l_sub]
 rw [he]; refine annihilation (acts X' v) (acts Y' v) R.skit R.bore.sk ?_ ?_ ?_
 · unfold X'; rw [←act_mul,mul_sub,V.gapP,sub_self,act_zero]
 · unfold Y'; rw [←act_mul,mul_sub,V.gapQ,sub_self,act_zero]
 rw [←act_mul,←act_mul,←act_mul, mul_assoc]; exact congrArg (fun x:Op I=> acts x v) (sub_eq_zero.mp V.rest) -- tune
omit R h in
lemma CAR_fitC (i:I) (E F:Op I)(j:I): let a:= introW T' D' i; let g:= contextM P Q L A C S W; let x:=introW E F j; antiB a x=g E F i j • 1:=by intro a g x; unfold antiB a x introW letters; rw [l_CAR]; unfold g contextM τpair; apply congrArg (fun z:ℂ=> z • (1:FC I)); rw [soundM,soundM,Matrix.add_apply]; simp [Matrix.mul_apply,mul_comm]
lemma frameC (i:I) (E F:Op I)(j:I): wick U u (introW S W i*introW E F j)= contextM P Q L A C S W E F i j:=by
 let b:= introW S W i; let a:= introW T' D' i; let g:= contextM P Q L A C S W; let x:=introW E F j; obtain ⟨y,z⟩:= annih R h S W i
 have hg := CAR_fitC (X:=X) (Y:=Y) (L:=L) (A:=A) (C:=C) S W i E F j
 change wick U u (b*x)=g E F i j; have hl:= wick.lt0 (k:=u) (A:=b-a) z x; have hr:= wick.rt0 (b:=U) (A:=a) y x; rw [sub_mul,wick.sub, sub_eq_zero] at hl; change a*x+x*a=g E F i j • 1 at hg; rw [show wick U u (b*x)=_ from hl, ←add_zero (wick U u (a*x)), ←(hr : wick U u (x*a)=0), ←wick.add, show a*x+x*a= _ from hg, wick.termScale,wick.one (R.realP h),mul_one]

end
end YM.CF.BPress.Pf
