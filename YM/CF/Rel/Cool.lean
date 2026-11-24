import YM.CF.Rel.Pawn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev noteG(G:Gauge)(m:ℕ):= CurRun (m+1)→Space m→ℂ
def trimU (F:noteG G m)(s:SpotG G (m+1))(x:InputZ G n):=∑ d:DialT n m,∑ p:CurRun (m+1), Ca (F p) d*oct p x s d 0
abbrev OutM (m:ℕ):=Fin (m+1)→ Shed (Keys m) (m+1)
lemma trim_s {F U:noteG G m}(x:InputZ G n)(s:SpotG G (m+1)): trimU (F-U) s x=trimU F s x-trimU U s x:=by unfold trimU; simp only [Pi.sub_apply]; simp_rw [show ∀ i:CurRun (m+1), F i-U i=fun y=> F i y-U i y from fun i=>rfl,ca_sub,sub_mul,sum_sub_distrib]
def palm (k:Site n)(i:Fin (m+1))(a:Axis):Site n:=if i=0 then Lattice.step a else 0
def pailH (X:OutM m)(k:Site n)(i:Fin (m+1))(x:InputZ G n)(s:SpotG G (m+1))(d:DialT n m)(p:CurRun (m+1))(b:TypeFace 3)(a:Axis):=left ℂ 2 a b (p i)*sting k i a * B (X i) p d b * oct p x s (d+reedU i a) 0
-- χ⊕ δ ν
lemma sumPerm {E:Type}[AddCommMonoid E]{α:Type}[Fintype α]{β:Type}[Fintype β]{ι:Type}[Fintype ι] (F:α→β→ι→E): (∑ p,∑ b,∑ c,F p b c)=∑ b,∑ c,∑ p,F p b c:=by rw [sum_comm]; exact sum_congr rfl fun i _=>sum_comm
lemma opening(v:Axis→ℝ)(k:Site n)(h:Push.Loops.Matches (axes v) k)(i:Fin (m+1))(X:OutM m)(p:CurRun (m+1))(b:TypeFace 3)(a:Axis)(s:SpotG G (m+1))(x:InputZ G n):
 (∑ d:DialT n m,(left ℂ 2 a b (p i) * (sting k i a*B (X i) p (d-reedU i a) b-B (X i) p d b))*oct p x s d 0) =∑ d:DialT n m,(pailH X k i x s d p b a-left ℂ 2 a b (p i)*B (X i) p d b*oct p x s d 0):=by
 simp_rw [mul_sub,sub_mul,sum_sub_distrib]; congr 1; rw [←Equiv.sum_comp (Equiv.addRight (reedU (n:=n) i a))]; refine sum_congr rfl fun j _=>?_ ; simp only [show Equiv.addRight (reedU i a) j=j + reedU i a from rfl,add_sub_cancel_right,pailH, mul_assoc]; -- tune
lemma pail_p(k:Site n)(i:Fin (m+1))(a:Axis)(p:CurRun (m+1))(x:InputZ G n)(s:SpotG G (m+1))(d:DialT n m)(b:TypeFace 3)(U:OutM m): pulseP k (palm k i a)*pailH U k i (te x (palm k i a)) s d p b a=left ℂ 2 a b (p i)*B (U i) p d b * ends p x s d i a :=by
 have hp:pulseP k (palm k i a)*sting k i a=1:=by unfold palm sting; split <;> simp [*]
 unfold pailH; rw [oath,show left ℂ 2 a b (p i)*sting k i a=sting k i a*left ℂ 2 a b (p i) from mul_comm ..]; rw [←mul_assoc,←mul_assoc,←mul_assoc,hp,one_mul]; rfl
lemma veins(k:Site n)(v:Axis→ℝ)(X:OutM m)(i:Fin (m+1))(h:Push.Loops.Matches (axes v) k)(g:Paddle i (X i))(s:SpotG G (m+1))(x:InputZ G n):
 trimU (fun p y=>nullL (cardR v y) i (X i y) p) s x= ∑ d:DialT n m,∑ b:TypeFace 3,∑ p:CurRun (m+1),∑ a:Axis,(pailH X k i x s d p b a-pulseP k (palm k i a)*pailH X k i (te x (palm k i a)) s d p b a):=by
 let E(p:CurRun (m+1))(d:DialT n m)(b:TypeFace 3)(a:Axis):= pailH X k i x s d p b a-left ℂ 2 a b (p i)*B (X i) p d b*oct p x s d 0
 calc
    _ = ∑ p:CurRun (m+1),∑ b:TypeFace 3,∑ a:Axis,∑ d:DialT n m,E p d b a:=by
       unfold trimU; rw [sum_comm]; apply sum_congr rfl; intro p _; simp_rw [accuse k v h,sum_mul]
       rw [sum_comm]; apply sum_congr rfl; intro b _; rw [sum_comm]; exact sum_congr rfl fun a _=> opening v k h i X p b a s x
    _ = ∑ d:DialT n m,∑ b:TypeFace 3,∑ p:CurRun (m+1),∑ a:Axis,E p d b a:=by
       rw [sum_comm]; conv_rhs=> rw [sum_comm]; -- tune
       exact sum_congr rfl fun b _=> (sumPerm _).symm
    _= _:=by
       apply sum_congr rfl; intro d _; apply sum_congr rfl; intro b _; have he:=shine (X i) i x s d b g; simp_rw [E,pail_p k i, Finset.sum_sub_distrib]; simp_rw [mul_sub, Finset.sum_sub_distrib] at he; -- tune occurrence p substitution and pail_p explicit arguments
       rw [sub_eq_zero] at he; rw [he]
lemma fairy (k:Site n)(v:Axis→ℝ)(X:OutM m)(h:Push.Loops.Matches (axes v) k)(Y:noteG G m)(hp:∀ i,Paddle i (X i))(hm:∀ (p:Corn (Keys m)) (q:CurRun (m+1)), Y q (axes p)=∑ i,nullL (cardR v (axes p)) i (X i (axes p)) q)(s:SpotG G (m+1))(x:InputZ G n): trimU Y s x = ∑ i,∑ d: DialT n m,∑ b:TypeFace 3,∑ p:CurRun (m+1),∑ a:Axis,(pailH X k i x s d p b a-pulseP k (palm k i a)*pailH X k i (te x (palm k i a)) s d p b a):=by
 simp_rw [← fun i=>veins k v X i h (hp i) s x]; unfold trimU; have hY(d:DialT n m)(p:CurRun (m+1)): Ca (Y p) d=∑ i,Ca (fun y=>nullL (cardR v y) i (X i y) p) d:=by rw [←ca_sum]; apply cac; intro i; rw [toll_unt]; exact hm _ _
 simp_rw [hY,sum_mul]; conv_rhs=> rw [sum_comm]
 exact sum_congr rfl fun i _=>sum_comm
end YM.CF.Rel
