import YM.SU5.FiniteGaugeData.Maypole.Bermuda
import YM.SU5.FiniteGaugeData.Poin.Envoi
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Folio
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)
-- chronology.Braces
section plain
variable {α R:Type}[Monoid R](A:α→ R)(B:α→α→R)
lemma mappingF {β:Type}{p:β→α}{X:β→R}{Y:β→β→R}(f:∀ i,X i=A (p i))(q:∀ i j,Y i j=B (p i) (p j))(L:List β): Film X Y L= Film A B (L.map p):=by
 rw [Film_map]; exact congrArg₂ (fun X Y=>Film X Y L) (funext f) (funext fun i=>funext (q i))
lemma twoF (i j:α)(L:List α): Film A B (i::j::L)= A i * B i j * Film A B (j::L):= (mul_assoc ..).symm
lemma joiningF (L Q:List α)(u v:α): Film A B ((L++[u]) ++ (v::Q))=Film A B (L++[u])*B u v*Film A B (v::Q):= by
 induction L with
 | nil=> rw [List.nil_append,List.singleton_append,twoF,solitary]
 | cons x L ih=> cases L with
    | nil=> change Film A B (x::u::v::Q)= Film A B [x,u]* _ *_; rw [twoF,twoF A B x u [], mul_assoc (A x * _),mul_assoc (A x * _)]; exact congrArg (fun y=> A x * B x u * y) ih
    | cons j L=> rw [List.cons_append,List.cons_append,List.cons_append]; change Film A B (x :: j :: _) = Film A B (x :: j::_)*_*_; rw [twoF,twoF, mul_assoc (A x * _),mul_assoc (A x * _)]; exact congrArg (fun y=> A x * B x j * y) ih
end plain
-- chronometry
variable {α:Type}(A:α→H.Op)(ν:α→ℕ)
abbrev Item (α:Type):=α×E4
local notation "Ι"=> Item α
abbrev timesA(a:Axis)(u:Ι):ℝ:=u.2 a
abbrev leanX (s:ℝ)(n:ℕ):H.Op:= Par S n s.toNNReal
abbrev stamps(V:Ι): H.Op:= coreSp S V.2 (A V.1)
def gapK(V Z:Ι):H.Op:= leanX S (Z.2 a-V.2 a) (ν V.1+ν Z.1)
abbrev legis(V: List Ι): H.Op:= Film (stamps S A) (gapK S ν) V
def billBefore (s:ℝ)(n:ℕ)(v:List (Item α)):H.Op:= match v with | []=>1| x::_=> leanX S (timesA a x-s) (n+ν x.1)
def billLast (s:ℝ)(n:ℕ)(v:List (Item α)):H.Op:= match v.reverse with | []=>1| x::_=> leanX S (s-timesA a x) (ν x.1+n)
lemma budgetFoot(x:Ι)(v:List Ι)(s:ℝ)(n:ℕ): billBefore S ν s n (x::v)=leanX S (timesA a x-s) (n+ν x.1):=rfl
lemma budgetBack(v:List Ι)(s:ℝ)(i:Ι)(n:ℕ): billLast S ν s n (v++[i])=leanX S (s-timesA a i) (ν i.1+n):=by rw [billLast,List.reverse_append,List.reverse_singleton]; rfl
abbrev Front (s:ℝ)(v:List (Item α)):= billBefore S ν s 0 v*legis S A ν v
abbrev Back (s:ℝ)(v:List (Item α)):= legis S A ν v*billLast S ν s 0 v
abbrev face(s:ℝ)(v:List (Item α)):H:=Front S A ν s v Ω
abbrev role(s:ℝ)(v:List (Item α)):H:=star (Back S A ν s v) Ω -- need parentheses lean
abbrev wordValue(v:List (Item α)):= inner ℂ Ω (legis S A ν v Ω)
abbrev ahead(a:Axis)(v:List (Item α)):= Sau (timesA a) v
abbrev LaneE(a:Axis)(p:ℝ)(v:List (Item α)):= ahead a v ∧ ∀ i∈v, p<timesA a i
abbrev BackE(a:Axis)(p:ℝ)(v:List (Item α)):= ahead a v ∧ ∀ i∈v, timesA a i<p
lemma LastX(v:List Ι)(i:Ι) : BackE a (i.2 a) v→ ahead a (v++[i]):=fun p=> List.pairwise_append.mpr ⟨p.1,List.pairwise_singleton ..,fun v H _ h=> (List.mem_singleton.mp h) ▸ p.2 v H⟩ -- order direction
section
variable (U:Cross a){v t u:ℝ}{n k:ℕ}
-- sliding translations & rotation angle matrix later
lemma heat_a (v:ℝ≥0): star (S.E v)=S.E v:= S.sym v
lemma warm_a (x:ℝ)(q:0<x): star (leanX S x n)= leanX S x n:= parRev S x.toNNReal n (Real.toNNReal_pos.mpr q)
lemma heat_κ (x:ℝ)(q:0<x): Cache S n * leanX S x n=S.E x.toNNReal:= P_Heq S x.toNNReal n (Real.toNNReal_pos.mpr q)
lemma comm_u (x:ℝ)(q:0<x) : Commute (leanX S x n) (S.U U):=by rw [←laneslot]; exact mslot S U.val (OS.Semigroup.duration x.toNNReal) (dur.mpr (Real.toNNReal_pos.mpr q)) _
lemma compV (x y:ℝ≥0): S.E x*S.E y=S.E (x+y):= (S.time ..).symm
lemma commute' (x:ℝ≥0):Commute (Cache S n) (S.E x):=(cupE S x).pow_left n
lemma comm_e (x:ℝ)(h:0<x)(u:ℝ≥0): Commute (leanX S x n) (S.E u) :=by
 ext1 y; apply cache_I S n; apply DFunLike.congr_fun (show Cache S n * (leanX S x n * S.E u)= Cache S n * (S.E u * leanX S x n) from ?_) y
 rw [←mul_assoc,heat_κ S x h,←mul_assoc,(commute' S u).eq,mul_assoc,heat_κ S x h,compV,compV,add_comm]
lemma invest (h:0<u)(q:0≤v)(p:0<t): leanX S u n*S.E v.toNNReal * leanX S t k= leanX S (u+v+t) (n+k) :=by
 ext1 y; apply cache_I S (n+k); apply DFunLike.congr_fun (show Cache S (n+k)*(leanX S u n*S.E v.toNNReal * leanX S t k)= Cache S (n+k)*leanX S (u+v+t) (n+k) from ?_) y
 rw [heat_κ S (u+v+t) (by linarith), cacheA]
 have hh:Cache S n * Cache S k= Cache S k * Cache S n:= ((Commute.refl (saucer S)).pow_pow n k); -- tune
 let V:=u.toNNReal; let H:=v.toNNReal; let T:= t.toNNReal; rw [hh]; simp only [← mul_assoc]; rw [mul_assoc (Cache S k) (Cache S n),heat_κ S u h,(commute' S V).eq, mul_assoc (S.E V), (commute' S H).eq,←mul_assoc,mul_assoc (S.E _ *S.E _),heat_κ S t p,compV,compV]; congr 1; unfold V H; rw [Real.toNNReal_add (by linarith : 0≤ u+v) p.le,Real.toNNReal_add h.le q] 
include hp
lemma shed(u:ℝ≥0): S.E u Ω=Ω:= earthO S Ω u (rlock S Ω hp)
lemma earnO (u:ℝ)(p:0<u): leanX S u n Ω=Ω:=by apply cache_I S n; exact (DFunLike.congr_fun (heat_κ S (n:=n) u p) Ω).trans ((shed S Ω hp u.toNNReal).trans (keepO S Ω (rlock S Ω hp) n).symm)
lemma offer : S.U U Ω=Ω:= (laneslot S U) ▸ hp U.val
end
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
