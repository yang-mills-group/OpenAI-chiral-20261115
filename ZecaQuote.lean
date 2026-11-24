import ZecaMoment
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin
variable {α:Type}(Ω:H)
  (D:α→Moment H)(sp:α→Cross a)(t:α→ℝ)(h r:α→ℝ≥0)

abbrev lodgedOp (i:α):=
  optx S (D i).op (sp i).val

abbrev leap0 (i j:α):=
  parabola S ((D i).n+(D j).n) (↑(t j-t i))

def quoteL (L:List α):ℂ:=inner ℂ Ω (Film (lodgedOp S D sp) (leap0 S D t) L Ω)

abbrev padOp (i:α):=
 optx S ((D i).cost S (h i) (r i)) (sp i).val

abbrev padGap (i j:α):=
 S.E (t j - h j - (t i + r i)).toNNReal

def quotePaid (L:List α):ℂ:=
 inner ℂ Ω (Film (padOp S D sp h r) (padGap S t h r) L Ω)

abbrev padBefore (i j:α):=
 t i + r i ≤ t j - h j
local notation "A" n:max l:max => parabola S n (duration l)

lemma cache_heat (u:ℝ≥0)(n:ℕ):
 Commute (R^n) (S.E u):= (cupE S u).pow_left n

/-- Spend a bridge of length s g v. -/
lemma linkP (m n:ℕ){s v:ℝ≥0}(g:ℝ≥0)(e:0<s)(b:0<v) :
  A m s * S.E g * A n v = A (m+n) (s+g+v):=by
 suffices R^(m+n)*(A m s * S.E g * A n v)=R^(m+n)*A (m+n) (s+g+v) by
   ext1 x; exact cache_I S (m+n) (DFunLike.congr_fun this x)
 rw [show R^(m+n)*A (m+n) (s+g+v)=_ from K_E S (m+n) (s+g+v) (by positivity)]
 calc
   _ = R^n * (R^m * A m s) * S.E g * A n v:=by
         rw [add_comm,pow_add]; simp only [mul_assoc]
   _ = S.E (s+g)*(R^n * A n v):=by
      rw [show R^m * A m s=_ from K_E S m s e,mul_assoc (R^n),
          show S.E s * S.E g=_ from (S.time s g).symm,(cache_heat ..).eq,mul_assoc]
   _ = _:= by rw [show R^n * A n v=_ from K_E S n v b]
              exact (S.time ..).symm
lemma para_vacuum {t:ℝ≥0}(p:0<t)(n:ℕ)(q:R Ω=Ω):
 (A n t) Ω=Ω:=by
 apply cache_I S n
 rw [keepO S Ω q n]
 exact (DFunLike.congr_fun (K_E S n t p) Ω).trans (earthO S Ω t q)
lemma gap0 {i j:α}(p:0<r i)(q:0<h j)
  (e:padBefore t h r i j):
 A ((D i).n) (r i) * padGap S t h r i j * A ((D j).n) (h j)=leap0 S D t i j:=by
 rw [linkP S _ _ _ p q]
 unfold leap0 duration
 congr 2
 simp [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr e)]
 ring

lemma pad_expand (i:α) (e:0<h i)(u:0<r i):
 padOp S D sp h r i=
  A ((D i).n) (h i) * lodgedOp S D sp i * A ((D i).n) (r i):=by
 unfold padOp Moment.cost
 rw [versQ,versP]
 · exact (mslot S _ _ (dur.mpr e) _).symm
 · exact (mslot S _ _ (dur.mpr u) _).symm

lemma quoteL_paid (o:R Ω=Ω) (L:List α)
    (lh:∀ i∈L,0<h i) (rh:∀ i∈L,0<r i)
    (g:L.Pairwise (padBefore t h r)):
 quoteL S Ω D sp t L = quotePaid S Ω D sp t h r L:=by
 let c := padOp S D sp h r
 let T:= Film c (padGap S t h r)
 let z:= lodgedOp S D sp
 let l:= leap0 S D t
 let U:= Film z l
 cases L with
 | nil=>rfl
 | cons i L=>
   have e : T (i::L) Ω=(A ((D i).n) (h i)) (U (i::L) Ω):=by
     induction L generalizing i with
     | nil=>
         unfold T U c; rw [solitary,solitary,
          pad_expand S D sp h r i (lh i (by simp)) (rh i (by simp))]
         exact congrArg (fun x=> (A ((D i).n) (h i)) (z i x))
             (para_vacuum S Ω (rh i (by simp)) _ o)
     | cons j L ih=>
         obtain ⟨f,k⟩:=List.pairwise_cons.mp g
         have v:=ih j (fun a e=>lh a (List.mem_cons_of_mem i e)) (fun a e=>rh a (List.mem_cons_of_mem i e)) k
         change padOp S D sp h r i (padGap S t h r i j (T (j::L) Ω))= _
         rw [pad_expand S D sp h r i (lh i (by simp)) (rh i (by simp)),v]
         have w:=DFunLike.congr_fun
          (gap0 S D t h r (rh i (by simp)) (lh j (by simp)) (f j List.mem_cons_self))
           (U (j::L) Ω)
         exact congrArg (fun x=> (A ((D i).n) (h i)) (z i x)) w
   change inner ℂ Ω (U (i::L) Ω)=inner ℂ Ω (T (i::L) Ω)
   rw [e,←ContinuousLinearMap.adjoint_inner_left (A ((D i).n) (h i)),para_adj S _ _ (lh i (by simp)),para_vacuum S Ω (lh i (by simp)) _ o]
#print axioms quoteL_paid
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
