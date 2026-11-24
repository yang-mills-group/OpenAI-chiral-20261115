import ZecaQuote
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin
variable {n:ℕ}(Ω:H)
  (D:Fin n→Moment H)(x:Points n)(k:ℕ)

/-- spacers on centers -/
abbrev cord (k:ℕ)(i:Fin n):ℝ := (dy k)*(i.val:ℝ)
lemma cordMono(k:ℕ):StrictMono ((cord k):(Fin n→ℝ)):=fun i j h=>
 mul_lt_mul_of_pos_left (Nat.cast_lt.mpr h) (show (0:ℝ)<dy k from dy_pos k)
lemma cordGo(i:Fin n):Tendsto (fun k=>cord k i) atTop (𝓝 0):=by simpa using dy_go.mul_const (i.val:ℝ)
def deskTimes (a:Axis)(k:ℕ)(x:Points n)(r:ℝ)(i:Fin n):ℝ:= cord k i - r*(x i a)
lemma deskMono : ∀ᶠ r:ℝ in 𝓝 0,StrictMono (deskTimes a k x r):=by
 show ∀ᶠ r:ℝ in 𝓝 0, ∀ i j:Fin n, _ → _
 rw [eventually_all]; intro i
 rw [eventually_all]; intro j
 by_cases h:i<j
 · have g:(deskTimes a k x 0) i < (deskTimes a k x 0) j:=by
     simpa [deskTimes] using cordMono k h
   unfold deskTimes
   exact (IsOpen.mem_nhds (isOpen_lt (f:=fun t=>cord k i - t*(x i a)) (g:=fun t=>cord k j - t*(x j a)) (by fun_prop) (by fun_prop)) g
    |>(show ∀ᶠ r:ℝ in 𝓝 0,deskTimes a k x r i < deskTimes a k x r j from ·)).mono (fun r e _=>e)

 · exact Eventually.of_forall (fun _ h'=> (h h').elim)

lemma FilmRel {α:Type} (P Q:α→α→H.Op)(A:α→H.Op)(s:α→α→Prop)
 (e:∀i j,s i j→P i j=Q i j)(L:List α)(u:L.Pairwise s):
 Film A P L=Film A Q L:=by
 induction L with
 | nil=>rfl
 | cons i L ih=>
     obtain ⟨p,v⟩:=List.pairwise_cons.mp u
     rw [Film_step,Film_step,ih v]
     cases L with
      | nil=>rfl
      | cons j L=>
        show A i * (P i j*_) = A i*(Q i j*_)
        rw [e i j (p j List.mem_cons_self)]
lemma ord(n:ℕ): (Each n).Pairwise (·<·):=by
 exact List.pairwise_lt_finRange _

abbrev litGap (a:Axis)(k:ℕ)(x:Points n)(z:ℂ)(i j:Fin n):ℂ:=
  (↑(cord k j-cord k i) :ℂ) -
      z*(↑(x j a-x i a):ℂ)
-- below chooses no guards (arbitrary gaps but relational AnalyticAt)
def arcOp (k:ℕ)(x:Points n)(z:ℂ)(i j:Fin n):H.Op :=
 parabola S ((D i).n+(D j).n) (litGap a k x z i j)
abbrev bodySp (a:Axis)(x:Points n):=fun i:Fin n=>SEP a (x i)
def arc (k:ℕ)(x:Points n)(z:ℂ):=
 inner ℂ Ω (Rail (lodgedOp S D (bodySp a x)) (arcOp S D k x z) Ω)

lemma arc_real (r:ℝ): arc S Ω D k x (r:ℂ)=
 quoteL S Ω D (bodySp a x) (deskTimes a k x r) (Each n):=by
 have e:arcOp S D k x r = leap0 S D (deskTimes a k x r):= by
    funext i j; unfold arcOp leap0
    congr 1; unfold litGap deskTimes; push_cast; ring
 unfold arc; rw [e]; rfl

lemma arcOp_ana (i j:Fin n)(h:i<j)(r:ℝ):
 AnalyticAt ℂ (fun z=> arcOp S D k x z i j) (imaginary r):=by
 let f(z:ℂ):=litGap a k x z i j
 have t:f (imaginary r)∈inside:=by
    simpa [f,litGap,imaginary,inside] using cordMono k h
 have af:AnalyticAt ℂ f (imaginary r):= analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
 exact (Bokeh S _ _ t).comp af

private lemma arc_ana' (r:ℝ) (L:List (Fin n))(u:L.Pairwise (·<·)):
 AnalyticAt ℂ (fun z=>Film (lodgedOp S D (bodySp a x)) (arcOp S D k x z) L)
   (imaginary r):= by
 induction L with
 | nil=> exact analyticAt_const
 | cons i L ih=>
   obtain ⟨e,p⟩:=List.pairwise_cons.mp u
   let f(z:ℂ):=clip (arcOp S D k x z) i L
   have cf:AnalyticAt ℂ f (imaginary r):=by
       cases L with
       | nil=> exact analyticAt_const
       | cons j L=> exact arcOp_ana S D x k i j (e j List.mem_cons_self) _
   exact AnalyticAt.mul analyticAt_const (cf.mul (ih p))
lemma arc_ana (r:ℝ):
 AnalyticAt ℂ (arc S Ω D k x) (imaginary r):=by
 let G:= (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ H.space Ω)
 exact (G.analyticAt _).comp (arc_ana' S D x k r (Each n) (ord n))

structure Marks (S:OS.Semigroup H a)(Ω:H) {n:ℕ}(D:Fin n→Moment H)(V:ℕ→Points n→ℂ→ℂ):Prop where
 reads (x:Points n)(k:ℕ):
    ∀ᶠ r:ℝ in 𝓝 0, StrictMono (deskTimes a k x r) ∧
    V k x r= quoteL S Ω D (bodySp a x) (deskTimes a k x r) (Each n)
 ink (x:Points n)(k:ℕ)(r:ℝ): AnalyticAt ℂ (V k x) (imaginary r)
lemma arc_marks: Marks S Ω D (arc S Ω D):=⟨
 fun y n=>Eventually.mono (deskMono (a:=a) y n) (fun r g=>⟨g,arc_real S Ω D y n r⟩),
 arc_ana S Ω D⟩
lemma ink_uniq {V}(g:Marks S Ω D V):
 V k x I = arc S Ω D k x I:=by
 apply starship (g.ink x k) (arc_ana S Ω D x k)
 filter_upwards [g.reads x k] with r h; rw [h.2,arc_real]
#print axioms arc_marks
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
