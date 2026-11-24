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

open Boundary

variable (Ω:Bench S) (D:Moment H)
local notation "O"=>Ω.val
variable (h:saucer S Ω.val=Ω.val) (e:∀p,M S p Ω.val=Ω.val)
include h
lemma coinVac (u v:ℝ≥0) (t:0<v):
  D.cost S u v O = parabola S D.n (duration u) (D.op O):=
 congArg_coin (para_vacuum S O t D.n h)
where
 congArg_coin : parabola S D.n (duration v) O=O→_:= fun e=>congrArg
  (fun x:H=>parabola S D.n (duration u) (D.op x)) e
lemma coinScalar (u v:ℝ≥0) (p:0<u) (t:0<v):
  inner ℂ O (D.cost S u v O)=inner ℂ O (D.op O):=by
 rw [coinVac S Ω D h u v t,←ContinuousLinearMap.adjoint_inner_left,para_adj S _ _ p,para_vacuum S O p D.n h]

include e
lemma coinRaw (p:E4): D.form S p Ω Ω=inner ℂ O (D.op O):=by
 unfold Moment.form lucent; rw [hallO S Ω h]
 change inner ℂ O (M S p (D.op (M S (-p) O)))=_
 rw [e]
 exact (congrArg (fun x=>inner ℂ x (M S p (D.op O))) (e p).symm).trans
     (tsees ..)
lemma coinTest (b:inner ℂ Ω.val (D.op Ω.val)=0)(f:Test4):
 inner ℂ Ω.val (D.field S f Ω).val=0:=by
 rw [(realStamp S).scalar]
 simp [coinRaw S Ω D h e,b]

/-- True onepoint of field and partners. -/
def WitZero :Prop:=
  inner ℂ Ω.val (D.op Ω.val)=0∧
  ∀ f:Test4,
    inner ℂ Ω.val (D.field S f Ω).val=0 ∧
    inner ℂ Ω.val (D.dagger.field S f Ω).val=0
lemma witZero {s t:ℝ≥0}(p:0<s)(q:0<t)
 (b:inner ℂ Ω.val (D.cost S s t Ω.val)=0):
 WitZero S Ω D:=by
 rw [coinScalar S Ω D h _ _ p q] at b
 refine ⟨b, fun f=> ⟨coinTest S Ω D h e b f,coinTest S Ω _ h e ?_ f⟩⟩
 show inner ℂ O (D.op.adjoint O)=0
 rw [ContinuousLinearMap.adjoint_inner_right,←inner_conj_symm,b,map_zero]
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
