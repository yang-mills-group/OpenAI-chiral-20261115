import YM.CF.BProof.Wick.Godet
import YM.CF.BProof.Wick.Loom
/-! Bill for actual contraction. Derivative path in two pieces 0,1;1,2; same integral.
Keep detailed split for real part: plogre, and use imaginary pieces of swept path. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev walking := Set.Icc (0:ℝ) 1
@[simp] lemma walk0 : (0:ℝ)∈walking:=Set.left_mem_Icc.mpr zero_le_one
@[simp] lemma walk1 : (1:ℝ)∈walking:=Set.right_mem_Icc.mpr zero_le_one
lemma upt {u:ℝ}(p:u∈walking): ‖u‖≤1:=by rw [Real.norm_of_nonneg p.1]; exact p.2
abbrev zen(z:ℂ):ℂ:= Complex.I * z.im
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]
abbrev Line (I:Type):= ℝ → Op I
def rug (A T : Op I)(u:ℝ):= land A (slit A T u)
abbrev crownP (A T:Op I):=rug A T 1
lemma rug_null {A T:Op I}(h:Gust A T): rug A T 0=A:=by rw [rug,h.rise,zero_smul,add_zero,land,send,entered,h.1.isSelfAdjoint,h.1.isIdempotentElem,add_sub_cancel,inv_one,one_mul,h.1.isIdempotentElem]
structure Ride (A T:Op I)(V Z V' Z':Line I)(P Q: Op I)(c r:ℝ):Prop where
 breeze : Gust A T
 bridge : Board (crownP A T) P Q c
 rails : ∀ u∈ walking, Shelf (rug A T u) (V 0) r
 fires : ∀ u∈ walking, Shelf (crownP A T) (V u) r
 sails : ∀ u∈ walking, Shelf (floorH (crownP A T) P Q u) (V 1) r
 pores : ∀ u∈ walking, Shelf (floorH (crownP A T) P Q 0) (Z u) r
 grips : V 1=Z 0
 frame : Double.Deck (crownP A T) P Q (Z 1) c r
 small : ‖T‖≤1/2
structure Story (V Z V' Z':Line I): Prop where
 wind : ∀ u∈ walking, HasDerivAt V (V' u) u
 top : ∀ u∈ walking, HasDerivAt Z (Z' u) u
structure SumK (A T:Op I)(V Z V' Z': Line I)(P Q:Op I):Prop where
 c1: ContinuousOn (fun u=>(salary (rug A T u) T (V 0)).trace) walking
 c2: ContinuousOn (fun u=>(bonus (crownP A T) (V' u) (V u)).trace) walking
 c3: ContinuousOn (fun u=>(salary (floorH (crownP A T) P Q u) (shutter (crownP A T) P Q u) (V 1)).trace) walking
 c4: ContinuousOn (fun u=>(bonus (floorH (crownP A T) P Q 0) (Z' u) (Z u)).trace) walking
def rolled (A T:Op I)(V Z V' Z':Line I)(P Q:Op I) := linestretch A T (V 0)+ hose (crownP A T) V V' 0 1 - spentDown (crownP A T) (V 1) P Q + hose (floorH (crownP A T) P Q 0) Z Z' 0 1
-- real part even at generic P,Q
def Pose (T A P Q:Op I):ℝ:= feeB (1+star T*T)/2+(feeB (hutch A P) + feeB (hutch (1-wedgeQ A P) Q))/2
def lumpLog (A T:Op I)(V Z V' Z':Line I)(P Q:Op I):ℂ:= (↑(Pose T (crownP A T) P Q+ tickCost (entryP (crownP A T) P Q) (Z 1)):ℂ)+zen (rolled A T V Z V' Z' P Q)
variable {A T V Z V' Z' P Q c r}(h:Ride (I:=I) A T V Z V' Z' P Q c r){x:Wave I}
def Initial (A C:Op I)(x:Wave I)(f:ℂ):Prop:=Complex.exp ((↑(tickCost A C):ℂ)+zen f) • x=filled A C
include h
lemma start (u:Sea A x) {f:ℂ} (p: Initial A (V 0) x f): overlap (V 0) x=Complex.exp ((↑(tickCost A (V 0)):ℂ) - zen f):=by
 let ζ:=(tickCost A (V 0):ℂ); let Z:= V 0; let U:=zen f; have hA:= h.breeze.1; have he:Complex.exp (ζ+U)=inner ℂ x (pairWave Z):= smul_left_injective ℂ (Task.sea hA u).nonzero (Eq.trans p (u.scalar hA (pairWave Z))) -- namespace
 unfold overlap; rw [←inner_conj_symm,←he]; change (starRingEnd ℂ) (Complex.exp (ζ+U))=Complex.exp (_-_); rw [←Complex.exp_conj]; unfold ζ U zen; congr 1; simp [mul_comm,sub_eq_add_neg]
lemma closeWalk (g:Story V Z V' Z')(p: SumK A T V Z V' Z' P Q)(s:Task A x) : let B:= acts (quant (house (crownP A T) P Q 0)) (expire A T x); overlap (Z 1) B= Complex.exp (rolled A T V Z V' Z' P Q)*overlap (V 0) x :=by
 intro B; have he:= s.quantS (h.breeze.fit 1); have hz:Task (crownP A T) (expire A T x):=he; have hx:Task (floorH (crownP A T) P Q 0) B:= hz.quantS h.bridge.fit0; rw [pairCoast zero_le_one Z Z' hx h.pores g.top p.c4,← h.grips]; unfold B; rw [chordEnd h.bridge hz h.sails p.c3,pairCoast zero_le_one V V' hz h.fires g.wind p.c2,liveline h.breeze s h.rails p.c1,rolled,Complex.exp_add,sub_eq_add_neg, Complex.exp_add, Complex.exp_add]; ring
omit h in
lemma folio (p:‖T‖≤1/2)(g:Gust A T)(s:Sea A x) : Real.log ‖expire A T x‖=feeB (1+star T*T)/2:=by
 unfold expire; rw [logWay (Task.sea g.1 s) (g.fit 1),g.voice,one_pow,one_smul,s.2, Real.log_one,zero_add,earning]; rw [add_sub_cancel_left,CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg T]
lemma writeLog (z:Story V Z V' Z')(p: SumK A T V Z V' Z' P Q)(s:Sea A x){f:ℂ}(e:Initial A (V 0) x f): let B:=acts (quant (house (crownP A T) P Q 0)) (expire A T x); overlap (Z 1) B=Complex.exp (lumpLog A T V Z V' Z' P Q-zen f):=by
 intro B; let X:= crownP A T; have ht:= Task.sea h.breeze.1 s; have hp':Task X (expire A T x):=ht.quantS (h.breeze.fit 1); have he: Align.Twig (Z 1) P:=by rw [Align.Twig,h.frame.markA,h.frame.colorA.eq]
 have hX := lines h.bridge hp' he (h.pores 1 walk1); let T':=rolled A T V Z V' Z' P Q; let g:= (tickCost A (V 0):ℂ); have hp: overlap (Z 1) B=Complex.exp (T'+(g-zen f)):=by rw [closeWalk h z p ht,start h s e, Complex.exp_add] -- let mismatch
 rw [folio h.small h.breeze s, hp, Complex.norm_exp,Real.log_exp] at hX
 rw [hp]; apply congrArg;
 unfold lumpLog Pose; apply Complex.ext
 · unfold T' g at *; simp [zen] at hX ⊢; exact hX -- tune
 simp [zen,g,T',sub_eq_add_neg]
end YM.CF.BProof.Wick
