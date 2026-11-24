import GaugeFieldConstruction.Momentcast
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
namespace Bank
variable (E F:Type*) [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
abbrev OneF:= E→L[ℝ]F
abbrev TwoF:= E→L[ℝ](E→L[ℝ]F)
def DualS: Submodule ℝ (TwoF E F) where
 carrier:={ x|∀ i j,x i j=x j i}
 zero_mem' :=fun _ _=>rfl
 add_mem':=by intro x y p h; exact fun i j=> congrArg₂ (fun (x y:F)=> x+y) (p i j) (h i j)
 smul_mem':=by intro z f h; exact fun i j=>congrArg (fun x:F=> z • x) (h i j)
abbrev Duo:= DualS E F
abbrev Ole:= F × OneF E F × Duo E F
variable {E F}
lemma dual_uni (x y:Duo E F)(t:∀ i:E,x.val i i=y.val i i):x=y:=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j
 have hx:=t (i+j); simp only [map_add, ContinuousLinearMap.add_apply] at hx; rw [x.property j i,y.property j i,t i,t j] at hx
 apply (smul_right_injective (M:=F) (by norm_num : (2:ℝ)≠0)) -- tune
 simp only; rw [two_smul,two_smul]; have he:=hx; simp only [←add_assoc,add_left_inj] at he; simp only [add_assoc,add_right_inj] at he; exact he
structure AptK (f:E→ F)(P:Ole E F):Prop where
 turn(x:E): TierS (fun s:ℝ=> f (s • x)) P.1 (P.2.1 x) (P.2.2.val x x)
variable {f g:E→ F}{P R:Ole E F}
lemma AptK.equal (w:AptK f P)(h:f=ᶠ[𝓝 0]g): AptK g P:= ⟨fun i=> (w.turn i).equal ((show Tendsto (fun x:ℝ=> x • i) (𝓝 0) (𝓝 0) from (by exact (show Continuous (fun x:ℝ=> x • i) from by fun_prop).tendsto' _ _ (zero_smul ..))).eventually h)⟩
lemma AptK.const (v:F): AptK (fun _:E=>v) (v,0,0):=⟨fun _=>TierS.const _⟩
lemma AptK.point (p:AptK f P): f 0=P.1:=by simpa only [Pi.smul_apply,zero_smul] using (p.turn 0).post
lemma AptK.joinK (u:AptK f P)(w:AptK g R): AptK (f+g) (P+R):=⟨fun i=> (u.turn i).add (w.turn i)⟩
lemma AptK.unique (w:AptK f P)(p:AptK f R): P=R:=by have h(x:E):=(w.turn x).unique (p.turn x) (EventuallyEq.refl ..); exact Prod.ext (h 0).1 (Prod.ext (ContinuousLinearMap.ext fun i=>(h i).2.1) (dual_uni _ _ fun i=>(h i).2.2))
lemma AptK.sumV {α: Type*}(T: Finset α)(f:α→ E→F)(P:α→Ole E F)(h:∀ i∈T,AptK (f i) (P i)):AptK (∑ i∈T,f i) (∑ i∈T,P i):=by
 classical
 induction T using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact AptK.const (0:F)
 | @insert i T p ih=> rw [sum_insert p,sum_insert p]; exact (h _ (mem_insert_self ..)).joinK (ih fun i v=>h i (mem_insert_of_mem v))
def preTwo {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](v:Duo E F)(f:X→L[ℝ]E):Duo X F:=⟨(((v.val.comp f).flip.comp f).flip),fun i j=> v.property _ _⟩
def pre {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](v:Ole E F)(f:X→L[ℝ]E): Ole X F:= (v.1,v.2.1.comp f,preTwo v.2.2 f)
def minusF(v:Ole E F):= -v
lemma AptK.preC {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](w:AptK f P)(g:X→L[ℝ] E): AptK (fun x=> f (g x)) (pre P g):=⟨fun i=>by simp_rw [map_smul g]; exact w.turn _⟩
variable {A:Type*}[NormedAddCommGroup A][NormedSpace ℝ A]
-- explicit compL
private abbrev mix (L:F→L[ℝ]A)(R:TwoF E F) : TwoF E A:= (ContinuousLinearMap.compL ℝ E F A L).comp R
def post2 (v:Duo E F)(L:F→L[ℝ]A):Duo E A:=⟨mix L v.val,fun i j=>congrArg L (v.property i j)⟩
def postF(v:Ole E F)(L:F→L[ℝ] A):Ole E A:= (L v.1,L.comp v.2.1,post2 v.2.2 L)
lemma AptK.geomF (t:AptK f P)(L:F→L[ℝ] A) : AptK (fun x=> L (f x)) (postF P L):=⟨fun i=> (t.turn i).map L⟩
lemma AptK.negS (p:AptK f P): AptK (-f) (-P):=by
 convert p.geomF (-ContinuousLinearMap.id ℝ F) using 2 <;> try rfl
lemma AptK.minus (u:AptK f P)(w:AptK g R): AptK (f-g) (P-R):=by rw [sub_eq_add_neg,show P-R=P+-R from sub_eq_add_neg P R]; exact u.joinK w.negS
variable {J:Type*}[NormedRing J][NormedAlgebra ℝ J]
def cartF(T U:Ole E J):Ole E J:= by
 let A:= T.1; let B:=U.1; let P:= T.2.1; let Q:=U.2.1; let L:= ContinuousLinearMap.mul ℝ J B; let R:= (ContinuousLinearMap.mul ℝ J).flip B; let F:= ContinuousLinearMap.mul ℝ J A;
 let V:= R.comp P + F.comp Q
 let X:= (((ContinuousLinearMap.mul ℝ J).comp P).flip.comp Q).flip
 let Y:=post2 T.2.2 R + post2 U.2.2 F
 exact (A*B, V, Y + ⟨X+X.flip,fun i j=>add_comm ..⟩)
lemma cart_0(T U:Ole E J): (cartF T U).1=T.1*U.1:=rfl
lemma cart_1(T U:Ole E J)(i:E):(cartF T U).2.1 i=T.2.1 i*U.1 + T.1*U.2.1 i:=rfl
lemma cart_2(T U:Ole E J)(i j:E):(cartF T U).2.2.val i j=T.2.2.val i j*U.1 + T.1*U.2.2.val i j+(T.2.1 i*U.2.1 j+T.2.1 j*U.2.1 i):=rfl
lemma AptK.cart {f g:E→ J}{u v:Ole E J}(t:AptK f u)(P:AptK g v): AptK (f*g) (cartF u v):= ⟨fun x=> (t.turn x).mul (P.turn x)⟩
end Bank
end Lenten
end YM.CF.TableF
end
