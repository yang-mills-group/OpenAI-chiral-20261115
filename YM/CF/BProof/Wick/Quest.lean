import YM.CF.BProof.Double.Touchdown
import YM.CF.BProof.Wick.Loom
import YM.CF.Sedge.Plume

/-! Pfaffian values on any letter family, by recursion. Includes possibilities
where order matters. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter Fock Finset Branch Align Double
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- use recursion as API. signs match conventional whole string ordering.
variable {L:Type*}
structure Scores (d:L→L→ℂ)(f:List L→ℂ) : Prop where
 clear : f []=1
 consist (x:L)(v:List L): f (x::v)=((picks v).map (fun i=> (cval i.neg*d x i.front)* f i.back)).sum
lemma Scores.two {d:L→L→ℂ}{f:List L→ℂ}(p:Scores d f)(x y):f [x,y]=d x y:=by rw [p.consist]; simp [picks,p.clear,cval]

variable {I:Type*}[Fintype I][LinearOrder I][Nonempty I]
def sample (x y:Wave I): FC I→ₗ[ℂ] ℂ where
 toFun F:= inner ℂ y (acts F x)
 map_add' F G:= by rw [act_add,inner_add_right]
 map_smul' c F:= by rw [act_smul,inner_smul_right]; rfl
def normal (x y:Wave I): FC I→ₗ[ℂ] ℂ:= (inner ℂ y x)⁻¹ • sample x y
lemma read_normal (x y: Wave I)(F:FC I): normal x y F=(inner ℂ y x)⁻¹ * inner ℂ y (acts F x):=rfl
lemma sample_paid {x y:Wave I}(e:inner ℂ y x≠0)(F:FC I):inner ℂ y (acts F x)= normal x y F*inner ℂ y x:=by rw [read_normal,mul_comm _ (inner ℂ y x),←mul_assoc,mul_inv_cancel₀ e,one_mul]
def issue (A P Q C:Op I)(x y: Book I):= tau (acts (oblique A P Q C) x) y
abbrev claim (φ: L→ Book I)(x y:Wave I)(l:List L):= normal x y ((l.map (fun i=> printT (φ i))).prod)
variable {p q:Finset I}{A C:Op I}{c r:ℝ}{x:Wave I}(t:Task A x)(d:Disjoint p q)(D:Double.Deck A (cutM p) (cutM q) C c r)
theorem take_press : inner ℂ (pressB p q C) x = overlap C (acts (cabin p q) x) := by rw [pressB,overlap]; nth_rw 1 [←(cabin_proj p q).isSelfAdjoint.star_eq]; exact act_inner ..
include t d D
theorem press_value : inner ℂ (pressB p q C) x=overlap C (acts (quant (house A (cutM p) (cutM q) 0)) x):= by rw [take_press,migrate D.cbP d t]
theorem value_press : inner ℂ (pressB p q C) x ≠0:=by rw [press_value t d D]; exact D.safety.bills (t.quantS D.cbP.fit0)
theorem finalGauge (φ:L→Book I): Scores (fun i j=>issue A (cutM p) (cutM q) C (φ i) (φ j)) (claim φ x (pressB p q C)):=by
 let y:= pressB p q C; let f(i:L):= printT (φ i); let X(i:L):= issue A (cutM p) (cutM q) C (φ i); let s (i j:L):= X i (φ j); let o:=(inner ℂ y x)⁻¹; refine ⟨?_,?_⟩; · simp only [claim,List.map_nil,List.prod_nil, read_normal,act_one,inv_mul_cancel₀ (value_press t d D)]
 intro i v; let T:=oblique A (cutM p) (cutM q) C; let U(i:L):=printT (acts T (φ i)); let F:=printT (acts (1-T) (φ i)); let H(l: List L):= chime f x l
 have ht: f i =U i+F:=by unfold U f F; rw [←map_add,← act_add,add_sub_cancel,act_one]
 have hu:= plume f U x s (fun i=>rightErase (D.enters _) t) (fun i j=>ant ..) i v
 change o* inner ℂ y (H (i::v))=((picks v).map fun c=> (cval c.neg*s i c.front)*(o* inner ℂ y (H c.back))).sum
 rw [show H (i::v)=_ from charm f x v i, ht,act_add, inner_add_right, ←act_inner F, touchdown _ D d (D.living ..),inner_zero_left,add_zero,hu]; generalize picks v=M; induction M with
 | nil=>simp
 | cons j l IH=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,inner_add_right,mul_add,IH]; congr 1; rw [seatsC,inner_smul_right]; ring -- tune
-- full
omit d D in
theorem ordinaryGauge (s:Shelf A C r)(φ:L→Book I): Scores (fun i j=>issue A 0 0 C (φ i) (φ j)) (claim φ x (pairWave C)):=by
 have hf:cutM (∅:Finset I)=0:=by simp [cutM]
 have he:Double.Deck A (cutM (∅:Finset I)) (cutM (∅:Finset I)) C 1 r:=hf ▸ nothing_deck s
 simpa only [hf,pressB,cabin_nil,act_one] using finalGauge t (Finset.disjoint_empty_left (∅:Finset I)) he φ
end YM.CF.BProof.Wick
