import GaugeFieldConstruction.StencilStressLaw
/-!
# Affording derivative field stress prices. Operator multilinearity.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
namespace StressLaw
variable {G:Gauge}{L:Register G}{S:Table L} (X:Wightman S)
namespace listCost
private lemma heq_tail_zero {E:Type*} (f:Fin (n+1)→E)(e:E): (fun i:Fin n=> Function.update f 0 e i.succ)=Fin.tail f:=by funext i; simp [Fin.tail]
private lemma heq_tail_succ {E:Type*} (f:Fin (n+1)→E)(e:E): (fun i:Fin n=> Function.update f k.succ e i.succ)=Function.update (Fin.tail f) k e:=by funext i; by_cases p:i=k <;> simp [Fin.tail,p]
variable {A:Type*}[Ring A][Algebra ℂ A]
lemma priceMul_plus (a:Fin n→A)(b c:A) : (List.ofFn (Function.update a k (b+c))).prod = (List.ofFn (Function.update a k b)).prod + (List.ofFn (Function.update a k c)).prod:= by
 induction n with
 | zero=> exact k.elim0
 | succ n ih=>
    induction k using Fin.cases with
    | zero=> simp only [List.ofFn_succ,update_self,List.prod_cons, heq_tail_zero]; rw [add_mul]
    | succ k=> simp only [List.ofFn_succ,List.prod_cons,heq_tail_succ,Function.update_of_ne (Fin.succ_ne_zero k).symm]; rw[ih k, mul_add]
lemma priceMul_scale (a:Fin n→A)(b:A)(χ:ℂ) : (List.ofFn (Function.update a k (χ • b))).prod = χ • (List.ofFn (Function.update a k b)).prod:= by
 induction n with
 | zero=> exact k.elim0
 | succ n ih=>
    induction k using Fin.cases with
    | zero=> simp only [List.ofFn_succ,update_self,List.prod_cons, heq_tail_zero]; rw [smul_mul_assoc]
    | succ k=> simp only [List.ofFn_succ,List.prod_cons,heq_tail_succ,Function.update_of_ne (Fin.succ_ne_zero k).symm]; rw[ih k, mul_smul_comm]
lemma permutes_mul(D:Equiv.Perm (Fin n))(a:Fin n→A)(b:A): Function.update a k b ∘ D = Function.update (a ∘ D) (D.symm k) b:= by
 funext i; by_cases h:i=D.symm k
 · subst i; simp
 simp_all [Equiv.eq_symm_apply] -- tune
end listCost
open listCost
local notation "OP"=>Module.End ℂ X.operators.domain
local notation "ℎ"=> X.operators.omega
local notation "Φ"=> X.operators.field
noncomputable def operatorPays (f:Fin n→Module.End ℂ X.operators.domain) :ℂ:= inner ℂ (ℎ) ((List.ofFn f).prod (ℎ))
noncomputable abbrev wage (v:Fin n→S.Union)(f:Fin n→Test4) (i:Fin n):OP:=Φ (v i) (f i)
noncomputable def changeBill (D:Equiv.Perm (Fin n))(a:Fin n→Module.End ℂ X.operators.domain): Module.End ℂ X.operators.domain →ₗ[ℂ] ℂ:={
 toFun z:= operatorPays X (Function.update a k z ∘ D)
 map_add' x y:= by unfold operatorPays; simp_rw [permutes_mul]; rw [priceMul_plus,LinearMap.add_apply,inner_add_right]
 map_smul' c v:= by unfold operatorPays; simp_rw [permutes_mul]; rw [priceMul_scale _ (a ∘ D) v c,LinearMap.smul_apply,inner_smul_right]; rfl }
lemma employed (f:Fin n→ Letter S) (a:Equiv.Perm (Fin n)) : inner ℂ X.operators.vacuum (X.operators.vector (List.ofFn (f ∘ a)))=operatorPays X (wage X (Prod.fst ∘ f) (Prod.snd ∘ f) ∘ a):=by
 let Y:= List.ofFn (f∘a)
 have hz(p:Sentence S): X.operators.evaluates p=(p.map X.operators.edits).prod (ℎ):=by
    induction p with
    | nil=> rfl
    | cons v p ih=> rw [Fields.evaluates,ih,List.map_cons,List.prod_cons,Module.End.mul_apply]
 have he:=hz Y
 unfold operatorPays; change inner ℂ (ℎ) (X.operators.evaluates Y)=_; rw [he]; unfold Y; rw [List.map_ofFn]; rfl

lemma crew_change_wage (v:Fin n→S.Union)(f:Fin n→Test4)(b:Test4): wage X v (Function.update f k b)=Function.update (wage X v f) k (Φ (v k) b):= by funext i; by_cases p:i=k <;> simp [p,wage]
lemma wage_advance (D :Equiv.Perm (Fin n))(v:Fin n→S.Union)(f:Fin n→Test4)(b:Test4)(P:Fin n→Module.End ℂ X.operators.domain)(p:∀ i,i≠k→P i=(wage X v f) i): operatorPays X (wage X v (Function.update f k b) ∘ D)= changeBill k X D P (Φ (v k) b):=by unfold changeBill; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; congr 1; rw[crew_change_wage]; congr 1; funext i; by_cases h:i=k<;> simp [h]; exact (p i h).symm

lemma sum_price {I:Type}[Fintype I](P:Fin n→Module.End ℂ X.operators.domain)(D:Equiv.Perm (Fin n))(v:I→Module.End ℂ X.operators.domain)(c:I→ℂ): operatorPays X (Function.update P k (∑ i:I,c i • v i) ∘ D)=∑ i:I, c i• operatorPays X (Function.update P k (v i) ∘ D):=by change (changeBill k X D P) _=_; rw [map_sum]; simp_rw [map_smul]; rfl

noncomputable def dragAlways (p:Poincare){Y:Surface S}{V:S.Rotation}{s:S.RealSpin}(e:X.Realizes (W:=Y) V s): Module.End ℂ X.operators.domain→ₗ[ℂ]Module.End ℂ X.operators.domain:={ toFun:= DragΛL X e p,map_add' v w:=by ext1 a; simp [DragΛL], map_smul' a x:=by ext1 v; simp [DragΛL] }
lemma drag_price {Y:Surface S}{V:S.Rotation}{s:S.RealSpin}(e:X.Realizes (W:=Y) V s) (v:Axis→ Module.End ℂ X.operators.domain)(c:Axis→ℂ) (p:Poincare): DragΛL X e p (∑ j:Axis,c j • v j)=∑ j:Axis,c j•DragΛL X e p (v j) := by change dragAlways X p e _=_; rw [map_sum]; simp_rw [map_smul]; rfl
#print axioms employed
#print axioms sum_price
end StressLaw
end YM.NSF.Boundary
end
