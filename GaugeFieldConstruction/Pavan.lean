import GaugeFieldConstruction.Kiwi
import GaugeFieldConstruction.Kuril
/- ordered clock output. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian CF
open Fineness Module Regis Regis.Head ProbabilityTheory Hood CF.Fock CF.Fock.Flux Pacts Prims
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.L2Operator NNReal InnerProductSpace
attribute [local instance] opCStarAlgebra
namespace Pitcher
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B:Op I}{u:Wave I}
variable {F:Type*} [NormedAddCommGroup F][InnerProductSpace ℝ F][MeasurableSpace F][BorelSpace F][FiniteDimensional ℝ F]
abbrev Panel (P A B:Op I)(u:Wave I)(L:F→FC I):ℂ:=∫ x,Worthy P A B u (L x)∂stdGaussian F
abbrev crownC (P A B:Op I)(u:Wave I)(L:F→FC I): Prop:= Integrable (fun x=>Worthy P A B u (L x)) (stdGaussian F)
abbrev syncR (W:List F)(g:FC I) : F→FC I:=fun x=> (dais W x:ℂ) • g
def wallX (x:F) : F→ℂ:= fun u=> (rub x u:ℂ)
abbrev monoG (v w:F)(x:F):ℂ := wallX v x*wallX w x
abbrev papaya (v w:F):ℂ:= (rub v w:ℂ)
lemma polyC0 (W:List F)(g:FC I) (P A B:Op I)(u:Wave I) : crownC P A B u (syncR W g) ∧ Panel P A B u (syncR W g)=(χfund 0 W:ℂ)* Worthy P A B u g:=by
 let U:=syncR W g; let H:= crestP P A B u
 unfold crownC Panel; simp_rw [show ∀ x:F,Worthy P A B u ((syncR W g) x)=_ from fun x=> (show H ((dais W x:ℂ) • g)=(dais W x:ℂ)*H g from map_smul H _ g)]; rw [entryD]; have he: lipW 0 W=dais W:=by funext i; simp [lipW,rub]
 constructor
 · have h: Integrable (dais W) (stdGaussian F):= he ▸ lip_int 0 W; exact ((show Integrable (fun x=> (dais W x:ℂ)) _ from Complex.ofRealCLM.integrable_comp h).mul_const _)
 rw [integral_mul_const,integral_complex_ofReal]; rfl
inductive Solid (I:Type*) [LinearOrder I][Fintype I] (F:Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] : (F→ FC I)→Prop
| raw (W: List F)(g:FC I) :Solid I F (syncR W g)
| double {f g:F→FC I} : Solid I F f → Solid I F g → Solid I F (f+g)
namespace Solid
lemma solid_pair {z:F→ FC I}(h:Solid I F z) (P A B: Op I)(u:Wave I) : crownC P A B u z:=by
 induction h with
 | raw i k=> exact (polyC0 ..).1
 | @double f g h1 h2 a b=> apply (a.add b).congr; exact Eventually.of_forall (fun x=> (show crestP P A B u (f x)+crestP P A B u (g x)=crestP P A B u (f x+g x) from (map_add ..).symm)) -- tune
lemma major (g:FC I): Solid I F (fun _=> g):=by convert Solid.raw ([]:List F) g using 1; ext1; simp [syncR,dais,factorV]
lemma scaler {z:F→ FC I}(h:Solid I F z)(a:ℂ) : Solid I F (a • z):=by
 induction h with
 | raw W g=> convert Solid.raw W (a • g) using 1; funext i; exact smul_comm a (dais W i:ℂ) g
 | double f g h' p=>rw [smul_add]; exact double h' p
lemma muls {f g:F→FC I}(v:Solid I F f)(h:Solid I F g) : Solid I F (f*g):=by
 induction v with
 | @double f s _ _ a b=>rw [add_mul]; exact double a b
 | raw x t=>
    induction h with
    | @double r s _ _ a b => rw [mul_add]; exact double a b -- ih
    | raw i u=> apply (show syncR x t*syncR i u=syncR (x++i) (t*u) from ?_) ▸ raw _ _; funext j; rw [Pi.mul_apply,syncR,syncR,syncR,Matrix.mul_smul,Matrix.smul_mul, show dais (x++i) j= dais x j*dais i j from (by simp [dais,factorV]),Complex.ofReal_mul,smul_smul,mul_comm]
lemma minusS {f g:F→ FC I}(v:Solid I F f)(h:Solid I F g):Solid I F (f-g):=by rw [sub_eq_add_neg, ← neg_one_smul ℂ g]; exact double v (h.scaler _)
lemma bundle {J:Type}[DecidableEq J] (S:Finset J)(f:J→F→FC I)(h:∀ i∈S,Solid I F (f i)): Solid I F (∑ i∈S,f i):=by
 induction S using Finset.induction_on with|empty=>rw [sum_empty]; exact major 0|@insert i s a b=>rw [sum_insert a]; exact double (h i (mem_insert_self ..)) (b (fun i p=> h i (mem_insert_of_mem p)))
end Solid
lemma spine_c {f g:F→FC I}(x:Solid I F f)(y:Solid I F g): Panel P A B u (f+g)= Panel P A B u f+Panel P A B u g:=by
 unfold Panel; simp_rw [show ∀ i:F,Worthy P A B u ((f+g) i)=Worthy P A B u (f i)+Worthy P A B u (g i) from fun _=>map_add (crestP ..) ..]; exact integral_add (x.solid_pair ..) (y.solid_pair ..)
lemma spine_s (f:F→FC I)(s:ℂ) : Panel P A B u (s • f) = s*Panel P A B u f:=by
 unfold Panel; simp_rw [show ∀ i:F,Worthy P A B u ((s • f) i)=s*Worthy P A B u (f i) from fun _=>map_smul (crestP ..) ..]; exact integral_const_mul ..
variable (P A B u F)
def ConeW : Submodule ℂ (F→FC I) where
 carrier:= {x|Solid I F x}
 add_mem':= fun x y=> Solid.double x y
 zero_mem':= Solid.major 0
 smul_mem':= fun c x h=> Solid.scaler h c
-- WARNING def uses P u for abbrev type infer (include explicit I) F; rewrite
variable {F}
def HallC : ConeW (I:=I) F→ₗ[ℂ] ℂ where
 toFun x:=Panel P A B u x.val
 map_add' i j:= spine_c i.property j.property
 map_smul' x i:= spine_s i.val x
namespace Coins
abbrev PatchC (I:Type*)[LinearOrder I][Fintype I](F:Type*)[NormedAddCommGroup F][InnerProductSpace ℝ F] := @ConeW I _ _ F _ _ -- includes unused instances? tune
-- functions use underlying. membership proof
variable {P A B u}{x y:F→ FC I}
lemma spine_d (p: Solid I F x)(g:Solid I F y) : Panel P A B u (x-y)= Panel P A B u x-Panel P A B u y:= (map_sub (HallC P A B u) (⟨_,p⟩: ConeW (I:=I) F) (⟨_,g⟩: ConeW (I:=I) F)) -- tune HSub
lemma spine_b {J: Type}[DecidableEq J] (S:Finset J)(f:J→F→FC I)(h:∀ i∈S,Solid I F (f i)) : Panel P A B u (∑ i∈S, f i)= ∑ i∈S,Panel P A B u (f i):=by
 induction S using Finset.induction_on with|empty=> simp [Panel,Worthy,translateW,quotation]|@insert i s g b=> have he(j)(p:j∈s):= h j (mem_insert_of_mem p); rw [sum_insert g,sum_insert g,spine_c (h _ (mem_insert_self ..)) (Solid.bundle s _ he), b he]
abbrev Wust (W:List F)(g:FC I) := syncR W g
lemma emit (W:List F)(g:FC I)(P A B:Op I)(u: Wave I) : Panel P A B u (Wust W g)= (χfund 0 W:ℂ)* crestP P A B u g:= (polyC0 ..).2
lemma Wust_K (X Y: List F)(x y:FC I): Wust X x*Wust Y y=Wust (X++Y) (x*y):=by
 funext j; rw [Wust,Wust,Wust,Pi.mul_apply,syncR,syncR,syncR,Matrix.mul_smul,Matrix.smul_mul, show dais (X++Y) j= dais X j*dais Y j from (by simp [dais,factorV]),Complex.ofReal_mul,smul_smul,mul_comm]
def Gn (i j:F): F→ FC I := Wust [i,j] 1- Wust ([]:List F) ((papaya i j) • 1)
def FN (F:Type*)[NormedAddCommGroup F][InnerProductSpace ℝ F](P A B:Op I){S:Finset I}(j:Seated S) : F→FC I:= Wust [] (paula P A B j)
def XN (P A B:Op I){S: Finset I}(i:F)(j:Seated S): F→ FC I:= Wust [i] (paula P A B j)
lemma Gn_S (i j:F): Solid I F (Gn i j):=Solid.minusS (.raw ..) (.raw ..)
lemma FN_S (P A B : Op I){S:Finset I}(i:Seated S): Solid I F (FN F P A B i):=.raw ..
lemma XN_S (P A B : Op I){S:Finset I}(i:F)(j:Seated S): Solid I F (XN P A B i j):=.raw ..
lemma w_C (W Y:List F)(x y:FC I):Solid I F (Wust W x * Wust Y y):=(Solid.raw W x).muls (.raw ..)
-- Gaussian pairing recursion via `simp`
end Coins
end Pitcher
end YM.Gleam.Guide
end
