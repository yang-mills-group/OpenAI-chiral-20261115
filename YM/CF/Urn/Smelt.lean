import YM.CF.Urn.Age
import YM.CF.Hake.Sea
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {ι α n m:Type*}[LinearOrder n][Fintype n]
-- symbols
abbrev Twig (n:Type*):= Lex ((Pastry.LeanV n) ⊕ Hake.Oboe n)
-- Lex instance for Bool × n? inferred only Pastry
instance : LinearOrder (Hake.Oboe n):= (inferInstanceAs (LinearOrder (Pastry.LeanV n))) -- diamond Dec eq preserved
abbrev twigExt :Pastry.LeanV n↪ Twig n:= Stilo.flame
abbrev twigCab : Hake.Oboe n↪ Twig n:=Stilo.seenH
abbrev twigS : Twig n → Pastry.LeanV n:= Sum.elim id id
abbrev tallC : Twig n → Bool:= Sum.elim (fun _=>true) (fun _=> false)
-- bare letters plus p matrix supplied
abbrev stick(P:Op n):Letter (Twig n) n where
 seek i:= !(twigS i).1
 sites i:=(twigS i).2
 matrix i := if tallC i then Proa.sprig (!(twigS i).1) P else 1
lemma stickUp(P:Op n)(i: Pastry.LeanV n): dialL (stick P) (twigExt i) =Pastry.drawT P i:=by
 rcases i with ⟨u,j⟩; cases u
 · change remove _=hideF _ _; rw [hideF,prong_t]; rfl
 change create _=seekF _ _; rw [seekF,prong_p]; rfl
lemma stickLo(P:Op n)(i:Hake.Oboe n): dialL (stick P) (twigCab i) = Hake.bell i:=by
 rcases i with ⟨u,j⟩; cases u
 · change remove (acts 1 (basisKet j))=takeF j; rw [act_one,remove_take]
 change create (acts 1 (basisKet j))=put j; rw [act_one,create_put]
-- full hidden antisym
lemma killH (P B: Op n)(v:IsStarProjection B)(x y: Ket n)(A :acts B x = x)(H:acts B y=0):inner ℂ x y=0:= by nth_rw 1 [←A]; rw [←v.isSelfAdjoint.star_eq,act_inner, H,inner_zero_right] -- tune
-- anti main & dust separately
variable {B W V E':Op n}
lemma wax (T:Letter ι n)(v:IsStarProjection B)(i j:ι): antiB (Proa.cane T B E' W V i) (Proa.cane T B E' W V j)=0∧ antiB (brim T B E' W V i) (brim T B E' W V j)=0:=by
 let X(C:Op n)(i:ι):= Proa.sprig (T.seek i) C * Proa.aqua T E' W V i
 let f(C:Op n)(i:ι):= acts (X C i) (basisKet (T.sites i)) -- C ( parser
 let P(C:Op n)(i:ι):= creed (T.seek i) (f C i)
 have h(C:Op n)(p:IsStarProjection C):antiB (P C i) (P C j)=0:=by
    have hv(i j)(g:T.seek i=true)(u:T.seek j=false):antiB (P C i) (P C j)=0:=by
       unfold P; rw [g,u]; unfold antiB; change remove _* create _+create _ * remove _= _; rw [car]
       have hx(a): C* C*a=C*a:=by rw [p.isIdempotentElem.eq]
       have ht :acts C (f C i)=f C i:=by unfold f X; rw [←act_mul,g]; change acts (C*(C*_)) _= acts (C*_) _; rw [←mul_assoc,hx]
       have hy: acts C (f C j)=0:=by unfold f X; rw [←act_mul,u]; change acts (C*((1-C)*_)) _=0; rw [←mul_assoc, Porth p,zero_mul, act_zero]
       rw [killH C C p _ _ ht hy,zero_smul]
    cases u:T.seek i<;>cases w:T.seek j
    · unfold P; rw [u,w]; exact car_create ..
    · rw [antiB_comm]; exact hv _ _ w u
    · exact hv _ _ u w
    unfold P; rw [u,w]; exact car_rem ..
 have ht(i):Proa.brim T B E' W V i=P (1-B) i:=by unfold Proa.brim P f X Proa.dust; generalize T.seek i=b; cases b <;> simp [Proa.sprig]
 rw [ht,ht]; exact ⟨h B v,h _ v.one_sub⟩
lemma melody(T:Letter ι n)(P:Op n)(W V:Op n)(E:Op n)(p:IsStarProjection P)(v:E*E=0)(k:star W*V=1)(i j:ι)(c:ℂ)(h:antiB (dialL T i) (dialL T j)=c • 1): fuelC T P E W V i j+ fuelC T P E W V j i=c:=by
 let A:=quant ((1-E)*W); let B:=quant (star V*(1+E)); let F:=dialL T; let G:=ivy T E W V; let C:=Proa.cane T P E W V; let H:=Proa.brim T P E W V
 have hu: A*B=1:=by
    unfold A B; rw [←quant_mul,←mul_assoc _ _ (1+E),mul_assoc (1-E),show W*star V=1 from (by rw [←star_star W,← star_mul,mul_eq_one_comm.mp k,star_one]),mul_one, sub_mul,one_mul,mul_add,mul_one,v,add_zero,add_sub_cancel_right,quant_one] -- tune star
 have hg(i j): A*(F i*F j)=(G i*G j)*A:=by rw [←mul_assoc, show A*F _= _ from super T E W V v k i, mul_assoc, show A*F _= _ from super T E W V v k j,←mul_assoc]
 have hf:c • (1:FC n)= antiB (G i) (G j):=by
    have he:A*(antiB (F i) (F j))=(antiB (G i) (G j))* A:=by rw [antiB,antiB,mul_add,hg,hg, ←add_mul]
    rw [show antiB _ _ = _ from h,Algebra.mul_smul_comm, mul_one] at he; rw [← mul_one (antiB (G i) _),←hu,←mul_assoc,←he, Algebra.smul_mul_assoc, hu]
 -- price read matrix identity
 obtain ⟨hw,hv⟩:= wax (B:=P) (E':=E) (V:=V) (W:=W) T p i j
 rw [show G i=C i+H i from ivy_v ..,show G j=C j+H j from ivy_v ..,Stilo.plus_sum, Stilo.minus_sum,Stilo.minus_sum, show antiB (H i) (C j)= _ from ash_F ..,antiB_comm (H j) (C i), show antiB (H j) (C i) = _ from ash_F .., show antiB (C i) (C j)=0 from hw,show antiB (H i) (H j)=0 from hv, add_zero,zero_add, ← add_smul] at hf
 rw [add_comm]; simpa using Matrix.ext_iff.mpr hf.symm (∅:Finset n) (∅:Finset n)
end YM.CF.Urn
