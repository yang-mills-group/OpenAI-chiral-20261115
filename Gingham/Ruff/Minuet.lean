import Gingham.Ruff.Gobelet
import YM.CF.Buffered.Diphthong

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical

open Nacre


open Buffered
open Reed (Fine think)
set_option synthInstance.maxSize 16000

open Heat

variable {I:Type*}[Fintype I][LinearOrder I]
lemma cuthbert1 (A B L:UNI I)(t:A.val*B.val=L.val)
 {T:FC I}{S:Finset I}{v:Bool}(h:Sector S v T):
 theta A (twist (quantU B) T)=theta L T:=by
  have up (k:I): theta A (twist (quantU B) (put k))=theta L (put k):=by
     rw [←create_put,twist_create,theta_upV,theta_upV,←act_mul,t]
  induction h with
  | zero => simp [theta_zero]
  | one => simp [theta_one]
  | up i _ => exact up i
  | down i _ => rw [takeF,map_star,theta_star,theta_star,up]
  | add _ _ a b=> rw [map_add,theta_add,theta_add,a,b]
  | mul _ _ a b=> rw [map_mul,theta_mul,theta_mul,a,b]
  | scale _ c a=> rw [twist_scalar,theta_smul,theta_smul,a]

lemma cuthbert2 (A B L:UNI I)(t:A.val*B.val= -L.val)
 {T:FC I}{S:Finset I}(h:Sector S false T):
 theta A (twist (quantU B) T)=theta L T:=by
  let R:=phaseU (I:=I) (-1) (by simp)
  have e: (L*R).val= -L.val:=by
    change _* ((-1:ℂ) • (1:Op I))= _
    rw [Algebra.mul_smul_comm,mul_one,neg_one_smul]
  rw [cuthbert1 A B (L*R) (t.trans e.symm) h,
    ←cuthbert1 L R _ rfl h]
  change theta L (twist (quantU (phaseU (I:=I) (-1) _)) T)=_
  rw [h.grade_diag, if_neg (by decide: ¬(false=true)),one_smul]

lemma owlette (N:Side)(a b:Shape)(V U:UNI SpinIdx):
    owl N a V * owl N b U = owl N (joinX a b) (U*V):= by
 rw [owl,owl, owl, ←mul_inv_rev,kio]

variable (i:Axis)(s:ℤ)
local notation "v"=>Window.pinLift i
lemma owl_plane :
 (owl N (Buffered.plane i s) v).val= -(carR i s N).val:=by
 let R:=carR i s N
 change star R.val= -R.val
 have u:R.val*R.val= -1:=carR_square i s
 calc
   _ = star R.val * (- (R.val*R.val)):=by rw [u,neg_neg,mul_one]
   _ = _:=by rw [mul_neg,←mul_assoc,R.property.1,one_mul]

def style (d:Shape)(U:UNI SpinIdx)(F: Mark N):Mark N:=
 fun x=> rotary d U (F (Yg d x.1,Yg d x.2))

lemma minuet (d:Shape)(U:UNI SpinIdx)
 {S:Support (More N)}{F:Mark N}(t:AtSupport false S F):
 reflMark i s (style d U F) = style (joinX (Buffered.plane i s) d) (U*v) F:=by
 let a:=Buffered.plane i s
 let b:=joinX a d
 have k: (carR i s N).val * (owl N d U).val= -(owl N b (U*v)).val:=by
   rw [show (carR i s N).val = -(owl N a v).val from by rw [owl_plane,neg_neg]]
   rw [neg_mul]
   exact congrArg (fun x:UNI (Single N)=> -x.val) (owlette ..)
 have det:detX b.s= !(detX d.s):= by
    change detX ((Signed.mirror i)*d.s)=_
    rw [det_p,det_t,Bool.true_xor]
 funext x
 change theta (carR i s N) (rotary d U (F
   (Yg d (Yg a x.1),Yg d (Yg a x.2))))=rotary b (U*v) (F _)

 rw [←kor, ←kor]
 unfold rotary
 rw [det]
 by_cases z:detX d.s=true
 · simp only [z, Bool.not_true, Bool.false_eq_true, if_false, if_true]
   exact theta_theta _ _ _ k (t.allV _).sector
 simp only [Bool.eq_false_iff.mpr z, Bool.not_false,Bool.false_eq_true,if_false, if_true]
 exact cuthbert2 _ _ _ k (t.allV _).sector


lemma stye_plain (F:Mark N):style (incX 1) 1 F=F:=by
 funext x
 have e:owl N (incX 1) 1=1:=by rw [owl,prep_one,inv_one]
 dsimp only [style]
 rw [Nacre.blank,Nacre.blank, Prod.mk.eta] -- tune
 show rotary (incX 1) 1 _=_
 rw [rotary, if_neg (show ¬detX (_:Shape).s = true from by
   change ¬detX 1 = true; rw [det_i]; decide),e]
 have h:quantU (1:UNI (Single N))=1:= Subtype.ext (quant_one ..)
 rw [h,twist_formula]
 simp

/-- Collapse any successive movements. Input order here: leftmost pose acts last. -/
def maiden
 : List (Axis×ℤ) → Mark N→ Mark N
 | [], f=>f
 | (a,w)::ps, f=>reflMark a w (maiden ps f)
def maidS:List (Axis×ℤ) → Shape
 | []=>incX 1
 | (a,w)::ps=>joinX (Buffered.plane a w) (maidS ps)
def maidU:List (Axis×ℤ) → UNI SpinIdx
 | []=>1
 | (a,_)::ps=>maidU ps * Window.pinLift a

lemma maidJ (l:List (Axis×ℤ)):
 JetS (maidS l).s false (detX (maidS l).s) (maidU l):=by
 induction l with
 | nil=>change JetS 1 false (detX 1) 1;rw [det_i]; exact calmSX
 | cons h l p =>
   obtain ⟨i,a⟩:=h
   change JetS _ false (detX ((Signed.mirror i)*(maidS l).s)) _
   rw [det_p,det_t]
   exact jet_add false true _ _ _ _ _ (mirrorX i) p
lemma procession (l:List (Axis×ℤ)){S:Support (More N)}{F:Mark N}(t:AtSupport false S F):
 maiden l F=style (maidS l) (maidU l) F:=by
 induction l with
 | nil=>exact (stye_plain F).symm
 | cons h l ih=> 
   obtain ⟨i,s⟩:=h
   rw [maiden,ih]
   exact minuet _ _ _ _ t
lemma owlag (w:Cover):
 owl N (lagX w) 1 = prepU (lagX (-w)) 1 inert N:=by
 unfold owl
 apply mul_left_cancel (a:=prepU (lagX w) 1 inert N)
 rw [mul_inv_cancel,kio,trips,one_mul]
 -- trips target?
 simp; exact (prep_one _).symm
#print axioms procession

lemma moveQ(s:ℤ){S:Support (More N)}{F:Mark N}(t:AtSupport false S F):
    reflMark i s (reflMark i 0 F)=style (lagX (hem i s)) 1 F:=by
 funext x
 let k:=Buffered.plane i s
 let o:=Buffered.plane i 0
 change theta (carR i s N) (theta (carR i 0 N)
   (F (Yg o (Yg k x.1),Yg o (Yg k x.2))))=rotary (lagX (hem i s)) 1 (F _)
 dsimp only [k,o]
 rw [←kor,←kor,plane_join,sub_zero,
    theta_theta _ _ _ (firm_join ..) (t.allV _).sector,
    rotary,owlag,if_neg (show ¬detX (_:Shape).s = true from by
        change ¬detX 1 = true; rw [det_i]; decide),
       zero_sub, neg_smul]; rfl

