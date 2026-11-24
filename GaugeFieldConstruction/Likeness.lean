import GaugeFieldConstruction.Rosin
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d e:ℕ}{k:Side}
variable (n k)
abbrev billJ(i:mort x d):ℂ:= Lifted.winding n i.1.val * Lifted.winding k i.1.val
abbrev billZ(i:jungle x d):ℂ:=feeV n i*feeV k i
lemma bill_J(b:Bool)(i j:mort x d):billZ n k (some (b,i,j))=billJ n k i*billJ n k j:=mul_mul_mul_comm ..
variable {n k}
structure Ship (x y:Cover)(d e:ℕ)(p:Bool)(A:UNI (Single n))(B:UNI (Single k)):Prop where
 kcruise (b:Bool)(i:mort x d)(t: Single k): ∑ j:mort y e,(if hereF k j=t then billJ n k j*moko A p b (hereF n j) (hereF n i) else (0:ℂ))=moko B p b t (hereF k i)*billJ n k i
variable {p b:Bool}{A:UNI (Single n)}{B:UNI (Single k)}
lemma Ship.Vuns (S:Ship x y d e p A B)(i:jungle x d)(t:Wa k):
  ∑ j:jungle y e,(if hereV k j=t then billZ n k j * boostX A p (hereV n i) (hereV n j) else (0:ℂ))= boostX B p (hereV k i) t *billZ n k i:=by
 rcases i with _|a
 · rw [Fintype.sum_option, Finset.sum_eq_zero]
   · rcases t with _|t <;> simp [billZ,feeV,hereV,boostX]
   intro j _; split; exact mul_zero _; rfl
 rcases a with ⟨l,h,j⟩; rcases t with _|⟨m,s,g⟩
 · rw [Fintype.sum_option, Finset.sum_eq_zero]; · change _+0= (0:ℂ)*_; rw [zero_mul, add_zero, if_pos (show hereV (x:=y) (d:=e) k none= none from rfl)]; exact mul_zero _
   intro j p; rw [if_neg (by exact Option.some_ne_none _)]
 rw [Fintype.sum_option, if_neg (show hereV (x:=y) (d:=e) k none≠some (m,s,g) from by simp [hereV]),zero_add] -- nofun tune explicit jungle
 rw [Fintype.sum_prod_type,Finset.sum_eq_single (l.xor p)]; swap
 · intro i u v; apply sum_eq_zero; intro i' _; split
   · rw [show boostX A _ _ _=0 from (by simp [hereV,boostX,Ne.symm v]), mul_zero]
   rfl
 swap; · simp
 by_cases h0:l.xor p=m
 · subst m; rw [Fintype.sum_prod_type (α₁:=mort y e) (α₂:=mort y e)]; simp only [ hereV,Option.map_some,Option.some.injEq, Prod.mk.injEq,true_and,boostX,ite_true]; rw [bill_J,_root_.mul_mul_mul_comm,←S.kcruise l h s,← S.kcruise (!l) j g,Finset.sum_mul]; apply sum_congr rfl; intro a _; rw [mul_sum]; apply sum_congr rfl; intro b _; rw [bill_J]; by_cases hp:hereF k a=s <;> by_cases h0:hereF k b=g<;>simp only [hp,h0,and_false,and_true,ite_true,ite_false,mul_zero,zero_mul]; exact mul_mul_mul_comm ..  -- tune simp bill
 simp only [boostX, hereV, Option.map_some,Option.some.injEq,Prod.mk.injEq,h0,false_and,ite_false,ite_true, sum_const_zero,zero_mul]
lemma cone_p(f:Psu x d)(t:Wa n)(U:Pane n): pR n f t U =∑ j:jungle x d, if hereV n j=t then feeV n j*f j (onC n U) else 0:=by
 unfold pR; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i _; by_cases h:hereV n i=t<;>simp [isolate,h,Ne.symm]
private lemma cs_mulK (b:Bool)(x y:ℂ):cSignX b (x*y)=cSignX b x*cSignX b y:=by cases b<;>simp [cSignX]
private lemma cs_zeroK (b:Bool):cSignX b 0=0:=by cases b<;>simp [cSignX]
private lemma cs_sumK(b:Bool){I:Type}(T:Finset I)(f:I→ℂ): cSignX b (∑ i∈T,f i)=∑ i∈T,cSignX b (f i):= by cases b<;>simp [cSignX]
private lemma cs_feeK(b:Bool)(i:jungle x d): cSignX b (feeV n i)=feeV n i:=by cases b; rfl; exact feeV_S ..
abbrev cardsA (n:Side){x:Cover}{d:ℕ}(F:jungle x d→ℂ)(t:Wa n):= ∑ j:jungle x d,if hereV n j=t then feeV n j*F j else 0
lemma ChiefC (F:jungle x d→ℂ)(p b:Bool)(m:Side)(D:UNI (Single m))(t:Wa m): steerZ D b p (cardsA m F) t= ∑ i:jungle x d, boostX D p (hereV m i) t*(feeV m i*cSignX (b.xor p) (F i)):=by
    rw [stripeQ]; unfold cardsA; simp_rw [cs_sumK (b.xor p) (univ:Finset (jungle x d)), mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_eq_single (hereV m i),if_pos rfl,cs_mulK,cs_feeK]
    · intro j _ v; rw [if_neg (Ne.symm v), cs_zeroK,mul_zero]
    simp
lemma consignee (C:Ship x y d e p A B)(h:d<n.val)(v:e<n.val) (F:jungle x d→ℂ)(G:jungle y e→ℂ)(E:∀ i:jungle y e,cardsA n G (hereV n i)=steerZ A b p (cardsA n F) (hereV n i)): cardsA k G= steerZ B b p (cardsA k F):=by
 funext t
 let κL:=b.xor p; let X(j:jungle x d)(a: Single k):= κL
 -- steering evaluating transported cards


 let H(i:jungle x d):= feeV n i*cSignX κL (F i)
 have he(i:jungle y e):feeV n i*G i=∑ j:jungle x d,boostX A p (hereV n j) (hereV n i)*H j:=by rw [show feeV n i*G i= _ from (show feeV n i*G i=cardsA n G (hereV n i) from (by simp [cardsA,(hereI v).eq_iff])),E,ChiefC]
 have hx(i:jungle y e): feeV k i * G i=billZ n k i*(∑ j:jungle x d,boostX A p (hereV n j) (hereV n i)*H j):=by rw [←he, billZ,mul_mul_mul_comm,feeV_U,one_mul]
 rw [ChiefC]; unfold cardsA;  let z(i:jungle y e)(j:jungle x d):=if hereV k i=t then billZ n k i*boostX A p (hereV n j) (hereV n i) else 0
 rw [sum_congr rfl (g:=fun i:jungle y e=>∑ j:jungle x d,z i j*H j) (fun i _=> ?_),sum_comm]; swap
 · by_cases hv:hereV k i=t
   · rw [if_pos hv,hx,mul_sum]; apply sum_congr rfl; intro j _; unfold z; rw [if_pos hv,mul_assoc (billZ n k i) (boostX ..)]
   rw [if_neg hv,sum_eq_zero fun j _=> show z i j * H j=0 by unfold z; rw [if_neg hv,zero_mul]]
 apply sum_congr rfl; intro i _; rw [←sum_mul,show ∑ j,z j i=_ from C.Vuns i t]; unfold H billZ κL; rw [_root_.mul_assoc, mul_mul_mul_comm (feeV n i),feeV_U,one_mul]
-- Helper apply on pR for two supports origin/target. ship by Shape/Gauge. Uses recognition only at required target anchors.
structure Dockers (x y:Cover)(d e:ℕ)(p:Bool)(Φ Ψ:Pane n)(Φ' Ψ':Pane k)(A:UNI (Single n))(B:UNI (Single k)):Prop where
 carriage: Ship x y d e p A B
 origin:Agrees (cartO x d) (onC n Φ) (onC k Φ')
 target:Agrees (cartO y e) (onC n Ψ) (onC k Ψ')
variable {F:Psu x d}{G:Psu y e}{Φ Ψ:Pane n}{Φ' Ψ':Pane k}
lemma Dockers.passK (D:Dockers x y d e p Φ Ψ Φ' Ψ' A B)(h:d<n.val)(v:e<n.val)(H:∀ i, LocalOn (cartO x d) (F i))(K:∀ i, LocalOn (cartO y e) (G i))(u:αLines (pR n G) Ψ=steerZ A b p (αLines (pR n F) Φ)):αLines (pR k G) Ψ'=steerZ B b p (αLines (pR k F) Φ'):=by
 let X:= fun i=>F i (onC n Φ); let Y:=fun i=>G i (onC n Ψ)
 have hx(W:LinksC)(k':Side)(v:Pane k')(R:Cover)(d':ℕ)(P:Psu R d')(w:Agrees (cartO R d') W (onC k' v))(L:∀ i,LocalOn (cartO R d') (P i)):αLines (pR k' P) v=cardsA k' (fun i=> P i W):=by
    funext j; unfold αLines; rw [cone_p]; simp_rw [show ∀ i,P i (onC k' v)= P i W from fun i=> (L i _ _ w).symm]
 refine ?_; let T:= αLines (pR n G) Ψ
 rw [hx _ k Ψ' y e G D.target K,hx _ k Φ' x d F D.origin H]; apply consignee D.carriage h v X Y; intro i; have hf: αLines (pR n F) Φ=cardsA n X:=funext fun i=>cone_p ..; rw [←hf]; exact ((cone_p G (hereV n i) Ψ).symm.trans (congrFun u _)) -- tune
end ArtCart
end MastTin
end YM.CF.XGarden
end
