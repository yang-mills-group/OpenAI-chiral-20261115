import GaugeFieldConstruction.Velma
import GaugeFieldConstruction.Jupa
/- Ordered ledger -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Topology Classical
open Roots Mew Roots.GJ
variable {I J B V W G E:Type}[LinearOrder I][Fintype I][DecidableEq J]
structure Lem (I J P V:Type) where
 seat: Finset J
 keys:List I
 val:P
 amt:V→ℂ
 won:ℝ
 pure: Bool
variable (g:Lem I J V B)(f:Lem I J W B)
def joint (r:ℝ)(q:G): Lem I J G B:=⟨g.seat∪f.seat,g.keys++f.keys,q,g.amt * f.amt, r*g.won*f.won,Bool.and g.pure f.pure⟩
#print joint
def egest (i:Finset J)(z:Key I)(x:B):ℂ:= if g.seat⊆ i then stalk g.keys (g.amt x) z else 0
lemma civic(r:ℝ)(q:G)(z:Key I)(x:B)(i:Finset J): egest (joint g f r q) i z x=egest g i z x*egest f i z x:=by
 by_cases p:g.seat ⊆ i <;> by_cases w:f.seat ⊆ i <;> simp [egest,joint,Finset.union_subset_iff,stalk,p,w] <;> ring
lemma eg_R(i:Finset J)(x:B):River (fun z:Key I=> egest g i z x):=by
 by_cases p:g.seat⊆ i; simp only [egest,if_pos p]; exact stalkR _ _; simp only [egest,if_neg p]; exact zeroR _
variable {A:Type}
def Lee (L:List A){E:Type}[AddCommMonoid E](ψ:A→E):E:=(L.map ψ).sum
lemma consA {E:Type}[AddCommMonoid E](L:List A)(g:A→E)(a:A): Lee (a::L) g=g a+Lee L g:=by simp [Lee]
lemma appA {E:Type}[AddCommMonoid E](S L:List A)(g:A→E): Lee (S++L) g= Lee S g+ Lee L g:=by simp [Lee]
lemma mapA {E:Type}[AddCommMonoid E](L:List A)(P:A→V)(g:V→E):Lee (L.map P) g= Lee L (fun i=>g (P i)):=by simp [Lee, Function.comp_def]
lemma joinA {E:Type}[AddCommMonoid E](L:List A)(P:A→List V)(g:V→E):Lee (L.flatMap P) g= Lee L (fun i=>Lee (P i) g):=by induction L with|nil=>rfl|cons i L h=>simp only [List.flatMap_cons,consA,appA,h]
lemma paidA {E:Type}[AddCommMonoid E](L:List A)(X Y:A→E)(p:∀ i∈ L,X i=Y i):Lee L X=Lee L Y:=congrArg List.sum (List.map_congr_left p) -- tune name
lemma sealA {E F:Type}[AddCommMonoid E][AddCommMonoid F](L:List A)(X:A→E)(p:E→+ F): p (Lee L X)=Lee L (fun i=>p (X i)):=by induction L with|nil=> exact map_zero p|cons i L h=> rw [consA,map_add, h,consA]
lemma scaleA {E:Type}[AddCommMonoid E][Module ℂ E](L:List A)(X:A→E)(z:ℂ): z • Lee L X=Lee L (fun i=>z • X i):=by induction L with|nil=> simp [Lee]|cons i L h=>rw [consA,smul_add,h,consA]
variable [LinearOrder G][Fintype G]
-- G leg type
abbrev Toil (I J T:Type):= List (Lem I J Unit T)
variable (Y:G→G→ Toil I J B)(X0:Finset J)(z:Key I)(x:B)(H:ℝ)
abbrev Book0 (I J G B:Type):= List (Lem I J (Option (G×G)) B)
abbrev Rain0 (I J G B:Type):= List (Lem I J G B)
def cryW (Q:Rain0 I J G B):Rad G:=Lee Q fun e=> egest e X0 z x • inPlace e.val
def cryY (Q:Book0 I J G B):PairLog G:= Lee Q fun e=>egest e X0 z x • (Pi.single e.val 1)
def cryH (i j:G):ℂ:=Lee (Y i j) (fun a=>egest a X0 z x)
#print cryW
variable (q:Book0 I J G B) (e:Lem I J (Option (G×G)) B)
def merP {A:Type}(e:Lem I J A B): Lem I J A B:={e with amt:= - e.amt}
lemma e_mer {A:Type}(e:Lem I J A B): egest (merP e) X0 z x= - egest e X0 z x:=by unfold egest; by_cases p:e.seat⊆X0<;>simp [merP,p,stalk]
def feint(i:G)(T:Lem I J (Option (G×G)) B):Rain0 I J G B:= T.val.elim [] (fun K=> ((Y i K.1).map fun R=> joint T R H K.2)++ ((Y i K.2).map fun R=> merP (joint T R H K.1)))
lemma hauls(i:G) : cryW X0 z x (feint Y H i e)=egest e X0 z x • rainfall (cryH Y X0 z x) i e.val:=by
 cases ht:e.val with
 | none=> simp only [ht,feint,rainfall,Option.elim_none,smul_zero]; rfl
 | some s=>
    rcases s with ⟨u,v⟩; simp_rw [cryW,feint,ht,Option.elim_some,appA,mapA,e_mer,civic,rainfall]
    unfold cryH; have he (V0:Toil I J B)(a:Rad G) : (Lee V0 (fun i=> egest i X0 z x)) • a = Lee V0 fun i=>egest i X0 z x • a:=by induction V0 with|nil=> simp [Lee]| cons i V ih=> rw [consA,add_smul, ih,consA]
    have hn(V0:Toil I J B)(P:Lem I J Unit B→Rad G): Lee V0 (fun i=> -P i)= -Lee V0 P:=by induction V0 with|nil=>simp [Lee]| cons i V h=>rw [consA, consA,h]; abel
    simp_rw [he,smul_sub,scaleA,mul_smul,neg_smul,mul_smul]; rw [hn,←sub_eq_add_neg]; rfl
-- sprouting
abbrev leaf (i:G): Lem I J G B:=⟨∅,[],i,1,1,true⟩
def frond (i:G):Rain0 I J G B:= leaf i :: q.flatMap (feint Y H i)
lemma trunk(i:G):cryW X0 z x (frond Y H q i)=drawP (cryH Y X0 z x) (cryY X0 z x q) i:=by
 unfold frond cryW drawP; rw [consA, joinA,show egest (leaf i) X0 z x=1 from (by simp [egest,leaf,stalk]),one_smul]; refine congrArg₂ (·+·) rfl ?_
 let A:= cryH Y X0 z x
 let T:PairLog G→ₗ[ℂ] Rad G:=
   { toFun:= fun v=> riseP A v i
     map_add':=by intro x y; simp [riseP,add_smul,sum_add_distrib]
     map_smul':=by intro z x; simp [riseP,smul_sum,mul_smul] }
 have h(t:Option (G×G)) : T (Pi.single t 1)=rainfall A i t:=by change (∑ a:Option (G×G),(Pi.single t 1:PairLog G) a • rainfall A i a)=_; rw [sum_eq_single t]; simp; intro j _ e; simp [Pi.single_apply,e,Ne.symm e]; simp
 unfold cryY; change _ = T.toAddMonoidHom (Lee _ _); rw [sealA]; refine paidA q _ _ fun t _=> (hauls _ _ _ _ _ _ _).trans ?_; change egest t _ _ _ • rainfall _ _ _= T (_ • _); rw [map_smul,h] -- tune
variable (u v:Rain0 I J G B)
def seedX : Book0 I J G B := u.flatMap fun i=> v.map fun j=> joint i j H (some (i.val,j.val))
private def fus_B : Rad G →ₗ[ℂ] Rad G →ₗ[ℂ] PairLog G:=
 { toFun:=fun u=>{
                toFun:= fun v=> fusT u v
                map_add':=fun x y=>funext fun i=>by cases i with| none=>simp [fusT]|some i=>simp [fusT,mul_add]
                map_smul':=fun z x=>funext fun i=>by cases i with| none=>simp [fusT]|some i=>simp [fusT,mul_left_comm] }
   map_add':=by intro x y; ext v i; cases i with| none=>simp [fusT]|some i=>simp [fusT,add_mul]
   map_smul':=by intro z x; ext v i; cases i with| none=>simp [fusT]|some i=>simp [fusT,mul_assoc] }
lemma cryPair : cryY X0 z x (seedX H u v)= fusT (cryW X0 z x u) (cryW X0 z x v):=by
 let D:= fus_B (G:=G)
 have hx(i j:G): fusT (inPlace i) (inPlace j)=Pi.single (some (i,j)) 1:=funext fun k=>by cases k with | none=> simp [Pi.single_apply,fusT] |some k=>rcases k with ⟨k,l⟩; by_cases p:i=k<;> by_cases q:j=l<;>simp [*,fusT,inPlace,Pi.single_apply,eq_comm]
 unfold seedX cryY cryW; rw [joinA]; --
 let T:= D.flip (cryW X0 z x v); change _= T.toAddMonoidHom (Lee _ _); rw [sealA]; refine paidA u _ _ fun i _=>?_
 rw [mapA]; change Lee v _=T (_ • _); rw [map_smul]; change _= _ • (D (inPlace i.val)).toAddMonoidHom (Lee _ _); rw [sealA, scaleA]; refine paidA v _ _ fun j _=>?_
 change egest (joint i j H (some (i.val,j.val))) X0 z x • (Pi.single _ _)=egest i _ _ _ • (D _) (_ • inPlace j.val); rw [map_smul,civic,mul_smul,show D (inPlace i.val) (inPlace j.val)=_ from hx ..]; rfl -- tune

def sprigW (i:G):Book0 I J G B:= v.flatMap fun j=>(Y i j.val).map fun e=>joint j e H none
lemma crySprig(i:G):cryY X0 z x (sprigW Y H v i)= quarry (cryH Y X0 z x) (cryW X0 z x v) i • L_0:=by
 let A:= cryH Y X0 z x; let T:Rad G →ₗ[ℂ] PairLog G:=
   { toFun:=fun x=>quarry A x i • L_0
     map_add':=by intro x y; simp [quarry,add_smul,add_mul,sum_add_distrib]
     map_smul':=by intro z x; simp [quarry,mul_assoc,←mul_sum]; rw [mul_smul] } -- tune
 unfold sprigW cryY cryW; rw [joinA]; change _=T.toAddMonoidHom (Lee _ _); rw [sealA]; refine paidA v _ _ fun j _=>?_
 rw [mapA]; change Lee _ _=T (_ • _); have hx : T (inPlace j.val)= A i j.val • L_0:=by unfold T quarry; simp [inPlace,Pi.single_apply,ite_mul]
 have hs (L:Toil I J B): Lee L (fun t=>egest t X0 z x) • (L_0 (I:=G))= Lee L fun y=>egest y X0 z x • L_0:=by induction L with|nil=>simp [Lee]|cons k L h=> rw [consA,consA,add_smul,h]
 rw [map_smul,hx,show A i j.val =Lee (Y i j.val) (fun t=>egest t X0 z x) from rfl,hs,scaleA]; refine paidA _ _ _ fun t _=>?_ ; rw [civic,mul_smul]; rfl

def toothW (i j:G) : Book0 I J G B:= seedX H (frond Y H q i) (frond Y H q j) ++ sprigW Y H (frond Y H q j) i
def growL : Book0 I J G B := match e.val with | none=>[e]| some (i,j)=> (toothW Y H q i j).map (fun k=>joint e k H k.val)
def topL (E:Book0 I J G B):= E.flatMap (growL Y H q)
lemma growP : cryY X0 z x (growL Y H q e)=egest e X0 z x • plotD (cryH Y X0 z x) (cryY X0 z x q) e.val:=by
 unfold growL
 cases h:e.val with
 | none=> simp only [cryY,consA,h]; exact add_zero _
 | some i=>
    rcases i with ⟨i,j⟩; unfold cryY; rw [mapA]; simp_rw [civic,mul_smul]; let T:=toothW Y H q i j; change Lee T (fun k=>egest e X0 z x • (egest k X0 z x • _))=_ -- tune metavars
    rw [←scaleA]; apply congrArg (egest e _ _ _ • ·); unfold T; rw [toothW,appA]; change cryY _ _ _ (seedX H (frond Y H q i) (frond Y H q j)) + cryY _ _ _ (sprigW Y H _ i)=_ -- tune matches
    rw [cryPair,crySprig,trunk,trunk]; rfl
lemma topP(E:Book0 I J G B): cryY X0 z x (topL Y H q E)=bondR (cryH Y X0 z x) (cryY X0 z x q) (cryY X0 z x E):=by
 let A:=cryH Y X0 z x; let B:= cryY X0 z x q
 let T:PairLog G →ₗ[ℂ] PairLog G :=
   { toFun:= fun v=> bondR A B v
     map_add':=by intro x y; simp [bondR,add_smul,sum_add_distrib]
     map_smul':=by intro z x; simp [bondR,smul_sum,mul_smul] }
 unfold cryY topL; rw [joinA]; change _=T.toAddMonoidHom (Lee _ _); rw [sealA]; refine paidA E _ _ fun i _=>?_ ; change cryY X0 z x (growL Y H q i)=T (_ • _); rw [map_smul,growP]; apply congrArg (egest i _ _ _ • ·); unfold T bondR; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [sum_eq_single i.val]; simp [A,B]; intro j _ h; simp [Pi.single_apply,h,Ne.symm h]; simp
end YM.CF.Fock.Wosk
end
