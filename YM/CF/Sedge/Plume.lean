import YM.CF.Sedge.Craft
/-! Exact list Wick expansion, left-to-right ordered. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {α n:Type*} [LinearOrder n][Fintype n]
structure Bout (α:Type*) where
  neg : Bool
  front : α
  back : List α
structure Cl (α:Type*) where
  cpos : Bool -- true = negative
  up : List (α × α)
  term : List α

def beside (x:α)(g:Bout α): Bout α:= ⟨!(g.neg),g.front,x::g.back⟩
def picks : List α→List (Bout α)
  | []=>[]
  | x::y=> ⟨false,x,y⟩ :: ((picks y).map (beside x))
def extendsU (x:α)(t:Cl α): Cl α:= {t with term:=x:: t.term}
def cites (x:α)(t:Cl α)(g:Bout α):Cl α:= ⟨ Bool.xor g.neg t.cpos,(x,g.front)::t.up,g.back⟩
def besideX (x:α)(c: Cl α): List (Cl α):= extendsU x c :: ((picks c.term).map (cites x c))
def claps : List α→ List (Cl α)
  | []=> [⟨false,[],[]⟩]
  | x::y=> (claps y).flatMap (besideX x)
def cval (v:Bool):ℂ:= if v then -1 else 1
lemma cneg(v:Bool):cval (!v)= -cval v:=by cases v <;> simp [cval]
lemma cxor(v w:Bool): cval (v^^w)=cval v * cval w:=by cases v<;>cases w<;>simp [cval]
def offer(d:α→α→ℂ)(t: Cl α):ℂ:= cval t.cpos * ((t.up.map fun x=> d x.1 x.2).prod)
def rollC(F:α→FC n)(l:List α):FC n:=(l.map F).prod
def chime(C:α→FC n)(q:Wave n)(l:List α): Wave n:=acts (rollC C l) q
@[simp] lemma emptyChime(C:α→FC n)(q:Wave n): chime C q []=q:=by simp [chime,rollC]
lemma charm(C:α→FC n)(q:Wave n)(l:List α)(x:α):chime C q (x::l)= acts (C x) (chime C q l):=by simp only [chime,rollC,List.map_cons,List.prod_cons,act_mul]
def seatsC(i:α)(d:α→α→ℂ)(C:α→FC n)(q:Wave n)(u:Bout α): Wave n:= (cval u.neg * d i u.front) • chime C q u.back
def invest (C:α→FC n)(q:Wave n)(d:α→α→ℂ)(c: Cl α):Wave n:=offer d c • chime C q c.term
lemma desc(c:ℂ)(v:List α)(S:α→Wave n):c • (v.map S).sum=(v.map (fun x=>c • S x)).sum:=by induction v with | nil=> simp| cons i l ih=> simp [smul_add,ih]
lemma cact (A:FC n)(v:List α)(S:α→Wave n): acts A (v.map S).sum=(v.map (fun x=> acts A (S x))).sum:=by induction v with | nil=>simp| cons i l ih=>simp [ih]
lemma plume (C A:α→ FC n)(q:Wave n)(d:α→α→ℂ)(h:∀ i,acts (A i) q=0)(g:∀ i j,antiB (A i) (C j)=d i j • 1)
    (i:α)(l:List α): acts (A i) (chime C q l)= ((picks l).map (seatsC i d C q)).sum:=by
  induction l with
  | nil=>rw [emptyChime,h]; rfl
  | cons j l ih=>
    let a:=A i; let c:=C j; let S:=seatsC i d C q
    have he (x:Bout α): S (beside j x)=(-1:ℂ) • acts c (S x):=by
      unfold S seatsC beside; dsimp only; rw [charm,cneg,map_smul,smul_smul,neg_mul,neg_one_mul]
    rw [charm,←act_mul,show A i * C j=_ from eq_sub_of_add_eq (g i j),act_sub,act_mul _ (A _),ih,act_smul,act_one]
    change _ - acts c ((picks l).map S).sum=_; rw [picks,List.map_cons,List.sum_cons,List.map_map,show seatsC i d C q ⟨false,j,l⟩= d i j • chime C q l by simp [seatsC,cval]]
    rw [show seatsC i d C q ∘ beside j=(fun x=>(-1:ℂ) • acts c (S x)) from funext he,←desc _ (picks l) (fun x=>acts c (S x)), ←cact]; simp [sub_eq_add_neg]
lemma partake (F C A:α→FC n)(q:Wave n)(d:α→α→ℂ)(h:∀ i,acts (A i) q=0)(g:∀ i j,antiB (A i) (C j)=d i j • 1)
    (hp:∀ i,F i=C i+A i)(i:α)(t:Cl α): acts (F i) (invest C q d t)=((besideX i t).map (invest C q d)).sum:=by
  let V:=invest C q d; let u:= t.term
  have he(x:Bout α):offer d t • seatsC i d C q x= V (cites i t x):=by
    unfold seatsC V invest offer cites; rw [smul_smul]; congr 1; dsimp only [List.map_cons,List.prod_cons]; rw [cxor]; ac_rfl
  nth_rw 1 [invest]; rw [hp,map_smul,act_add,←charm,plume _ _ _ _ h g, besideX,List.map_cons,List.sum_cons,smul_add, desc,List.map_map];
  exact congrArg (fun x:Wave n=>V (extendsU i t)+x) (by rw [show (fun x=>offer d t • seatsC i d C q x)=V ∘ cites i t from funext he])
lemma shadeW (F C A:α→FC n)(q:Wave n)(d:α→α→ℂ)(h:∀ i,acts (A i) q=0)(g:∀ i j,antiB (A i) (C j)=d i j • 1)(p:∀ i,F i=C i+A i)
    (l:List α):chime F q l=((claps l).map (invest C q d)).sum:=by
  induction l with
  | nil=> simp [claps,invest,offer,cval]
  | cons i l ih=>
    rw [charm,ih, cact, claps]; simp_rw [partake _ _ _ _ _ h g p]
    generalize claps l=v; induction v with | nil=>simp | cons a m h=> simp [h]
end YM.CF.Fock
