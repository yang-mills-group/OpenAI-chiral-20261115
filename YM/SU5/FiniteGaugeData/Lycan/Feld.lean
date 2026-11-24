import YM.SU5.FiniteGaugeData.Jadot.Loyd
/-! # WP24: Wick recipe of occupied-tilted comparator in the chiral aperture

Arbitrary length, on noncommuting operator products. Recursion at the first creator, keep lengths of all lists explicit for later homogeneity. -/
set_option autoImplicit false
set_option synthInstance.maxSize 17000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 510000
noncomputable section
namespace YM.CF.Fock.Reduction.Lycan
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims Dijon Currency Fist Ziz Thera Spire Scroll Celeste Loyd
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{P Q:Op n}{x y:Wave n}
variable {A D:Type*}
/-- Sum over a later remover. At its site, the first remover replaces it; the list retains all its later creators. -/
def slid {E:Type*}[AddCommMonoid E][Module ℂ E](f:D→ℂ) (y:D)(W:List (A×D)→ E): List (A×D) → E
 | []=>0
 | (p,q)::R=> f q • W ((p,y)::R) + slid f y (fun T=> W ((p,q)::T)) R
-- termination binder f W
/-- Laplace (Wick) recipe, length checked externally. Inner $⟨w,oblique \cdot v⟩$ evaluated per-pair. This also identifies it without indexing/list→ FinType hacks. -/
def fed (C:A→D→ℂ): ℕ→ List (A×D) → ℂ
 | 0,[]=>1
 | 0,_::_=>0
 | _+1,[]=>0
 | n+1,(a,b)::V=> C a b*fed C n V-slid (C a) b (fed C n) V
/-- Uncolored filling. -/
abbrev Album (C:A→D→ℂ)(X:List (A×D)):= fed C X.length X
lemma sift_pure {E:Type*}[AddCommMonoid E][Module ℂ E](f:D→ℂ)(y:D)(W W':List (A×D)→E) (X:List (A×D))(p:∀ Y,Y.length=X.length → W Y=W' Y): slid f y W X=slid f y W' X:=by
 induction X generalizing W W' with
 | nil=> rw [slid,slid]
 | cons x X ih=>
    rcases x with ⟨a,b⟩; rw [slid,slid,p _ (by simp)]; congr 1
    exact ih _ _ (fun Z h=> p _ (by simp only [List.length_cons,h] )) -- tune congr
lemma spindle (C:A→D→ℂ)(X:List (A×D))(a:A)(b:D): Album C ((a,b)::X)= C a b*Album C X-slid (C a) b (Album C) X:=by
 change fed C _ _=_; rw [List.length_cons,fed]; exact congrArg _ (sift_pure (C a) b _ _ X fun Y h=> (by unfold Album; rw [h]:fed C X.length Y=Album C Y)) -- tune defeq
set_option linter.flexible false
variable (g:Standing Q P)
-- Volt as linear currency
lemma cellar : Volt Q P 0=0:=by simp [Volt]
lemma wages(X Y:FC n):Volt Q P (X+Y)=Volt Q P X+Volt Q P Y:=by unfold Volt; rw [act_add, inner_add_right,add_div]
lemma paysGap(X Y:FC n):Volt Q P (X-Y)=Volt Q P X-Volt Q P Y:=by unfold Volt; rw [act_sub,inner_sub_right,sub_div]
lemma currency(X:FC n)(c:ℂ):Volt Q P (c • X)=c*Volt Q P X:=by unfold Volt; rw [act_smul,inner_smul_right, mul_div_assoc]
lemma grain {I:Type*}(X:I→ FC n)(D:Finset I): Volt Q P (∑ i∈D,X i)=∑ i∈ D,Volt Q P (X i):=by
 classical
 induction D using Finset.induction_on with
 | empty=> rw [sum_empty,cellar,sum_empty]
 | insert i D p ih=> rw [sum_insert p,sum_insert p,wages,ih]
include g
lemma solar:Volt Q P 1=1:=by unfold Volt; rw [act_one,div_self (vision g (mantleP g.hedge) (mantleP g.carpet) 1).1]
-- projection of creator on right
local notation "Row"=> oblique Q P
lemma well_head(u:Ket n)(X:FC n): Volt Q P (create u*X)= Volt Q P (create (acts (oblique Q P) u)* X):=by
 let L:=acts Row u; let v:=u-L; have ht:=g.luxury; have he:acts Q v=0:=by unfold v L; rw [map_sub, ←act_mul, TuneC.crisp ht,sub_self]
 nth_rw 1 [← show v+L=u from sub_add_cancel ..]; rw [map_add,add_mul,wages]; let p:=mantle Q; have hf:Volt Q P (create v*X)=0:=by
    unfold Volt; rw [act_mul,←act_inner]; change (inner ℂ (acts (remove v) p) _ )/_=_; rw [tars g.carpet (mantleP g.carpet).1 he,inner_zero_left,zero_div]
 rw [hf,zero_add]
lemma stem_out(u:Ket n)(X:FC n):Volt Q P (X*create (acts (oblique Q P) u))=0:=by
 unfold Volt; have he:acts P (acts Row u)=acts Row u:=by rw [←act_mul,g.luxury.tray]
 rw [act_mul,tarp g.hedge (mantleP g.hedge).1 he,map_zero,inner_zero_right,zero_div]
omit g
variable (U:A→Ket n)(V:D→Ket n)
abbrev mark (a:A)(b:D): FC n:= create (U a)*remove (V b)
abbrev studio (X:List (A×D)):FC n:= (X.map (fun x=> mark U V x.1 x.2)).prod
abbrev cupE (Q P:Op n)(u:Ket n)(v:Ket n):= inner ℂ v (acts (oblique Q P) u)
lemma low_slide (x y:Ket n) : remove x* remove y= -(remove y*remove x):= by
 have h:= congrArg star (car_create y x); rw [star_add,star_mul,star_mul, star_zero] at h; exact eq_neg_of_add_eq_zero_left h
lemma duo(x y:Ket n)(z:inner ℂ x y=0): remove x* create y= -(create y* remove x):=by have h:=car x y; rw [z,zero_smul] at h; exact eq_neg_of_add_eq_zero_left h
lemma remove_comm (a:A)(q b:D)(p:inner ℂ (V b) (U a)=0): remove (V b) * mark U V a q= mark U V a q *remove (V b):=by
 unfold mark; rw [←mul_assoc,duo _ _ p,neg_mul,mul_assoc,low_slide (V b) (V q),mul_neg,neg_neg,mul_assoc]
variable (scale0:∀ (a:A)(b:D),inner ℂ (V b) (U a)=0)
include scale0 g
/-- Slide through later pairs to a ket: sign care. -/
private lemma trip (u:Ket n)(b:D) (W:FC n)(X:List (A×D)): Volt Q P (W * remove (V b) * create (acts (oblique Q P) u)*studio U V X )= slid (fun q=>cupE Q P u (V q)) b (fun Y=>Volt Q P (W *studio U V Y)) X:=by
 induction X generalizing W with
 | nil=> rw [studio,List.map_nil,List.prod_nil,mul_one,stem_out g,slid]
 | cons z X ih=>
    rcases z with ⟨p,q⟩; let R:=studio U V X; let D':=mark U V p q; let L:=acts Row u; let F:= create L; let Z:= cupE Q P u (V q); let D₀:=mark U V p b; let G:=remove (V b)
    have hF: F*D'=D'*F-Z • create (U p):=by
      unfold D' mark; rw [← mul_assoc,show F * create (U p)= -(_*F) from eq_neg_of_add_eq_zero_left (car_create ..),neg_mul,mul_assoc (create (U p)),show F*remove (V q)=Z • 1-remove (V q)*F from eq_sub_of_add_eq' (car ..),mul_sub,Algebra.mul_smul_comm,mul_one,neg_sub,mul_assoc]
    have hG:G*D'= D'*G:= remove_comm U V _ _ _ (scale0 _ _); have hv:G*create (U p)= -D₀:=duo _ _ (scale0 _ _)
    have hh: W*G*F*(D'*R)= (W*D')*G*F*R + Z • (W*(D₀*R)):=by
      rw [mul_assoc (W*G),←mul_assoc F,hF,sub_mul, mul_sub,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; simp only [mul_assoc]; rw [←mul_assoc G D',hG,←mul_assoc G (create _),hv,neg_mul,mul_neg,smul_neg,sub_neg_eq_add]; simp only [mul_assoc]
    rw [slid]; change Volt Q P (W*G*F*(D'*R))= Z • Volt Q P (W*(D₀*R))+ slid _ _ _ X
    rw [hh,wages,currency, smul_eq_mul,add_comm _ (Z*_),ih]
    refine congrArg _ (sift_pure _ b _ _ X (fun Y h=>?_)); show Volt Q P (W*D'*studio U V Y)=Volt Q P (W*(D'*studio U V Y)); rw [mul_assoc]
lemma pay_wick(a:A)(b:D)(X:List (A×D)): Volt Q P (studio U V ((a,b)::X)) = cupE Q P (U a) (V b)* Volt Q P (studio U V X)- slid (fun q=>cupE Q P (U a) (V q)) b (fun Y=> Volt Q P (studio U V Y)) X:=by
 let W:=studio U V X; let L:=acts Row (U a); let B:=remove (V b); let Z:=cupE Q P (U a) (V b); change Volt Q P (create (U a)* B*W)= _; rw [mul_assoc, well_head g,←mul_assoc]; change Volt Q P ( (create L*B)*W )= Z*Volt Q P W-_
 rw [show create L*B= Z • 1-B*create L from eq_sub_of_add_eq' (car ..), sub_mul,Algebra.smul_mul_assoc,one_mul,paysGap,currency]; exact congrArg _ (by simpa only [one_mul] using (trip g U V scale0 (U a) b 1 X)) -- tune
/-- Wick recursion in tilted spectral regime -/
lemma adjust(X:List (A×D)):Volt Q P (studio U V X)=Album (fun a b=>cupE Q P (U a) (V b)) X:=by
 suffices h:∀ (k:ℕ)(X:List (A×D)), X.length=k→ Volt Q P (studio U V X)=Album (fun a b=>cupE Q P (U a) (V b)) X from h _ X rfl
 intro k; induction k with
 | zero=>intro X h; rw [List.length_eq_zero_iff.mp h,studio,List.map_nil,List.prod_nil,solar g]; rfl
 | succ n ih=>
    intro X h; cases X with
    | nil=> simp only [List.length_nil, Nat.zero_ne_add_one] at h
    | cons x X => rcases x with ⟨a,b⟩; rw [List.length_cons,Nat.add_left_inj] at h; rw [spindle, pay_wick g U V scale0,ih _ h]; congr 1
                  apply sift_pure; exact fun Y v=> ih _ (v.trans h)
#print axioms adjust
end YM.CF.Fock.Reduction.Lycan
