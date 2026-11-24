import GaugeFieldConstruction.Ved
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
variable (ι:G→J)(a b h r:ℝ)(U:G→ G→Toil I J B)(c d:ℝ)(p:FumedH a b ι U c d)(q:Book0 I J G B)(D:ℝ)(t:Puffion ι q)(s:MajorZ a b h q D)
variable (hr:0≤r)(ha:0≤a)(hb:0≤b)(ht:1≤h)
local notation "WG"=>weightV a b
local notation "WX"=>bil a b
include p hr ha hb
local notation "V0"=> Lem I J (Option (G×G)) B
local notation "Zv"=> Lem I J G B
local notation "Hh"=> Lem I J Unit B
lemma fleet_y (e:Lem I J (Option (G×G)) B)(v:0≤e.won)(y:J): let R:=fun k=>∑ i:G,Lee (U i k) fun x=>WG x; let Y:=fun k=>∑ i:G,Lee (U i k) fun x=>WX x y;
    ∑ i:G, Lee (feint U r i e) (fun v=>WX v y) ≤ r *WX e y *((e.val.map Prod.fst).elim 0 R+(e.val.map Prod.snd).elim 0 R)+ r * WG e *((e.val.map Prod.fst).elim 0 Y+(e.val.map Prod.snd).elim 0 Y):=by
 intro R Y; unfold feint; cases w:e.val with
 | none=> simp [w, Lee]
 | some V=>
    rcases V with ⟨u,z⟩; simp only [w,Option.elim_some,Option.map_some,appA,mapA]; simp only [R,Y,mul_add,mul_sum, ←lea_scale, ←sum_add_distrib]; refine sum_le_sum fun i _=> ?_
    have hx(k:G)(u:G): Lee (U i k) (fun x=> WX (joint e x r u) y) ≤ Lee (U i k) (fun x=> r*WX e y*WG x)+ Lee (U i k) (fun x=> r*WG e* WX x y):=(lea_p _ _ _ fun q t=>WP_union a b r e q ha hb hr v (p.fee0 i k q t) u y).trans_eq (lea_pair ..)
    apply le_trans (add_le_add (hx u z) (hx z u)); apply le_of_eq; abel
variable (hC:0 ≤ c)(hD:0≤ D)
include t s ht hC hD
def Aqua_D (i:G)(x:J):= Lee (frond U r q i) (fun v=>WX v x)
def Tax_D (r c d D:ℝ) := r*(D*c+D*c)+r*(D*d+D*d)
local notation "P_F" i:max => frond U r q i
lemma frond_bill (y:J): ∑ i:G, Aqua_D a b r U q i y ≤ Tax_D r c d D:=by
 let R:=fun k=>∑ i:G, Lee (U i k) fun x=>WG x; let Y:=fun k=>∑ i:G,Lee (U i k) fun x=>WX x y; let L(P:G×G→G)(X:G→ℝ)(p:V0):= (p.val.map P).elim 0 X; let V':=fun (u:Hh)=>WG u
 have ht2 : ∑ i:G, Aqua_D a b r U q i y = Lee q (fun e=> ∑ i:G, Lee (feint U r i e) (fun x=>WX x y)):=by
    unfold Aqua_D frond; simp_rw [consA,show ∀ i:G,bil a b (leaf (I:=I) (B:=B) i) y=0 from fun _=>by simp [bil],zero_add,joinA,lea_sum] -- tune
 let W1(P:G×G→G)(F:G→ℝ)(x:V0):= WX x y * L P F x
 let W2(P:G×G→G)(F:G→ℝ)(x:V0):= WG x * L P F x
 have h1(P:G×G→G): Lee q (W1 P R) ≤ D*c:=by
    refine le_trans (lea_p q _ (fun x=> c* WX x y) ?_) ((lea_scale _ _ _).le.trans ((mul_le_mul_of_nonneg_left (MajorZ.lower _ _ _ ht hb t.1 s y) hC).trans_eq (mul_comm ..)))
    intro i hi; rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ (WP_p _ _ _ hb (t.1 i hi) y); unfold L; cases i.val with|none=>exact hC|some x=> exact p.σ1 _
 have hY(i):0≤ Y i:=sum_nonneg fun j _=> lea_n _ _ fun x h=> WP_p _ _ _ hb (p.fee0 _ _ x h) y
 have h2(P:G×G→G)(v:∀i j,P (i,j)=i ∨ P (i,j)=j):Lee q (W2 P Y) ≤ D*d:=calc
    _ ≤ ∑ i,D*Y i:= mapf_ζ _ _ _ _ _ hY (legP ι a b h q D t s hb ht P v)
    _ =D*∑ i, privH a b U i y:=by rw [←mul_sum]; unfold Y privH; rw [sum_comm (f:=fun i j=>Lee (U j i) fun x=> WX x y)]
    _ ≤ _:=mul_le_mul_of_nonneg_left (p.pc0 _) hD
 rw [ht2]; refine le_trans (lea_p q _ (fun x=>r*(W1 Prod.fst R x+ W1 Prod.snd R x)+r*(W2 Prod.fst Y x+ W2 Prod.snd Y x)) (fun x h=>?_)) ?_
 · have hx:= fleet_y ι a b r U c d p hr ha hb x (t.1 x h) y
   apply hx.trans_eq; unfold W1 W2 L R Y; ring
 rw [lea_pair,lea_scale,lea_scale,lea_pair,lea_pair]; exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add (h1 _) (h1 _)) hr) (mul_le_mul_of_nonneg_left (add_le_add (h2 Prod.fst (fun _ _=>Or.inl rfl)) (h2 Prod.snd (fun _ _=>Or.inr rfl))) hr)
#print axioms frond_bill
omit hD hC ht ha s
lemma Aqua_p (x:J)(i:G):0≤ Aqua_D a b r U q i x:= lea_n _ _ (fun j t₀=>WP_p a b _ hb ((seed_Λ ι a b r U c d p q t hr _).1 j t₀) x)
end YM.CF.Fock.Wosk
end
