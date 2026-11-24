import YM.CF.Pastry.Bliss
set_option linter.unusedSectionVars false

/-! Berezin convention in explicit creator coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock NormedSpace Function Finset Pastry Phase
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [LinearOrder n] [Fintype n] [LinearOrder m] [Fintype m]
-- All exterior part
def Absorb (S : Finset n) (A : FC n) := ∃ f : Finset n→ℂ,A=∑ i ∈ S.powerset, f i • poke i
abbrev Plain (A : FC n) := Absorb univ A
namespace Absorb
variable {A B : FC n} {s t : Finset n}
lemma zero : Absorb s (0:FC n) := ⟨fun _=>0,by simp⟩
lemma one : Absorb s (1:FC n) := by
  refine ⟨fun i=> if i=∅ then 1 else 0,?_⟩; simp only [ite_smul,one_smul,zero_smul,sum_ite_eq',mem_powerset,empty_subset,ite_true]; exact (Poly.tag_void _).symm
lemma atom (h : s⊆t) : Absorb t (poke s) := ⟨fun i=> if i=s then 1 else 0,by simp [ite_smul,h]⟩
lemma blade {i:n} (h:i∈s) : Absorb s (put i) := by rw [show put i=poke {i} from (Poly.tag_once (cane n) i).symm]; exact atom (singleton_subset_iff.mpr h)
lemma scale (h : Absorb s A) (c:ℂ) : Absorb s (c • A) := by obtain ⟨f,rfl⟩:=h; exact ⟨fun i=>c*f i,by simp [smul_sum,smul_smul]⟩
lemma sum (h : Absorb s A) (g : Absorb s B) : Absorb s (A+B) := by obtain ⟨f,rfl⟩:=h; obtain ⟨t,rfl⟩:=g; exact ⟨f+t,by simp [sum_add_distrib,add_smul]⟩
lemma lot {Y : Type*} (S : Finset Y) (v : Y→FC n) (h : ∀ i∈S,Absorb s (v i)) : Absorb s (∑ i∈S,v i) := by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [sum_empty]; exact zero
  | insert i S p ih=> rw [sum_insert p]; exact (h i (mem_insert_self ..)).sum (ih (fun i g=>h i (mem_insert_of_mem g)))
lemma times (h : Absorb s A) (g : Absorb s B) : Absorb s (A*B) := by
  obtain ⟨f,rfl⟩:=h; obtain ⟨w,rfl⟩:=g
  rw [sum_mul]; apply lot; intro i k; rw [mul_sum]; apply lot; intro j l
  rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; apply scale; apply scale; rw [poke,poke,Poly.tag_mul]; split_ifs; exact (atom (union_subset (mem_powerset.mp k) (mem_powerset.mp l))).scale _; exact zero
lemma eval (h : Absorb s A) (g : Absorb t B) (v : Poly n m) : v.eval (A*B)=v.eval A*v.eval B := by
  obtain ⟨f,rfl⟩:=h; obtain ⟨o,rfl⟩:=g
  rw [sum_mul,map_sum,map_sum,map_sum,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum,map_sum,mul_sum]; apply sum_congr rfl; intro j _; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; simp only [map_smul,v.eval_prod, v.eval_oneT,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma cold (h : Absorb s A) (p : ¬t⊆s) : crumb A t=0 := by obtain ⟨f,rfl⟩:=h; rw [crumb_sum,sum_eq_zero]; intro i h; rw [crumb_scale,chip,if_neg (show t≠i from fun k=>p (k.symm ▸ mem_powerset.mp h)),mul_zero]
lemma packs (h : Absorb s A) (u : s⊆t):Absorb t A := by obtain ⟨f,rfl⟩:=h; exact lot _ _ (fun i p=> (atom (Finset.Subset.trans (mem_powerset.mp p) u)).scale _)
lemma full (h : Plain A) : A=∑ i:Finset n, crumb A i • poke i := by
  obtain ⟨f,h⟩:=h; have he : @powerset n univ=univ := by ext; simp
  rw [he] at h; nth_rw 1 [h]; apply sum_congr rfl; intro i g; congr 1; rw [h,crumb_sum,sum_eq_single_of_mem _ g,crumb_scale,chip,if_pos rfl,mul_one]; intro j k h; rw [crumb_scale,chip,if_neg h.symm,mul_zero]
end Absorb
-- bars positive come first, columns descending, each with negative. No relative ordering assumed for ambient union.
abbrev EF (n : Type*) := FC (LeanV n)
abbrev bar (i:n):EF n:= wire false i
abbrev col (i:n):EF n:=wire true i
abbrev θ (n : Type*) [LinearOrder n] [Fintype n] : Poly n (LeanV n) := ⟨bar,fun i j=>put_put _ _⟩
abbrev η (n : Type*) [LinearOrder n] [Fintype n] : Poly n (LeanV n) := ⟨col,fun i j=>put_put _ _⟩
-- coefficient makes last-oriented insertion formulas simple
def press : ℕ→ℂ
  | 0=>1
  | i+1=> -((-1:ℂ)^i * press i)
lemma press_size (i) : ‖press i‖=1 := by induction i with | zero=> simp [press] | succ n ih=> rw [press]; simp [ih,norm_pow]
def monu (s t: Finset n) : EF n := press t.card • ((θ n).tag s*(η n).tag t)
lemma monu_n (s : Finset n) (i : n) (p : i∉s) (t) : monu (insert i s) t=parity i s • (bar i * monu s t) := by
  rw [monu,monu,Poly.tag_any _ _ _ p,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,mul_assoc,smul_comm] -- tune
lemma monu_v (s t:Finset n) (i:n) (p:i∉t) : monu s (insert i t)= - (parity i t • (monu s t*col i)) := by
  rw [monu,card_insert_of_notMem p,Poly.tag_any _ _ _ p,Poly.flip _ t i,Algebra.mul_smul_comm, Algebra.mul_smul_comm,monu,Algebra.smul_mul_assoc,←mul_assoc]
  change press (t.card+1) • _=_; simp only [press,smul_smul,neg_mul,neg_smul]; congr 2
  change (-1:ℂ)^t.card * press _ * _=_; calc
    _ = ((-1:ℂ)^t.card * (-1:ℂ)^t.card)*(parity i t * press t.card) := by ring
    _ = _ := by rw [←mul_pow]; simp
lemma monu_both {i:n} {s: Finset n} (p:i∉s) : monu (insert i s) (insert i s) = -(bar i * monu s s * col i) := by rw [monu_n _ _ p, monu_v _ _ _ p,mul_neg,Algebra.mul_smul_comm,smul_neg,smul_smul,parity_sq, one_smul,mul_assoc]
lemma monu_nil : monu (∅:Finset n) ∅=1 := by simp [monu,Poly.tag_void,press]
def index (s t: Finset n) : Finset (LeanV n) := s.image (Prod.mk false) ∪ t.image (Prod.mk true)
@[simp] lemma index_b (s t:Finset n) (i:n) : (false,i)∈ index s t↔ i∈s:= by simp [index]
@[simp] lemma index_c (s t:Finset n) (i:n): (true,i)∈ index s t↔i∈t := by simp [index]
lemma index_n (s t: Finset n) (i:n) : index (insert i s) t= insert (false,i) (index s t) := by simp [index]
lemma index_v (s t: Finset n) (i:n): index s (insert i t)=insert (true,i) (index s t) := by simp [index]
lemma index_inj {s t a b : Finset n} (h : index s t=index a b): (s,t)=(a,b) := Prod.ext (Finset.ext fun i=>by rw [←index_b s t, h]; exact index_b ..) (Finset.ext fun i=>by rw [←index_c s t,h]; exact index_c ..)
def coldSet (s:Finset (LeanV n)) (v:Bool):= Finset.univ.filter fun i=>(v,i)∈s
lemma index_from (s : Finset (LeanV n)) : index (coldSet s false) (coldSet s true)=s := by ext ⟨b,i⟩; cases b <;> simp [coldSet]
lemma monu_unit (s t: Finset n) : ∃ c:ℂ, ‖c‖=1 ∧ monu s t=c • poke (index s t) := by
  induction s using Finset.induction_on with
  | empty=>
    induction t using Finset.induction_on with
    | empty=> refine ⟨1,norm_one,?_⟩; simp only [monu_nil,index,image_empty, union_empty,poke,Poly.tag_void,one_smul]
    | insert i t g ih=>
      obtain ⟨c,h,e⟩:= ih; let x : Finset n := ∅; let T:=index x t; let A:LeanV n:=(true,i)
      change ∃ c, ‖c‖=1 ∧ monu x _=_; rw [monu_v _ _ _ g, show monu x t=_ from e,index_v]
      have he : Disjoint T {A}:= by simp [T,A,g]
      have ht : poke T * col i = Poly.sail T {A} • poke (insert A T) := by
        rw [show col i=poke {A} from (Poly.tag_once (cane _) A).symm,poke,poke,Poly.tag_mul,if_pos he]; congr 1; rw [union_singleton]; -- tune
      let z:= - (parity i t*(c* Poly.sail T {A})); refine ⟨z,by simp [z,norm_pow,Poly.sail_size,h,parity],?_⟩
      rw [Algebra.smul_mul_assoc,ht, smul_smul,smul_smul]; unfold z; rw [neg_smul,mul_assoc]
  | insert i s g ih=>
    obtain ⟨c,h,e⟩:=ih; let T:=index s t; let A:LeanV n:=(false,i)
    have ht : Disjoint ({A}:Finset (LeanV n)) T:=by simp [T,A,g]
    have he : bar i*poke T=Poly.sail {A} T • poke (insert A T) := by rw [show bar i=poke {A} from (Poly.tag_once (cane _) A).symm,poke,poke, Poly.tag_mul,if_pos ht,singleton_union] -- tune
    let v:= parity i s*(c*Poly.sail {A} T); refine ⟨v,by simp [v,norm_pow,Poly.sail_size,h,parity],?_⟩
    rw [monu_n _ _ g t, index_n,e,Algebra.mul_smul_comm,he,smul_smul, smul_smul,mul_assoc] -- order assoc
lemma monu_abs (s t: Finset n) : Plain (monu s t) := by obtain ⟨c,g,h⟩:=monu_unit s t; rw [h]; exact (Absorb.atom (subset_univ _)).scale _
def tuneC (s t: Finset n):= (monu_unit s t).choose
def zap (s t: Finset n) (A : EF n) := star (tuneC s t)*crumb A (index s t)
lemma zap_one (s t x y : Finset n) : zap s t (monu x y)=if (s,t)=(x,y) then 1 else 0 := by
  have h := (monu_unit x y).choose_spec; change ‖tuneC x y‖=1 ∧ _ at h
  rw [h.2,zap,crumb_scale,chip]; by_cases l:(s,t)=(x,y)
  · obtain ⟨rfl,rfl⟩:= Prod.mk.inj l; rw [if_pos rfl,if_pos rfl,mul_one]; exact scale_unit_self (c:=tuneC s t) h.1
  rw [if_neg (show index s t ≠ index x y from fun h=> l (index_inj h)), if_neg l,mul_zero,mul_zero]
lemma zap_free (s t: Finset n) : zap s t 0=0 := by unfold zap crumb; simp
lemma zap_s (p : ℂ) (A : EF n) (s t : Finset n) : zap s t (p • A)=p*zap s t A := by simp only [zap,crumb_scale,mul_left_comm]
lemma zap_l (A B : EF n) (s t:Finset n) : zap s t (A+B)=zap s t A+zap s t B := by simp only [zap,crumb_add,mul_add]
lemma zap_sum {I : Type*} (S : Finset I) (f : I→ EF n) (s t : Finset n) : zap s t (∑ i∈S,f i)=∑ i∈S,zap s t (f i) := by simp only [zap,crumb_sum,mul_sum]
lemma absorb_monu {A : EF n} (h : Plain A) : A=∑ s:Finset n,∑ t:Finset n, zap s t A • monu s t := by
  let x (p:Finset n × Finset n):=index p.1 p.2
  have hv : Bijective x := ⟨fun a b e=> index_inj e,fun s=> ⟨(coldSet s false,coldSet s true),index_from _⟩⟩
  let f:= Equiv.ofBijective x hv
  nth_rw 1 [h.full]; rw [←Equiv.sum_comp f (fun i=>crumb A i • poke i),Fintype.sum_prod_type]; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=>?_
  have hp := (monu_unit a b).choose_spec
  change crumb A (index a b) • _=_; rw [hp.2, zap,smul_smul]; change crumb A (index a b) • poke _ = (_*_*tuneC a b) • _; rw [mul_right_comm,scale_unit_self (show ‖tuneC a b‖=1 from hp.1),one_mul]; rfl
end YM.CF.Reed
