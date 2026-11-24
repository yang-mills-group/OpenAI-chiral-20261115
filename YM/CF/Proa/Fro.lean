import YM.CF.Proa.Foss
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
set_option synthInstance.maxSize 8000
open Acorn
variable {D n Y:Type}[TopologicalSpace D][Fintype Y][DecidableEq Y][LinearOrder n][Fintype n]
variable {X:Master D Y}{O:n→Y}{R S:Seal Y}{A F:D→ FC n}{c K a h:ℝ}
abbrev cult(x:D)(v:FC n)(A:D→FC n):=exp (A x)*v*exp (-A x)
lemma tilt_u(x:D)(A:D→FC n)(v u): cult x (v*u) A=cult x v A*cult x u A:=by
 have ht:exp (-A x)*exp (A x)=1:=mul_eq_one_comm.mp (wind_inv (A x)); unfold cult; simp only [←mul_assoc]; rw [mul_assoc _ (exp _) (exp _), ht,mul_one]
lemma costsC(a:ℝ)(R S T:Seal Y)(v:R⊆S)(p:S⊆T): cost a R T=cost a R S*cost a S T:=by
 unfold Acorn.cost Branch.rent; rw [←Real.exp_add]; congr 1; have he: (T\R).card=(S\R).card+(T\S).card:=by
    rw [Finset.card_sdiff_of_subset v,Finset.card_sdiff_of_subset p,Finset.card_sdiff_of_subset (v.trans p)]; have hx:= card_le_card v; have ht:= card_le_card p; omega
 rw [he,Nat.cast_add,mul_add]
lemma pay_cut (p:R ⊆ S)(v:Carries X O S a h A c):Carries X O R a h A (Acorn.cost a R S*c):=by
 obtain ⟨I',A,W,H,Z,Y'⟩:=v; refine ⟨I',A,W,(fun i=>⟨(H i).1,(fun g=>⟨p.trans ((H i).2 g).1,((H i).2 g).2⟩)⟩),le_trans ?_ (mul_le_mul_of_nonneg_left Z (rent_pos ..|>.le)),Y'⟩
 rw [mul_sum]; refine sum_le_sum fun i _=>le_of_eq ?_; unfold Acorn.bill; by_cases v:(W i).2.2.2=0; · simp [v]
 rw [costsC a R S _ p ((H i).2 v).1]; ring

def Fume (k:ℕ)(a K h:ℝ):=worth k^2*(Real.exp a+K)*h
lemma fumeC (H:∀x,UnitR (A x))(hK:0≤ K)(p:∀ (i:I n), Drop X O a i (fun x=>unitL (A x) (Acorn.pen i)) K)(he:0≤a)(b:0≤h)(v: Carries X O S a (Fume X.k a K h) F c) :Carries X O S a h (fun x=>cult x (F x) A) c:=by
 obtain ⟨I',j,V,t,Y',w⟩:=v
 let W:=worth X.k; have hW:1≤W:=one_w _; let C':= Real.exp a+K; have hx(i): Drop X O a i (fun x=> cult x (Acorn.pen i) A) C':=by
    simp_rw [cult,fun x:D=> repel (A x) (H x)]; exact (Drop.fixed X i O a).add (p i)
 let N:= Fume X.k a K h; have hN:0≤N:=by unfold N Fume; positivity
 have hf(i:I'): Carries X O S a h (fun x=> cult x (valK (V i) x) A) (Acorn.bill a N S (V i)):=by
   let L:= (V i).2.1; let T:=(V i).1; let r:= (V i).2.2.2; let f:=(V i).2.2.1; let P(u:List (I n))(x:D):=f x • (u.map Acorn.pen).prod
   by_cases hk:r=0
   · have ht(x:D):f x=0:=norm_le_zero_iff.mp (le_trans ((t i).1.sumline x) (le_of_eq hk)); change Carries _ _ _ _ _ (fun x=>cult x (P L x) A) (Acorn.cost a S T*N^L.length*r); simp_rw [P,ht,zero_smul,cult,mul_zero,zero_mul,hk, mul_zero]; exact Carries.nil_eq
   obtain ⟨q,e,u⟩: S⊆T∧Even L.length∧∀ i∈L,O i.2∈T := (t i).2 hk
   have hv:T.Nonempty:=by have he:(Grove _ T):=(t i).1.travel hk; exact (show ∀ T:Seal Y,Grove X.frame T→T.Nonempty from fun T H=>by cases H <;> simp) _ he
   -- recursion counts pairs
   have hy(k:ℕ)(l:List (I n))(p:l.length=k+k)(u:∀ i∈l,O i.2∈T): Carries X O T a h (fun x=> cult x (P l x) A) (N^l.length*r):=by
     induction k generalizing l with
     | zero=> rw [show l=[] from List.length_eq_zero_iff.mp p]; simp only [P,List.map_nil,List.prod_nil,cult,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,wind_inv,List.length_nil,pow_zero,one_mul]
              let v: Capot n Y D:= (T,[], f, r); have hv:ryde X O T v:=⟨(t i).1,fun _=>⟨subset_rfl,⟨0,rfl⟩,fun _ v=>nomatch v⟩⟩
              have hp:= Carries.basic (a:=a) (h:=h) hv
              rw [show Acorn.bill a h T v=r by simp [Acorn.bill,v,Acorn.cost, Branch.rent]] at hp; exact hp
     | succ k ih=>
       cases l; simp at p
       next z l=>
        cases l; simp at p; omega
        next j l=>
         let Q(a:I n)(x:D):= cult x (Acorn.pen a) A
         have he':l.length=k+k:=by simp only [List.length_cons] at p; omega
         have hg: Carries X O T a h (fun x=>Q z x* Q j x) (W^2*h^2*C'*C'):=by
            let f (x:D):=(1:ℂ); have h:= (hx z).copp (hx j) he le_rfl (Pro.nonzero (X:=X) T (fun _=>(t i).1.travel hk) (c:=1)) (R:=T) (h:=h) (fun v=> ⟨subset_rfl,u z (by simp),u j (by simp)⟩)
            simpa only [one_smul,Acorn.cost,Finset.sdiff_self,Branch.rent, Finset.card_empty, Nat.cast_zero, mul_zero, Real.exp_zero,mul_one,norm_one] using h
         let K:= ih l he' (fun i v=>u i (by simp [v])); rw [show (fun x=> cult x (P (z::j::l) x) A)=(fun x=> Q z x*Q j x)*fun x=>cult x (P l x) A from funext fun x=>by rw [show P _ x=(Acorn.pen z*Acorn.pen j)*P l x by simp [P,_root_.mul_assoc,Algebra.mul_smul_comm],tilt_u,tilt_u]; rfl]
         apply (hg.product K hv he b).more; change W*_*_≤_; rw [List.length_cons,List.length_cons,pow_succ N,pow_succ N l.length]
         have hb:0≤r:=(t i).1.pos; have hu:0≤W^2*h^2*C'*C'*(N^l.length*r):=by unfold C'; positivity
         calc
           _ ≤ W^2*(W^2*h^2*C'*C'*(N^l.length*r)):=by rw [mul_assoc W]; gcongr; nlinarith
           _ = _:=by unfold W N C' Fume; ring
   obtain ⟨m,g⟩:=e; exact ((pay_cut q (hy m L g u)).more (le_of_eq (mul_assoc ..).symm))
 simp_rw [w,cult,mul_sum,sum_mul]; exact (Carries.all_s _ _ _ (fun i (_:i∈univ)=> hf i)).more Y'
end YM.CF.Proa
