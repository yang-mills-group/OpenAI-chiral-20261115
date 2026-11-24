import YM.CF.Acorn.Pulse
import YM.CF.Jet.Foster
/-! Supported operator polynomial. Uses relative charges by the growth of the connected
support over a **mandatory** footprint. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D:Type} [LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D]
-- no gauge decorations (kernel family tensor prescriptions later)
structure Master (D Y:Type) where
 frame:Branch.Field Y
 moves: Seal Y→ D→ D→ Prop
 grow(S T:Seal Y): S⊆T→∀ x y,moves T x y→moves S x y
 draw: Draw D
 k:ℕ
variable {X:Master D Y}{R S T:Seal Y}{a b c H d:ℝ}{F G:D→ℂ}
structure Pro (X:Master D Y)(S:Seal Y)(F:D→ℂ)(c:ℝ):Prop where
 pos: 0≤c
 travel : c≠0→ Grove X.frame S
 cont: Continuous F
 sumline x : ‖F x‖≤c
 reads x y:X.moves S x y→ F x=F y
 plot: OrderD X.draw X.k F c
def worth (k:ℕ):ℝ:=2^k * ‖ContinuousLinearMap.mul ℝ ℂ‖
lemma one_w (k:ℕ):1≤worth k :=by
 let P:=ContinuousLinearMap.mul ℝ ℂ
 have hg:1 ≤ ‖P‖:=by
   have hh:= (P 1).le_opNorm 1; have he:=P.le_opNorm 1
   change ‖(1:ℂ)*1‖ ≤ _*_ at hh; rw [mul_one,norm_one,mul_one] at hh; rw [norm_one,mul_one] at he; exact hh.trans he
 exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hg
namespace Pro
lemma larger (h:Pro X S F c)(g:S⊆T)(p:c≠0→Grove X.frame T)(v:c ≤ d)(e:c=0→d=0): Pro X T F d:=⟨h.pos.trans v,fun l=>p (fun t=>l (e t)),h.cont,fun t=> (h.sumline _).trans v,fun x y t=>h.reads _ _ (X.grow S T g x y t),fun E _ _ _ W f p t x l=> (h.plot E W f p t x l).mono v⟩
lemma sum(h:Pro X S F c)(g:Pro X S G d): Pro X S (F+G) (c+d):=by
 refine ⟨add_nonneg h.pos g.pos,?_,h.cont.add g.cont,fun x=>(norm_add_le ..).trans (add_le_add (h.sumline _) (g.sumline _)),fun x y f=> congrArg₂ (fun x y:ℂ=> x+y) (h.reads x y f) (g.reads x y f),fun E _ _ _ W f p t x l=> (h.plot E W f p t x l).add (g.plot E W f p t x l)⟩
 intro hg; by_cases he:c=0; exact g.travel (by rwa [he,zero_add] at hg); exact h.travel he
lemma nonzero {X:Master D Y} {c:ℂ}(S:Seal Y)(e:c≠0→Grove X.frame S): Pro X S (fun _=>c) ‖c‖:=⟨norm_nonneg _,fun g=>e (by simpa using g),continuous_const,fun _=>le_rfl,fun _ _ _=> rfl,fun E _ _ _ S x p t _ _=>allows_const _ le_rfl⟩
lemma twice(h:Pro X S F c)(g:Pro X T G d)(p:c≠0→d≠0→ (S∩T).Nonempty):Pro X (S∪T) (F*G) (worth X.k*c*d):=by
 have hx:=one_w X.k; have hp:=h.pos; have hh:=g.pos
 refine ⟨by positivity,fun v=>?_,h.cont.mul g.cont,fun x=>?_,fun x y l=>congrArg₂ (fun x y:ℂ=> x*y) (h.reads x y (X.grow S (S∪T) subset_union_left _ _ l)) (g.reads x y (X.grow T (S∪T) subset_union_right _ _ l)),fun E _ _ _ W f p t x l=> (h.plot E W f p t x l).bilinear _ (g.plot E W f p t x l) (le_refl ‖ContinuousLinearMap.mul ℝ ℂ‖)⟩
 · have he:= right_ne_zero_of_mul (left_ne_zero_of_mul v); have ht:=right_ne_zero_of_mul v; obtain ⟨u,k⟩:=p he ht; exact (h.travel he).unite (g.travel ht) (mem_inter.mp k).1 (mem_inter.mp k).2
 rw [Pi.mul_apply,norm_mul]; exact mul_le_mul ((h.sumline _).trans (le_mul_of_one_le_left h.pos hx)) (g.sumline _) (norm_nonneg _) (by positivity)
lemma sc(h:Pro X S F c)(z:ℂ):Pro X S (z • F) (‖z‖*c):=by
 let L:=ContinuousLinearMap.mul ℝ ℂ z; have he: ‖L‖ ≤ ‖z‖ :=ContinuousLinearMap.opNorm_le_bound (f:=L) (norm_nonneg _) (fun y=>le_of_eq (norm_mul z y))
 exact ⟨mul_nonneg (norm_nonneg z) h.pos,fun h'=>h.travel (right_ne_zero_of_mul h'),L.continuous.comp h.cont,fun x=> (L.le_opNorm _).trans (mul_le_mul he (h.sumline _) (norm_nonneg _) (norm_nonneg _)),fun x y t=> congrArg (fun p:ℂ=>z*p) (h.reads x y t),fun E _ _ _ W f p t x l=> (h.plot E W f p t x l).linear L he⟩
end Pro

def cost(a:ℝ)(R S:Seal Y):ℝ:= rent a (S \ R)
lemma cost_join(h:0≤a)(R S T:Seal Y): cost a R (S∪T) ≤ cost a R S * cost a R T :=by rw [cost,cost,cost,union_sdiff_distrib]; exact rent_join _ _ h
lemma cost_trim (h:0≤a)(R S:Seal Y):cost a R S ≤ Branch.rent a S:=by unfold cost rent; gcongr; exact Finset.sdiff_subset

abbrev Capot (n Y D:Type):= Seal Y × List (I n) × (D→ℂ) × ℝ
def ryde (X:Master D Y)(H:n→Y)(R:Seal Y)(i:Capot n Y D):Prop := Pro X i.1 i.2.2.1 i.2.2.2 ∧ (i.2.2.2≠0 → R⊆i.1 ∧ Even i.2.1.length ∧ ∀ x∈i.2.1,H x.2 ∈ i.1)
def bill(a h:ℝ)(R:Seal Y)(i: Capot n Y D):ℝ:= cost a R i.1*h^i.2.1.length*i.2.2.2
def valK(x:Capot n Y D)(U:D):FC n:= x.2.2.1 U • (x.2.1.map pen).prod
def Carries (X:Master D Y)(H:n→Y)(R:Seal Y)(a h:ℝ)(F:D→FC n)(L:ℝ):Prop:=∃ (I':Type) (_:Fintype I')(w:I'→Capot n Y D), (∀ i, ryde X H R (w i)) ∧ (∑ i, bill a h R (w i))≤ L ∧ ∀ x, F x=∑ i,valK (w i) x -- Exists Type in Prop universes
variable {h L K:ℝ}{O:n→Y}{A B:D→FC n}
namespace Carries
lemma basic {i:Capot n Y D} (v:ryde X O R i): Carries X O R a h (valK i) (bill a h R i):=⟨Unit,inferInstance,fun _=>i,fun _=>v,by simp,by simp⟩
lemma add (e:Carries X O R a h A K)(g:Carries X O R a h B L):Carries X O R a h (A+B) (K+L):=by
 obtain ⟨χ,hx,x,H,p,U⟩:=e; obtain ⟨η,g,y,k,h,W⟩:=g; refine ⟨χ⊕η,inferInstance, Sum.elim x y,fun i=>Sum.rec (motive:=fun i=> ryde _ _ _ _) H k i,?_,?_⟩
 · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]; exact add_le_add p h
 intro i; simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,Pi.add_apply,U,W]
lemma sMul(e:Carries X O R a h A K)(z:ℂ): Carries X O R a h (z • A) (‖z‖*K):=by
 obtain ⟨χ,hx,x,H,p,U⟩:= e
 let Q(i:χ):Capot n Y D:= ((x i).1,(x i).2.1,z • (x i).2.2.1,‖z‖*(x i).2.2.2)
 refine ⟨χ,inferInstance,Q,fun i=>⟨(H i).1.sc _,fun t=>(H i).2 (right_ne_zero_of_mul t)⟩,?_,?_⟩
 · unfold Q bill; dsimp only; simp_rw [mul_left_comm (_*h^_) ‖z‖,← mul_sum]; exact mul_le_mul_of_nonneg_left p (norm_nonneg _)
 intro u; rw [Pi.smul_apply,U, Finset.smul_sum]; exact sum_congr rfl fun i _=>by rw [valK,valK,smul_smul]; rfl
lemma nil_eq : Carries X O R a h 0 0:=⟨Fin 0,inferInstance,(fun x=>Fin.elim0 x),fun x=>Fin.elim0 x,by simp,by simp⟩
lemma more(e:Carries X O R a h A K)(g:K≤L):Carries X O R a h A L:=by obtain ⟨i,o,v,t,u,y⟩:=e; exact ⟨i,o,v,t,u.trans g,y⟩
lemma all_s {u:Type}(f:Finset u)(k:u→ℝ)(A:u→ D→FC n)(p:∀ i∈f,Carries X O R a h (A i) (k i)):Carries X O R a h (fun x=> ∑ i∈f,A i x) (∑ i∈f,k i):=by
 classical
 induction f using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact nil_eq
 | @insert i s h ih=> simp only [sum_insert h]; exact (p i (mem_insert_self ..)).add (ih fun i hi=>p i (mem_insert_of_mem hi))
lemma pos_b {x:Capot n Y D}(p:ryde X O R x)(hp:0≤h): 0≤ bill a h R x:= mul_nonneg (mul_nonneg (rent_pos ..).le (pow_nonneg hp _)) p.1.pos
lemma pos(e:Carries X O R a h A K)(p:0≤h):0≤K:=by obtain ⟨i,h,u,q,t,-⟩:=e; exact le_trans (sum_nonneg (fun x _=>pos_b (q x) p)) t
lemma product(e:Carries X O R a h A K)(g:Carries X O R a h B L)(v:R.Nonempty)(t:0≤a)(p:0≤h):Carries X O R a h (A*B) (worth X.k*K*L):=by
 have hq:=g.pos p
 obtain ⟨χ,hx,x,H,q,M⟩:=e; obtain ⟨η,hy,y,U,s,T⟩:=g
 let W:=worth X.k; have hp:0≤W:=lt_of_lt_of_le zero_lt_one (one_w _)|>.le
 let N(i:χ×η):Capot n Y D:= let (J,l,b,w):=x i.1; let (K,j,c,u):=y i.2; (J∪K,l++j,b*c,W*w*u)
 refine ⟨χ×η,inferInstance,N,fun i=>?_, ?_,?_⟩
 · let a:=x i.1; let b:=y i.2; let f:=a.2.2.2; let w:=b.2.2.2; have ha:=H i.1; have hb:= U i.2
   refine ⟨ha.1.twice hb.1 (fun p k=> by obtain ⟨x,hx⟩:=v; exact ⟨x,mem_inter.mpr ⟨(ha.2 p).1 hx,(hb.2 k).1 hx⟩⟩),fun k=> ?_⟩
   change W*f*w≠0 at k; obtain ⟨u,l,f⟩:=ha.2 (right_ne_zero_of_mul (left_ne_zero_of_mul k)); obtain ⟨-,m,d⟩:=hb.2 (right_ne_zero_of_mul k)
   exact ⟨u.trans subset_union_left,(by change Even (a.2.1++b.2.1).length; rw [List.length_append]; exact l.add m),fun x p=>(mem_union.mpr ((List.mem_append.mp p).imp (f x) (d x)))⟩
 · change _ ≤ W*K*L
   calc
     _ ≤ W * ∑ i:χ×η, bill a h R (x i.1)*bill a h R (y i.2):=by
       rw [mul_sum]; apply sum_le_sum; rintro ⟨i,j⟩ _
       let J:=x i; let A:=y j; let P:=J.2.2.2; let Q:=A.2.2.2; have hk:0≤P:=(H i).1.pos; have hx:0≤Q:=(U j).1.pos; change cost a R (J.1∪A.1)*h^(J.2.1++A.2.1).length*(W*P*Q)≤W*(bill _ _ _ J*bill _ _ _ A)
       rw [List.length_append,pow_add]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (cost_join t _ _ _) (by positivity)) (by positivity)) (le_of_eq ?_); unfold bill P Q; ring
     _ ≤ _ := by
       rw [Fintype.sum_prod_type]; simp_rw [←mul_sum,←sum_mul]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul q s (sum_nonneg fun i _=> pos_b (U _) p) ((sum_nonneg (fun i _=>pos_b (H i) p)).trans q)) hp
 intro i; rw [Pi.mul_apply,M,T,sum_mul_sum,Fintype.sum_prod_type]; exact sum_congr rfl fun v p=> sum_congr rfl fun y l=>by rw [valK,valK, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; unfold valK N; simp
lemma identity(t:Grove X.frame R):Carries X O R a h 1 1:=by
 let i:Capot n Y D:=(R,[],(fun _=>1),‖(1:ℂ)‖); have he:ryde X O R i:= ⟨Pro.nonzero R (fun _=>t),fun _=>⟨subset_refl _,⟨0,rfl⟩,by simp [i]⟩⟩; have he':=basic (a:=a) (h:=h) he
 rw [show bill a _ _ i=1 by simp [bill,i,cost,rent]] at he'
 convert he' using 1; ext x s r; simp [valK,i]
end Carries
end YM.CF.Acorn
