import YM.CF.Urn.Ora
import YM.CF.Urn.Shaft
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I α ι n m: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]
open Stilo Scree Hake
open Pastry
-- matrices grouped by isformal/excit, label bool polarity (creator=true)
variable (b r t:Bool)(U:UNI n)(V:UNI m)
abbrev Ax(n m:Type*):= Bool→Bool→Matrix n m ℂ
abbrev Oak (n:Type*):= Bool→Bool→Bool→Bool→Op n
def mount (A:Ax n m)(i: Twig n)(x:LeanV m): ℂ:=let u:= (twigS i).1; if x.1=u then cSignX u (A (tallC i) u (twigS i).2 x.2) else 0
def soar (B: Oak n)(i j: Twig n):ℂ:=let u:=(twigS i).1; let v:=(twigS j).1; if u=v then 0 else cSignX u (B (tallC i) (tallC j) u v (twigS i).2 (twigS j).2)
abbrev tendA(A F:Ax n m):Prop:=∀ g t,F g (t.xor r)=suburban b U V (A g t)
def playX(B C:Oak n):Prop:=∀ g z t u,t≠u → C g z (t.xor r) (u.xor r)= sings b U (B g z t u)
abbrev hoodY(U:UNI n)(r:Bool)(i j:Twig n):ℂ:=if tallC i=tallC j then sewV U r (twigS i) (twigS j) else 0
def tellX(t:Bool):LeanV n↪ Twig n:=if t then twigExt else twigCab
lemma tellY(t:Bool)(i:LeanV n):tallC (tellX t i)=t ∧ twigS (tellX t i)=i:=by cases t<;> exact ⟨rfl,rfl⟩
lemma tellU(i:Twig n):tellX (tallC i) (twigS i)=i:=by cases i<;>rfl
lemma garden {Y:Type*}[AddCommMonoid Y][DistribMulAction ℂ Y](a:LeanV n)(t:Bool)(F:Twig n→ Y)(hv:∀ s:Twig n, (0:ℂ) • F s=0) : ∑ i:Twig n,hoodY U r (tellX t a) i • F i = ∑ i:LeanV n,sewV U r a i • F (tellX t i) :=by
 rw [←sum_subset (subset_univ ((univ:Finset (LeanV n)).map (tellX t)))]; swap
 · intro i _ v; rw [hoodY,if_neg]; exact hv i; rintro p; exact v ((tellU i) ▸ Finset.mem_map.mpr ⟨_,mem_univ (twigS i),congrArg (fun x:Bool=> tellX x (twigS i)) ((tellY t a).1.symm.trans p)⟩) -- tune
 rw [sum_map]; simp_rw [hoodY]; apply sum_congr rfl; intro i _; rw [(tellY ..).1,(tellY ..).1,if_pos rfl,(tellY ..).2,(tellY ..).2]
lemma trit (F:Twig n→ FC m)(x:Bool)(i:LeanV n): roseB (hoodY U r) F (tellX x i)= roseB (ι:=LeanV n) (sewV U r) (F ∘ tellX x) i:= garden r U i x F fun _=>zero_smul .. -- tune
lemma fallV(t:Bool)(A:Ax n m)(y:n)(b:Bool): lank (mount A) (tellX b (t,y))= ∑ x:m,cSignX t (A b t y x) • wire t x:=by
 rw [lank,Fintype.sum_prod_type,sum_eq_single t]; apply sum_congr rfl; intro i _; simp only [mount,(tellY ..).2,(tellY ..).1,if_true]
 intro i _ p; apply sum_eq_zero; intro j _; simp only [mount,(tellY ..).2,if_neg p,zero_smul]
 simp
lemma lonY (b r:Bool)(U:UNI n)(F:FC (LeanV n))(z:ℂ):lotY b r U (z • F)= cSignX (b.xor r) z • lotY b r U F:=by change sings _ _ _=_; rw [singT,win_c, twist_scalar]; rfl
lemma trimH (A F:Ax n m)(p:tendA b r U V A F)(i:Twig n): lotY b r V (lank (mount A) i)=roseB (hoodY U r) (lank (mount F)) i:=by
 obtain ⟨t,x,j,rfl⟩:∃ t x j,i=tellX t (x,j):=⟨tallC i,(twigS i).1,(twigS i).2,(tellU i).symm⟩
 rw [trit,fallV,map_sum]; unfold roseB; rw [Fintype.sum_prod_type,sum_eq_single (x.xor r)]; swap; · intro a _ v; apply sum_eq_zero; intro j _; unfold sewV; rw [cream,if_neg v,zero_smul]
 swap; simp
 let u:=x.xor r
 have he(j:m):lotY b r V (wire x j)=∑ y:m,(crib V r x).val y j • wire u y:=by rw [show lotY b r V (wire x j)=_ from leafU b r V j x]; apply sum_congr rfl; intro i _; rw [cream]; rw [if_pos rfl]
 simp only [Function.comp_apply,fallV]; have hx(z:n):sewV U r (x,j) (x.xor r,z)=(crib U r x).val z j:=(cream U r x _ _ _).trans (if_pos rfl)
 rw [sum_congr rfl (fun i (_:i∈(univ:Finset m))=> Eq.trans (lonY b r V _ _) (congrArg (fun e:FC (LeanV m)=> cSignX (b.xor r) (cSignX x (A t x j i)) • e) (he i)))]; simp_rw [Finset.smul_sum,smul_smul,hx]; rw [sum_comm]; conv_rhs=>rw [sum_comm]
 apply sum_congr rfl; intro v _; simp_rw [← Finset.sum_smul]; rw [← link_l b r x U V (A t x) (F t u) (p t x) j v] -- tune matrix transpose order
lemma markG(g:Oak n)(v t:Bool)(i j:LeanV n):soar g (tellX t i) (tellX v j)= if i.1=j.1 then 0 else cSignX i.1 (g t v i.1 j.1 i.2 j.2):=by simp only [soar,(tellY ..).1, (tellY ..).2]
lemma taxi (P Q:Oak n)(k:playX b r U P Q)(i j:Twig n):cSignX (b.xor r) (soar P i j)=taxL (hoodY U r) (soar Q) i j:=by
 let F:=hoodY U r
 obtain ⟨t,x,y,rfl⟩:∃ t x j,i=tellX t (x,j):= ⟨_,(twigS i).1,(twigS i).2,(tellU i).symm ⟩; obtain ⟨s,w,j,rfl⟩:∃ t x k,j=tellX t (x,k):= ⟨_,(twigS j).1,(twigS j).2,(tellU j).symm ⟩ -- recursive tune
 let i :=tellX t (x,y); let z:=tellX s (w,j)
 have he(a:Bool)(u:n)(l:Bool)(H:Twig n→ℂ): ∑ i,hoodY U r (tellX l (a,u)) i * H i= ∑ i:n,(crib U r a).val i u * H (tellX l (a.xor r,i)):=by
    change ∑ i: Twig n,(hoodY U r (tellX l (a,u)) i) • H i= _ -- tune
    rw [garden r U (a,u) l H (fun _=>zero_smul ..),Fintype.sum_prod_type,sum_eq_single (a.xor r)]
    · apply sum_congr rfl; intro i _; unfold sewV; rw [cream,if_pos rfl]; rfl
    · intro i _ p; apply sum_eq_zero; intro j _; unfold sewV; rw [cream,if_neg p,zero_smul]
    simp
 unfold taxL; simp_rw [mul_assoc]; simp_rw [←mul_sum]; -- tune
 rw [he x y t (fun l=> ∑ a,hoodY U r _ a*soar Q l a)]
 rw [sum_congr rfl (fun i (_:i∈(univ:Finset n))=> congrArg (fun a:ℂ=> (crib U r x).val i y*a) (he w j s (soar Q ((tellX t) (x.xor r,i)))))]
 simp_rw [markG]
 by_cases h:x=w; · subst w; cases f:b.xor r <;> simp [cSignX]
 have hp: x.xor r ≠ w.xor r:=by cases x <;>cases w <;>cases r<;>first| contradiction| decide
 rw [if_neg h,link_k b r x U w h (P t s x w) _ (k t s x w h)]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [if_neg hp,mul_assoc]
end YM.CF.Urn
