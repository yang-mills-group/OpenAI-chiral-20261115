import YM.CF.Rel.Drop
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
def fillSpot (d:DialT n m)(i:Fin (m+1)): Site n:=Fin.cases 0 d i
def colorB (x:InputZ G n)(p: Body 2 n)(b:G.ColorIndex):ℂ:=((sumH G x p) b:ℝ)
def oct(p:CurRun (m+1))(x:InputZ G n)(b:SpotG G (m+1))(d:DialT n m)(v:Site n):=∏ i, colorB x (fillSpot d i+v,p i) (b i)
lemma oath(p:CurRun (m+1))(x:InputZ G n)(b:SpotG G (m+1))(d:DialT n m)(v:Site n): oct p (te x v) b d 0=oct p x b d v:=by unfold oct colorB; simp_rw [add_zero,sumHt]
-- line sum closed
lemma apart_l (x:InputZ G n)(v:Site n)(b:TypeFace 3)(j:G.ColorIndex): (∑ c:TypeFace 2, ∑ a:Axis,left ℂ 2 a b c*(colorB x (v+Lattice.step a,c) j-colorB x (v,c) j))=0:=by
 let y:=fun b:Body 2 n=> (sumH G x b j)
 have hh:y=Matrix.mulVec (Exterior.d 1 n) (parts G 1 x j):=rfl
 have ht:Matrix.mulVec (Exterior.d 2 n) y (v,b)=0:=by rw [hh,Matrix.mulVec_mulVec, Exterior.closed, Matrix.zero_mulVec]; rfl
 rw [discrete] at ht
 have hu:=congr_arg ((↑):ℝ→ℂ) ht; rw [Complex.ofReal_sum,Complex.ofReal_zero] at hu; rw [←hu,sum_comm (s:= (univ:Finset (TypeFace 2)))]; refine sum_congr rfl fun a _=>?_ ; unfold left; simp only [Matrix.of_apply]; split
 next hp=>
    simp_rw [ite_mul,zero_mul]; rw [sum_ite_eq,if_pos (mem_univ _)]; simp only [Complex.ofReal_mul,Complex.ofReal_sub,parity,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]; rfl
 next h=> simp
section slide
variable (X:Shed (Keys m) (m+1)) (i:Fin (m+1))(p:CurRun (m+1))(x:InputZ G n)(s:SpotG G (m+1))(d:DialT n m)(b:TypeFace 3)(a:Axis)
abbrev B : ℂ:= Ca (fun y=> X y b p) d
-- differentiate in p variable: reduce internal endpoint to null
abbrev ends (p:CurRun (m+1))(x:InputZ G n)(s:SpotG G (m+1))(d:DialT n m)(i:Fin (m+1)) (a:Axis):= oct p x s (d+reedU i a) (if i=0 then Lattice.step a else 0)
private def hat:= ∏ j∈(univ.erase i), colorB x (fillSpot d j,p j) (s j)
lemma pas : oct p x s d 0= colorB x (fillSpot d i,p i) (s i)*hat i p x s d:=by unfold oct hat; simp only [add_zero]; exact (Finset.mul_prod_erase _ _ (mem_univ i)).symm
lemma upperX (j:Fin (m+1)): fillSpot (d+reedU i a) j+(if i=0 then Lattice.step a else 0)=fillSpot d j+(if i=j then Lattice.step a else 0):=by
 revert j; induction i using Fin.cases with
 | zero=> intro j; induction j using Fin.cases <;>simp [fillSpot,reedU] <;> intro hi <;> exact False.elim (Fin.succ_ne_zero _ hi.symm)
 | succ l=> intro j; induction j using Fin.cases with
            | zero=>simp [fillSpot]
            | succ h=>by_cases hh:h=l <;> simp [fillSpot,reedU,Pi.single_apply, *,Ne.symm]
lemma held : ends p x s d i a=colorB x (fillSpot d i+Lattice.step a,p i) (s i)*hat i p x s d:=by
 unfold ends oct; simp_rw [upperX]; rw [← Finset.mul_prod_erase _ (f:=fun j=> colorB x (fillSpot d j+(if i=j then Lattice.step a else 0),p j) (s j)) (mem_univ i)]; rw [if_pos rfl]; congr 1; refine prod_congr rfl fun j hj=>?_ ; have ht:= (mem_erase.mp hj).1; rw [if_neg ht.symm,add_zero]
lemma sameT (c:TypeFace 2): hat i (Function.update p i c) x s d=hat i p x s d:=prod_congr rfl fun j hj=> by rw [Function.update_of_ne (mem_erase.mp hj).1]
private lemma many {t:ℕ} {α:Type} [DecidableEq α] (j:Fin t) (f:(Fin t→α)→ℂ)[Fintype α]{u:α} (hp:∀ p:Fin t→α,p j=u→(∑ k:α,f (Function.update p j k))=0): (∑ p: Fin t→α,f p)=0:=by -- α undecl. use redundant |α|
 let R:ℂ:= Fintype.card α; have ht: ∑ p: Fin t→α,∑ k:α, f (Function.update p j k)=0:= sum_eq_zero fun p _=>by have he:=hp (Function.update p j u) (Function.update_self ..); simpa using he
 have he : R*∑ p:Fin t→α,f p=∑ p: Fin t→α, ∑ k:α,f (Function.update p j k):=by
    let V: (Fin t→α) × α≃ (Fin t→α)×α:={ toFun:=fun a=>(Function.update a.1 j a.2,a.1 j),invFun:=fun a=>(Function.update a.1 j a.2,a.1 j),left_inv:=fun i=>by simp,right_inv:=fun i=>by simp }
    have h:=Equiv.sum_comp V (fun a=> f a.1); unfold V at h; simp [Fintype.sum_prod_type, ←mul_sum] at h; rw [h]
 apply (mul_eq_zero.mp (he.trans ht)).resolve_left; have hx: Nonempty α:=⟨u⟩; unfold R; exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
lemma shine (hp:Paddle i X): (∑ p:CurRun (m+1), ∑ a:Axis,left ℂ 2 a b (p i)*B X p d b * (ends p x s d i a-oct p x s d 0))=0:=by
 refine many (u:= (plaquette ⟨(0,1),by decide⟩)) i _ ?_; intro p _;
 have ht(k:TypeFace 2): B X (Function.update p i k) d b=B X p d b:=by unfold B; exact cac _ _ _ (fun x=> hp _ _ _ _)
 simp_rw [pas (i:=i),held, sameT,Function.update_self,ht,← sub_mul]; have he:= apart_l x (fillSpot d i) b (s i); calc
    _= B X p d b*(∑ c:TypeFace 2,∑ a:Axis,left ℂ 2 a b c*(colorB x (fillSpot d i+Lattice.step a,c) (s i)-colorB x (fillSpot d i,c) (s i)))*hat i p x s d:=by simp_rw [mul_sum,sum_mul]; refine sum_congr rfl fun c _=>sum_congr rfl fun a _=>?_ ; ring
    _ = _:= by rw [he,mul_zero,zero_mul]
end slide
end YM.CF.Rel
