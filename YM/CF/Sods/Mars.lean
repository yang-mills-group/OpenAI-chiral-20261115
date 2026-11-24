import YM.CF.Kea.Mant
import YM.CF.Mesa.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E F:Type*}[Fintype E][DecidableEq E][DecidableEq F]{f:E→F}
def Bl(f:E→F)(A:Op E): Prop:=∀ i j, f i≠f j → A i j=0
lemma Bl.one : Bl f 1:=fun i j h=>Matrix.one_apply_ne (fun x=> h (x ▸ rfl))
variable {A B:Op E}
lemma Bl.star(p:Bl f A):Bl f (star A):= by intro i j h; simp only [Matrix.star_apply,p j i (Ne.symm h),star_zero]
lemma Bl.mul(p:Bl f A)(q:Bl f B):Bl f (A*B):=by
 intro i j h; rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _; by_cases e:f i=f k
 · rw [q k j (fun x=> h (e.trans x)),mul_zero]
 rw [p i k e,zero_mul]
lemma Bl.pull(p:Bl f A){U:UNI E}(h: Bl f U.val):Bl f (twist U A):=by rw [twist_formula]; exact (h.mul p).mul h.star
lemma Bl.diag (a:E→ℂ):Bl f (Matrix.diagonal a):=fun i j h=> Matrix.diagonal_apply_ne _ (fun p=> h (p ▸ rfl))
abbrev sector (f:E→F)(x:F):= univ.filter fun i=> f i=x
abbrev capH (f:E→F)(x:F):= ↥(sector f x)
lemma inh(i:E) : i∈ sector f (f i):=by simp
lemma road(x:F)(p:capH f x):f p.val=x:=(mem_filter.mp p.property).2
def piece (f:E→F)(x:F)(A:Op E):Op (capH f x):= A.submatrix Subtype.val Subtype.val
lemma piece_p (p: Bl f A)(x:F):piece f x (A*B)=piece f x A * piece f x B:=by
 ext ⟨i,h⟩ ⟨j,b⟩; unfold piece; rw [Matrix.mul_apply,Matrix.submatrix_apply, Matrix.mul_apply]; simp_rw [Matrix.submatrix_apply]; symm; refine Eq.trans (Finset.sum_attach (sector f x) (fun k:E=>A i k* B k j)) ?_
 apply Finset.sum_subset (subset_univ (sector f x)); intro k _ e; rw [p i k (by rw [(show f i=x from road x (⟨i,h⟩:capH f x))]; simpa [sector] using Ne.symm (show f k ≠ x by simpa [sector] using e)), zero_mul]
lemma piece_s(x:F):piece f x (star A)=star (piece f x A):=rfl
lemma piece_d(x:F)(a:E→ℂ):piece f x (Matrix.diagonal a)=Matrix.diagonal fun i:capH f x=> a i.val:=by ext i j; by_cases h:i=j; · simp [piece,h]
                                                                                                     simp [piece,h,(show i.val ≠ j.val from fun p=>h (Subtype.ext p))]
lemma piece_one(x:F): piece f x (1:Op E)=1:=by change piece f _ (Matrix.diagonal _)=_; rw [piece_d]; rfl
lemma BL_ext(p:Bl f A)(q:Bl f B)(h:∀ x:F,piece f x A=piece f x B):A=B:=by
 ext i j; by_cases e:f i=f j; · exact Matrix.ext_iff.mpr (h (f i)) (⟨_,inh i⟩:capH f _) ⟨j,(by simp [sector,e])⟩
 rw [p i j e, q i j e]
lemma wave_ext(U:∀ x:F,Op (capH f x)):∃ A:Op E,Bl f A∧ ∀ x,piece f x A=U x:=by
 classical
 let K(i j:E):ℂ:= if h:f i=f j then U (f i) ⟨i,inh i⟩ ⟨j,(by simp [sector,h])⟩ else 0
 refine ⟨Matrix.of K,fun i j h=> ?_,fun x=>?_⟩; · unfold Matrix.of; change K _ _=_; unfold K; rw [dif_neg h]
 ext ⟨i,g⟩ ⟨j,h⟩; have hi:f i=x:=(mem_filter.mp g).2; subst x; change K i j=_; unfold K; rw [dif_pos (Eq.symm (mem_filter.mp h).2)] -- rw K?
-- spectral decomposition in each block
lemma dozen(p:Bl f A)(h:IsSelfAdjoint A):∃ (U:UNI E)(d:E→ℝ),Bl f U.val ∧ A=spectral U d:=by
 classical
 have hx(x:F):∃ (U:UNI (capH f x))(d:capH f x→ℝ),piece f x A=spectral U d:= spectral_exists _ (show IsSelfAdjoint (piece f x A) from (piece_s (A:=A) (f:=f) x).symm.trans (congrArg (piece f x) h.star_eq))
 choose U d H using hx
 obtain ⟨W,g,V⟩:= wave_ext (f:=f) fun x=>(U x).val
 have ht: W ∈unitary (Op E):=by
   constructor
   · apply BL_ext (g.star.mul g) Bl.one; intro x; rw [piece_p g.star, piece_s, V,piece_one]; exact (U x).property.1
   apply BL_ext (g.mul g.star) Bl.one; intro x; rw [piece_p g,piece_s,V,piece_one]; exact (U x).property.2
 let D:E→ℝ:= fun i=> d (f i) ⟨i,inh i⟩
 refine ⟨⟨W,ht⟩,D,g, BL_ext p ((Bl.diag _).pull g) ?_⟩; intro x; rw [H, spectral,spectral,twist_formula,twist_formula,piece_p (g.mul (Bl.diag _)), piece_p g, piece_s, piece_d]; change _=piece f x W*_ * star (piece f x W); rw [V]; congr 2 -- tune
 congr 1; funext ⟨i,l⟩; have hi:f i=x:=road x (⟨i,l⟩:capH f x); subst x; rfl
end YM.CF.Sods
