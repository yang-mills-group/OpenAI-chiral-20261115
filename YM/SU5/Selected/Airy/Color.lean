import YM.SU5.Selected.Airy.Ride
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
-- Multivariate Palettes. $prefixG$ frequency sign positive. Rθ will combine later. Constrained time signs kept in Color inductive.
variable {d:Type*} [Fintype d]
@[fun_prop] lemma prefix_c (v:d→ℤ) : Continuous (prefixG v):=by unfold prefixG; fun_prop
lemma prefix_add (u v:d→ℤ)(x:Br d): prefixG (u+v) x=prefixG u x*prefixG v x:=by unfold prefixG; simp_rw [Pi.add_apply, fourier_add]; rw [prod_mul_distrib]
lemma prefix_neg (v:d→ℤ)(x:Br d): prefixG (-v) x=star (prefixG v x):=by unfold prefixG; simp_rw [Pi.neg_apply,fourier_neg,star_prod]; rfl
lemma prefix_zero (x:Br d): prefixG (0:d→ℤ) x=1:=by simp [prefixG]
lemma prefix_norm (x:Br d)(v:d→ℤ): ‖prefixG v x‖=1:=by unfold prefixG; rw [norm_prod]; simp only [fourier_apply,Circle.norm_coe,prod_const_one]
lemma tintMono (x:Torch)(t:roundC)(v:FaceL)(i:ℤ): prefixG (Ε v i) (Ε x t)=prefixG v x*fourier i t:= by change (∏ i':Fin (3+1), _)=_; unfold prefixG; rw [Fin.prod_univ_castSucc]; simp [Ε]
private def faces (v:d→ℤ): C(Br d,ℂ):= ⟨prefixG v,prefix_c _⟩
private lemma screws (v:d→ℤ): faces (-v)=star (faces v) := ContinuousMap.ext (fun w=> prefix_neg v w)
open Submodule
-- Stone-Weierstrass on $\prod Br$, keeping radians normalized. From `AddCircle`, extend multi-radian.
lemma stone : (span ℂ (Set.range (faces (d:=d)))).topologicalClosure=⊤:=by
 let S:Subalgebra ℂ C(Br d,ℂ):= Algebra.adjoin _ (Set.range faces)
 let A:StarSubalgebra ℂ C(Br d,ℂ):=
    { toSubalgebra := S
      star_mem':=by change S ≤ star S; refine Algebra.adjoin_le ?_; rintro x ⟨k,rfl⟩; exact Algebra.subset_adjoin (Set.mem_range.mpr ⟨_,screws _⟩) }
 have h:S.toSubmodule= span ℂ (Set.range faces):=by
    apply Algebra.adjoin_eq_span_of_subset; intro x hx; apply Submodule.subset_span
    apply Submonoid.closure_induction (motive:=fun x _=> x∈Set.range faces) (fun i=> id) ⟨0, (ContinuousMap.ext (fun k=> prefix_zero k))⟩ ?_ hx
    rintro _ _ _ _ ⟨v,rfl⟩ ⟨w,rfl⟩; exact ⟨v+w,ContinuousMap.ext (fun i=>prefix_add ..)⟩
 have t: A.SeparatesPoints :=by
    intro x y g; obtain ⟨i,p⟩:= Function.ne_iff.mp g
    classical
    let f:=faces (Pi.single i 1:d→ℤ); refine ⟨_, ⟨f,Algebra.subset_adjoin ⟨_,rfl⟩,rfl⟩,?_⟩
    have h(v:Br d): f v=fourier 1 (v i):=by change (∏ j:d, _)= _; rw [prod_eq_single i]; simp [Pi.single_eq_same]; intro a _ h; rw [Pi.single_eq_of_ne h,fourier_zero]; simp
    intro g; change f x=f y at g; rw [h,h,fourier_one,fourier_one,Subtype.coe_inj] at g; exact p (AddCircle.injective_toCircle piRank.ne' g)
 rw [←h]; exact congrArg (fun S:StarSubalgebra ℂ C(Br d,ℂ)=> S.toSubalgebra.toSubmodule) (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A t)

inductive Color (Q: (d→ℤ)→ Prop): (Br d→ℂ) → Prop where
 | zero:Color Q 0
 | mode(v:d→ℤ):Q v → Color Q (prefixG v)
 | smul(t:ℂ){f} : Color Q f → Color Q (t • f)
 | add {f g}: Color Q f→ Color Q g→ Color Q (f+g)
lemma Color_mono {Q P : (d→ℤ)→Prop}{f}(p:Color Q f)(e:∀ i, Q i→P i):Color P f:=by induction p with
 | zero=>exact .zero
 | mode v q=> exact .mode v (e v q)
 | smul t h ih=>exact ih.smul _ 
 | add _ _ h q=> exact h.add q -- tune dot for Color.smul arg order
abbrev Piece (v:d→ℤ)(u:ℕ):Prop:= ∀ i:d,(v i).natAbs ≤ u
lemma hedge {Q:(d→ℤ)→ Prop}{f:Br d→ℂ}(h:Color Q f) :∀ᶠ n:ℕ in atTop, Color (fun i=> Piece i n∧Q i) f:=by
 induction h with
 | zero=> exact Filter.Eventually.of_forall (fun _=> .zero)
 | mode v p=> exact ((eventually_all).mpr (fun i=>eventually_ge_atTop (v i).natAbs)).mono (fun i e=> .mode v ⟨e,p⟩)
 | smul v p q=> exact q.mono (fun i q=> .smul v q)
 | add p q u v=> exact (u.and v).mono (fun i t=> t.1.add t.2)

def Plasma (Q:(d→ℤ)→Prop)(f:Br d→ℂ): Prop:=∀ e:ℝ,0<e→ ∃ g:Br d→ℂ, Color Q g∧∀ w, ‖f w-g w‖≤ e
lemma fromStone {f:Br d→ℂ}(h:Continuous f): Plasma (fun _=>True) f:=by
 let A:=span ℂ (Set.range (faces (d:=d))); let F:C(Br d,ℂ):=⟨f,h⟩;
 intro e p; obtain ⟨x,h,de⟩:=(Metric.mem_closure_iff (s:=(A:Set C(Br d,ℂ))) (a:=F)).mp (show F∈A.topologicalClosure from (stone (d:=d)).symm ▸ Submodule.mem_top) e p
 refine ⟨x, ?_, fun w=> ((F-x).norm_coe_le_norm w).trans ((dist_eq_norm F x) ▸ de.le)⟩
 change x∈ span ℂ _ at h; refine span_induction ?_ ?_ ?_ ?_ h -- tune
 · rintro f ⟨i,rfl⟩; exact .mode i trivial
 · exact .zero
 · intro a b p q z u; exact z.add u
 intro a b p q; exact q.smul a
lemma Plasma.mono {Q P:(d→ℤ)→Prop}{f : Br d→ℂ}(p: Plasma Q f)(h:∀ i,Q i→ P i): Plasma P f:=by intro e v; obtain ⟨a,p,v⟩:=p _ v; exact ⟨a,Color_mono p h,v⟩
lemma Plasma.add {Q:(d→ℤ)→Prop}{f g:Br d→ℂ}(h:Plasma Q f)(p:Plasma Q g): Plasma Q (f+g):=by
 intro e v; obtain ⟨A,t,w⟩:=h (e/2) (by positivity); obtain ⟨B,b,l⟩:=p (e/2) (by positivity); refine ⟨A+B,t.add b,fun w'=>?_⟩; change ‖f w'+g w'-(A w'+B w')‖ ≤ _; rw [add_sub_add_comm]; apply (norm_add_le ..).trans; linarith [w w',l w']
lemma Plasma.zero {Q:(d→ℤ)→Prop}: Plasma Q (0:Br d→ℂ):=by intro e v; exact ⟨0,Color.zero,fun _=> by simp [v.le]⟩
lemma Plasma.sum {Q:(d→ℤ)→Prop}{ι:Type*}{f:ι→Br d→ℂ}{S:Finset ι}(h:∀ i∈ S,Plasma Q (f i)) : Plasma Q (fun w=>∑ i∈S, f i w) :=by
 classical
 suffices hx:Plasma Q (∑ i∈S,f i) by simpa only [Finset.sum_apply] using! (show Plasma Q (fun w=>(∑i∈S,f i) w) from hx)
 induction S using Finset.induction with| empty=> rw [sum_empty]; exact Plasma.zero|insert i S p v=> rw [sum_insert p]; exact (h i (mem_insert_self ..)).add (v (fun j t=>h j (mem_insert_of_mem t)))
lemma Plaza (f:Torch→ℂ)(h:Continuous f)(i:ℤ): Plasma (fun v:Cover=> v 3=i) (fun w=> fourier i (lapse w) * f (pier w)):=by
 let G(g:Torch→ℂ)(w:Coast):= fourier i (lapse w)*g (pier w)
 have ht (g:Torch→ℂ)(u:Color (fun _=>True) g): Color (fun v:Cover=> v 3=i) (G g):=by
    induction u with
    | zero=> exact (show G 0=0 from (by funext w; unfold G; simp)).symm ▸ Color.zero -- may timeout
    | mode v p => have he:G (prefixG v)=prefixG (Ε v i):= by ext1 w; unfold G; conv_rhs => rw [← to_whole w,tintMono]; rw [mul_comm] ;
                  exact he.symm ▸ .mode _ (by simp)
    | smul s p v=> rw [show G (s •_)=s • G _ from ?_]; exact v.smul _; ext1 w; unfold G; simp; ring -- tune
    | add p s a b=> rw [show G (_+_)=G _+G _ from ?_]; exact a.add b; ext1 w; unfold G; simp [mul_add]
 intro e p; obtain ⟨g,q,k⟩:= fromStone h e p; refine ⟨G g, ht g q, fun w=>?_⟩; unfold G; rw [←mul_sub,norm_mul,fourier_apply,Circle.norm_coe,one_mul]; exact k _
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms stone
#print axioms hedge
#print axioms Plaza
