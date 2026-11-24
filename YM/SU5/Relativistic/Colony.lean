import YM.SU5.FiniteGaugeData.Pannier.Sheds
/-!
# Copy certificate for *baryon*, two-plane marks. Direction sends X to exact Z.

Uses TallPea occupancy idea on sparsely sampled frame points (not all enough for a
pre-poster using fixed compact support near B!), all configurations use one repair.
On clean Broads the extra access allowance u is for projection accuracy only: may be HUGE,
**not counted in the mirror layout and may overlap without consistency** between copies.
Thus it is a question about flags locality; we pay the real flags budget,
not an operator distance to A.broad^c at rate e.

See the construction notes for cost proposal (simplified here: can keep stencil in stampG frame
so approximate Z preserves plus exactly after fixing clamp, use entire Vo's warmed lift).

Analytical modules import this, not vice versa. Aim high σ but contingent upon estimates.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra

variable {I:Type*} [LinearOrder I] [Fintype I]
-- 1+ X Y is handy; 1-product (1-handy) costs from one honored letter per head
abbrev Ring5 := Fin 5
def prime (F:Ring5→FC I):FC I:= 1-(List.ofFn (fun i=> (1:FC I)-F i)).prod
lemma prime_reflect (T:UNI I)(F:Ring5→FC I): theta T (prime F)=prime (fun i=>theta T (F i)):=by
 have he (A B:FC I):theta T (A-B)=theta T A-theta T B:=by
    rw [sub_eq_add_neg,← neg_one_smul ℂ B,theta_add,theta_smul]; simp [sub_eq_add_neg]
 let φ:FC I→* FC I:= ⟨⟨theta T,theta_one _⟩,theta_mul _⟩
 unfold prime; rw [he,theta_one]; apply congrArg (1- ·); change φ (List.ofFn (fun i=>1-F i)).prod= _; rw [map_list_prod,List.map_ofFn]; congr 2; funext a; exact (he 1 _).trans (by rw [theta_one])

variable {n:Side} {j k w d u t:ℕ} {ε E R γ γ' τ:ℝ} {M:Tulip.Male}
variable {A:Cliplet n k}
abbrev hot (A:Cliplet n k)(u:ℕ):= Lattice.halo u A.broad
-- P.sparse is with actual d; Pt lamp covers w+d+1 for **global** wm/tilt.
-- approaches supplied in gauge where FIRST input small. Trim X for each color.
structure Column (j:ℕ)(M:Tulip.Male)(w d u t:ℕ)(γ γ' τ E R:ℝ)(A:Cliplet n k):Prop where
 atCost: AtSupport false A.broad A.frame
 firm: Injective A.birth
 far: Sparse d A.s
 lamp: Lattice.halo (w+d+1) A.s⊆ A.broad
 peak (x:Fields n):∃ (V:Seat n→ SU.E)(X Z:Fin k → Ring5 → Ket (Single n)),
    (A.feel τ t x.1→Rightful A.broad (Lattice.gauge V x.1) 1 γ∧ Rightful (hot A u) (Lattice.gauge V x.1) 1 γ') ∧
    A.frame x=xpert (fun i=>prime (fun c=> handy A.rev (Tset n) (X i c) (Z i c))) ∧
    (∀ i c,A.cargo i (X i c)) ∧ (∀ i c,trim (hand (!A.rev) (cutM (Tset n))) (X i c)) ∧ (∀ i c,‖X i c‖ ≤ 1) ∧
    (∀ i c,withinM (modesIn n A.broad) (Z i c)) ∧ (∀ i c,‖Z i c‖ ≤ R) ∧
    (∀ i c i' c', inner ℂ (X i c) (Z i' c') = if i=i' ∧ c=c' then 1 else 0) ∧
    (∀ i c, let v:= acts (tradew n V).val (Z i c); ‖acts (sp A.rev j M (1:Pane n)) v-v‖ ≤ E)
namespace Column
variable (h:Column j M w d u t γ γ' τ E R A)
include h
lemma enter: A.s⊆ A.broad:= (halo_subset _ _).trans h.lamp
lemma enterAt (i:Fin k): A.birth i∈A.broad:= h.enter (mem_image_of_mem _ (mem_univ _))
lemma rich (p:0<k): A.broad.Nonempty:=⟨_,h.enterAt ⟨0,p⟩⟩
lemma abyss : Distant (w+d) A.s A.broadᶜ:= fun x p y v=> Nat.le_of_not_lt (fun e=> (mem_compl.mp v) (h.lamp (halo_spec.mpr ⟨_,p, e.le.trans (by omega)⟩)))

lemma trace (i:Axis)(s:ℤ)(e:twist (carR i s n) (sp A.rev j M (1:Pane n))=sp (!A.rev) j M (1:Pane n)) : Column j M w d u t γ γ' τ E R (A.mirror i s):=by
 let l:= (plane i s).anon n; let W:=A.mirror i s; let hL:= hyphen (n:=n) i s; have hm(l'): l (l l')=l':= fling_there ..
 have he: W.s=hL A.s:=s_mirror ..; have hw: W.broad=hL A.broad:=rfl; have hr:W.rev= !A.rev:=rfl
 change Column _ _ _ _ _ _ _ _ _ _ _ W
 constructor
 · exact h.atCost.refl i s
 · change Injective (l ∘ A.birth); exact Function.Injective.comp ((show Function.Involutive l from hm).injective) h.firm
 · rw [he]; exact Sparse.reflect h.far i s
 · rw [hw,he]; unfold hL; rw [← coal_halo]; exact image_subset_image h.lamp
 intro x; let x':= reflFields i s x
 obtain ⟨V,X,Z,k',m,f,x₀,x₁,z0,v,g,a⟩:= h.peak x'
 let T:= carR i s n; let U:=acts T.val
 refine ⟨V∘l,fun t c=>U (X t c),fun t c=>U (Z t c),fun p=>?_,?_,fun y c=>?_,fun y c=>?_,fun y c=>?_,fun y c=>?_,fun y c=>?_,fun i' a i'' a'=>?_,fun i' c=>?_⟩
 · have hp:A.feel τ t x'.1:=by
      unfold feel
      apply (Finset.disjoint_image (show Injective l from (show Involutive _ from hm).injective)).1
      change Disjoint (hyphen i s (Lattice.halo t A.broad)) (hyphen i s (flags τ (fling i s n x.1)))
      rw [coal_flags,coal_halo]; exact p
   have hs(D)(p:ℝ)(t:Rightful D (Lattice.gauge V x'.1) 1 p): Rightful (hL D) (Lattice.gauge (V ∘ l) x.1) 1 p:=by
      rw [show Lattice.gauge _ x.1=fling i s n (Lattice.gauge V x'.1) from ?_]; swap
      · rw [show fling i s n (Lattice.gauge V x'.1)=Lattice.gauge (V ∘ l) (fling i s n x'.1) from Nacre.van ..,show fling i s n x'.1=x.1 from fling_invol i s x.1]
      apply Rightful.land; rw [show hyphen i s (hL D)=D from fling_image ..]; exact t
   refine ⟨hs _ _ (k' hp).1,?_⟩; unfold hot; rw [hw]; unfold hL; rw [← coal_halo]; exact hs _ _ (k' hp).2
 · change theta T (A.frame x')= _; rw [m]; unfold xpert
   let φ:FC (Single n)→* FC (Single n):= ⟨⟨theta T,theta_one _⟩,theta_mul _⟩
   change φ (List.ofFn (fun t=>prime (fun c=>handy A.rev (Tset n) (X t c) (Z t c)))).prod=_; rw [map_list_prod,List.map_ofFn]; congr 2; funext b
   apply (show theta T (prime (fun c=> handy A.rev (Tset n) (X b c) (Z b c)))= _ from prime_reflect T _).trans; apply congrArg prime; exact funext (fun c=>fields_r (flatTset i s) (X b c) (Z b c))
 · unfold cargo; change trim (cutM (modesIn n {l (A.birth y)})) _; apply trim_field (_ : twist T (cutM (modesIn n {A.birth y}))=cutM (modesIn n {l (A.birth y)})) (f ..); unfold T; rw [refl_modes,Finset.image_singleton]
 · rw [hr]; exact trim_field (show twist T (hand (!A.rev) (cutM (Tset n)))=hand (!(!A.rev)) (cutM (Tset n)) from handTogether (flatTset ..) _) (x₀ ..)
 · exact (act_unit_norm T _).trans_le (x₁ ..)
 · exact trim_field (refl_modes i s _) (z0 ..)
 · exact (act_unit_norm T _).trans_le (v ..)
 · exact (act_unit_inner T (X i' a) (Z i'' a')).trans (g ..)
 change ‖acts (sp W.rev j M (1:Pane n)) (acts (tradew n (V∘l)).val (acts T.val (Z i' c))) - acts (tradew n (V∘l)).val (acts T.val (Z i' c))‖ ≤ E
 rw [hr, show acts (tradew n (V∘l)).val (acts T.val (Z i' c))=_ from despin i s V (Z i' c),← act_field _ e]; change ‖acts T.val _-acts T.val _‖ ≤ E; rw [← map_sub,act_unit_norm]; exact a i' c
end Column
end YM.CF.Pannier.Chancel.ScreeV
