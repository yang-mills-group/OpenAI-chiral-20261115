import YM.SU5.FiniteGaugeData.Pannier.CaneSugar
/-! # Tops (on cliplets) with one gauge frame, invariant accuracy under repeated Heat reflection. -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open Window (mem_Tset pinLift)
open RG
--
-- ↑ note open directives
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{k:ℕ}
structure Cliplet (n:Side)(k:ℕ) where
 broad: Finset (Seat n)
 birth: Fin k→Seat n
 rev:Bool
 frame:Mark n
namespace Cliplet
variable (A:Cliplet n k)
-- W centers
abbrev s := Finset.univ.image A.birth
abbrev cargo (z:Fin k) (x:Ket (Single n)):Prop:= withinM (modesIn n {A.birth z}) x
lemma cargo_le {i:Fin k}{x:Ket (Single n)}(h:A.cargo i x): withinM (modesIn n A.s) x:= within_more h (modes_monotone (singleton_subset_iff.mpr (mem_image_of_mem _ (mem_univ _))))
-- `Feel`: good declarations patchwise at sensitivity τ (direct input)
def feel (u:ℝ)(t:ℕ)(V:Pane n):Prop:= Disjoint (Lattice.halo t A.broad) (flags (G:=SU.group) u V)
abbrev xpert (X:Fin k→FC (Single n)):= (List.ofFn X).prod
/- `Press`. At ANY fields evaluated vector, A's formula. In actuality choose
   vectors and gauge as continuous functions at a fixed period for initial cliplet;
   not needed here (Envelope paid in its expense).
    d pitch, τ curvature, w width, t trigger for dirty charge. -/
structure Perron (j:ℕ)(M:Tulip.Male)(w d t:ℕ)(γ τ:ℝ)(A:Cliplet n k) : Prop where
 atCost : AtSupport false A.broad A.frame
 firm : Injective A.birth
 far : Sparse d A.s
 lamp : Lattice.halo (w+d+1) A.s⊆ A.broad
 peak (x:Fields n): ∃ (V:Seat n→ SU.E) (X Z:Fin k→ Ket (Single n)),
    (A.feel τ t x.1 → Rightful A.broad (Lattice.gauge V x.1) 1 γ) ∧
    A.frame x=xpert (fun i=> handy A.rev (Tset n) (X i) (Z i)) ∧
    (∀ i, A.cargo i (X i)) ∧ (∀ i, trim (hand (!A.rev) (cutM (Tset n))) (X i)) ∧ (∀ i,‖X i‖=1) ∧
    (∀ i, acts (tradew n V).val (Z i)=sparkUp (sp A.rev j M 1) (modesIn n A.s) (modesIn n A.broad) (acts (tradew n V).val (X i)))
variable {A}{j:ℕ}{M:Tulip.Male}{w d t:ℕ}{γ τ R:ℝ}(h:Perron j M w d t γ τ A)
namespace Perron
include h
lemma enter:A.s ⊆ A.broad:=(halo_subset (w+d+1) _).trans h.lamp
lemma broad_pos (p:0<k):A.broad.Nonempty:=by
 let i:Fin k:= ⟨0,p⟩; exact ⟨A.birth i,h.enter (mem_image_of_mem _ (mem_univ _))⟩
lemma halo_sp : Distant (w+d) A.s (A.broadᶜ):=by
 intro x hx y hy; rw [mem_compl] at hy; exact Nat.le_of_not_lt (fun e=>hy (h.lamp (halo_spec.mpr ⟨x,hx,(Nat.le_of_lt e).trans (by omega)⟩)))
omit h in
lemma peakCost {n: Type*}[LinearOrder n][Fintype n][Nonempty n]{R:ℝ}(T:Finset n)(b:Bool){x y:Ket n}(p: ‖x‖≤1)(u:‖y‖≤R): ‖handy b T x y‖≤1+R:=by
 let X:=creed (!b) x; let d:=cardH b (cutM T) y; let Y:=creed b d; change ‖1+X*Y‖≤_
 have h:‖X‖≤1:=(Flare.cost_pe (!b) x).trans p
 have v:‖Y‖≤R:=(Flare.cost_pe b d).trans ((hand_cost b (cutM_idp _) y).trans u)
 have ht:‖(1:FC n)‖=1:=by simp
 exact (norm_add_le _ _).trans (add_le_add ht.le ((norm_mul_le X Y).trans ((mul_le_of_le_one_left (norm_nonneg Y) h).trans v)))
lemma price (g:HearthB R (sp A.rev j M (1:Pane n)) A.s)(p:IsStarProjection (sp A.rev j M (1:Pane n)))(x:Fields n): ‖A.frame x‖≤(1+R)^k:=by
 obtain ⟨V,X,Z,_,q,_,_,e,u⟩:= h.peak x
 let F(i:Fin k):=handy A.rev (Tset n) (X i) (Z i); let R':=1+R; have hp(i:Fin k): ‖F i‖≤R':=by
    apply peakCost _ _ (e i).le; rw [← act_unit_norm (tradew n V) (Z i),u i]; exact (shore_cost (cutM_idp _) _).trans (warm_cost _ p g.2 ((act_unit_norm _ _).trans (e i)).le)
 have hu: 0≤ R':= add_nonneg zero_le_one ((norm_nonneg _).trans g.2)
 rw [q]; change ‖(List.ofFn F).prod‖≤ _; rw [show List.ofFn F=(List.ofFn id).map F from (by rw [List.map_ofFn]; rfl)]; have hR:= expCost F _ hp hu (List.ofFn id); rw [List.length_ofFn] at hR; exact hR -- tune List
where expCost(f:Fin k→FC (Single n))(r:ℝ)(t:∀ i,‖f i‖≤r)(h:0≤r)(L:List (Fin k)):‖(L.map f).prod‖≤r^L.length:=by
        induction L with|nil=> simp|cons i L ih=> simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (t _) ih (norm_nonneg _) h)
end Perron
variable (i:Axis)(s₀:ℤ)(A)
def mirror :Cliplet n k:=⟨hyphen i s₀ A.broad, (plane i s₀).anon n ∘ A.birth,!A.rev,reflMark i s₀ A.frame⟩
lemma s_mirror : (A.mirror i s₀).s = hyphen i s₀ A.s:= by unfold hyphen Cliplet.s mirror; dsimp; rw [image_image]
lemma Perron.mirror_p (f:Perron j M w d t γ τ A)
    (e:twist (carR i s₀ n) (sp A.rev j M (1:Pane n))= sp (!A.rev) j M (1:Pane n))
    (g:IsUnit (Fock.padded (modesIn n A.s) (sp A.rev j M (1:Pane n)))) : Perron j M w d t γ τ (A.mirror i s₀):=by
 let l:= (plane i s₀).anon n; let W:=A.mirror i s₀; let hL:= hyphen (n:=n) i s₀; have hm(l'): l (l l')=l':= fling_there ..
 have he: W.s=hL A.s:=s_mirror ..; have hw: W.broad=hL A.broad:=rfl; have hr:W.rev= !A.rev:=rfl; change Perron _ _ _ _ _ _ _ W
 constructor
 · exact f.atCost.refl i s₀
 · change Injective (l ∘ A.birth); exact Function.Injective.comp ((show Function.Involutive l from hm).injective) f.firm
 · rw [he]; exact Sparse.reflect f.far i s₀
 · rw [hw,he]; unfold hL; rw [← coal_halo]; exact image_subset_image f.lamp
 intro x; let x':= reflFields i s₀ x
 obtain ⟨V,X,Z,u,p,h,q,g',f'⟩:= f.peak x'
 let T:= carR i s₀ n; let U:=acts T.val; let B:=V∘l; refine ⟨B,U ∘ X,U ∘ Z,fun ht=>?_,?_,fun y=>?_,fun a=>?_,fun i=>?_,fun a=>?_⟩
 · have hp:A.feel τ t x'.1:=by
      unfold feel
      apply (Finset.disjoint_image (show Injective l from (show Involutive _ from hm).injective)).1
      -- need unfold feel? tune
      change Disjoint (hyphen i s₀ (Lattice.halo t A.broad)) (hyphen i s₀ (flags τ (fling i s₀ n x.1)))
      rw [coal_flags,coal_halo]; exact ht
   have h'': Lattice.gauge B x.1=fling i s₀ n (Lattice.gauge V x'.1):=by
      rw [show fling i s₀ n (Lattice.gauge V x'.1)=Lattice.gauge B (fling i s₀ n x'.1) from Nacre.van ..,show fling i s₀ n x'.1=x.1 from fling_invol i s₀ x.1]
   rw [h'']; apply Rightful.land; rw [hw]; unfold hL hyphen; rw [show _= _ from fling_image i s₀ A.broad]; exact u hp
 · change theta T (A.frame x')= _; rw [p]; change theta T (xpert fun a=> _)=_; unfold xpert
   let φ:FC (Single n)→* FC (Single n):= ⟨⟨theta T,theta_one _⟩,theta_mul _⟩
   -- `have` doesn't reduce
   change φ (List.ofFn (fun i=>handy A.rev (Tset n) (X i) (Z i))).prod= _; rw [map_list_prod,List.map_ofFn]; congr 2; funext a; exact fields_r (flatTset i s₀) (X a) (Z a)
 · have ht: W.birth y=l (A.birth y):=rfl; unfold cargo; rw [ht]; exact trim_field (show twist T (cutM (modesIn n {A.birth y}))=cutM (modesIn n {l (A.birth y)}) from (by rw [show T= carR i s₀ n from rfl]; rw [refl_modes,Finset.image_singleton])) (h y)
 · rw [hr]; exact trim_field (show twist T (hand (!A.rev) (cutM (Tset n)))=hand (!(!A.rev)) (cutM (Tset n)) from handTogether (flatTset ..) _) (q _)
 · exact (act_unit_norm T _).trans (g' _)
 change acts (tradew n (V ∘ l)).val (acts T.val (Z a))= sparkUp (sp W.rev j M (1:Pane n)) (modesIn n W.s) (modesIn n W.broad) (acts (tradew n (V ∘ l)).val (acts T.val (X a)))
 rw [hr,hw,he]; unfold T l; rw [despin i s₀ V,despin,f' a]; exact sparkOn e (refl_modes ..) (refl_modes ..) g _
end Cliplet
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Cliplet.Perron.mirror_p
