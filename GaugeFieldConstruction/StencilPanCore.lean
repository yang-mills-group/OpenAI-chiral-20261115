import GaugeFieldConstruction.StencilWightman
import GaugeFieldConstruction.StencilValise
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
 # At the Station: core arguments. Enlarges operator identification to
 the station's whole sector support even if the radial-carton expression
 is an unbounded-operator on this support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PanSt
open Function Filter MeasureTheory Measure Set Complex Submodule
open YM.Boundary (Test4)
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ComplexConjugate Classical
variable {H: Hilbert}{S: OS.Semigroup H timeAxis}{L V:Type*}
variable {D:Submodule ℂ H}(B:V→ Module.End ℂ D)(R:L→ D)
-- finite linear combination with preexisting star on the docket. Not domain closure on words' topology.
noncomputable abbrev sectorSt := (span ℂ (range (Subtype.val ∘ R))).topologicalClosure
local notation "Q"=> sectorSt R
private lemma coreZeroSt (w:H)(u:w∈ Q)(p:∀ x:L,inner ℂ w (R x).1=0): w=0:=by
 have h:w∈ (Q)ᗮ:=by
    unfold sectorSt; rw[orthogonal_closure]; refine (Submodule.mem_orthogonal' _ _).2 (fun i h=>?_); apply Submodule.span_induction (p:=fun i _=>inner ℂ w i=0) ?_ ?_ ?_ ?_ h
    · rintro i ⟨i,rfl⟩; exact p i
    · simp
    · intro X a _ _ h e; simp only [inner_add_right,h,e,add_zero]
    intro s i t hi; simp [hi,inner_smul_right]
 exact inner_self_eq_zero.mp (inner_left_of_mem_orthogonal u h)
lemma pay_dead_st (h:∀ i:V, ∀ x:D,x.1 ∈ Q→ (B i x).1∈ Q)
 (J:V→V)(j:∀ i:V, ∀ A Y:D,inner ℂ (B i A).val Y.val=inner ℂ A.val (B (J i) Y).val)
 (t: Module.End ℂ D) (p:t∈Submodule.span ℂ (Set.range B)) (e:∀ u:L, t (R u)=0) (x:D)(g:x.1∈ Q): t x=0:=by
 let U:= Submodule.span ℂ (range B)
 let W(t:Module.End ℂ D):Prop:= ∀ x:D,x.1∈ Q → (t x).val∈ Q
 let X(t T:Module.End ℂ D):Prop:= ∀ A B:D,inner ℂ (t A).val B.val=inner ℂ A.val (T B).val
 have he(T: Module.End ℂ D)(u:T∈ U): W T ∧ ∃ J':Module.End ℂ D, J'∈ U ∧ X T J':= by
    apply Submodule.span_induction (p:=fun T _=> W T ∧ ∃ J':Module.End ℂ D, J'∈ U ∧ X T J') ?_ ?_ ?_ ?_ u
    · rintro A ⟨i,h'⟩; subst A; exact ⟨h i, B (J i), Submodule.subset_span (mem_range_self _), j i⟩
    · exact ⟨fun x h=> (Q).zero_mem, 0, U.zero_mem, fun x y=>by simp ⟩
    · rintro A M _ _ ⟨u,J,c,p⟩ ⟨v,K,d,q⟩; exact ⟨fun x h=> (Q).add_mem (u x h) (v x h), J+K,U.add_mem c d, fun x y=>by simp [p x y,q x y, inner_add_left,inner_add_right]⟩
    rintro a A _ ⟨h,T,g,q⟩; exact ⟨fun x u=> (Q).smul_mem _ (h _ u), (Star.star a) • T, U.smul_mem _ g, fun x y=>by simp [inner_smul_left,inner_smul_right,q x y]⟩
 obtain ⟨v,J',a,pJ⟩:= he t p; unfold X at pJ
 have hv(b:L): J' (R b)=0:=by
    apply Subtype.ext
    apply coreZeroSt R _ ((he J' a).1 _ ((span ℂ (range (Subtype.val ∘ R))).le_topologicalClosure (Submodule.subset_span (show (R b).1 ∈ range (Subtype.val ∘ R) from mem_range_self _))))
    intro L; rw [←inner_conj_symm,← pJ,e]; simp
 apply Subtype.ext; apply coreZeroSt R _ (v x g); intro t; rw [pJ, hv]; simp

private lemma touchedSt (g h : E4 → ℂ) (pg : Continuous g) (ph : Continuous h)
    (ht : ∀ f : Test4, (∫ x, f x * g x) = ∫ x, f x * h x) : g = h := by
  refine Measure.eq_of_ae_eq (μ := volume) (ae_eq_of_integral_contDiff_smul_eq
    pg.locallyIntegrable ph.locallyIntegrable ?_) pg ph
  intro f hf hf'
  let t : Test4 := (hf'.comp_left (show Complex.ofReal 0=0 by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hf)
  simpa only [Complex.real_smul, show (t : E4 → ℂ) = (fun x => (f x : ℂ)) from rfl] using ht t

lemma valise_pays_enoughSt (A M:H.Op)(v:H) (h:∀ f:Test4, valise S A f v = valise S M f v): A v=M v:=by
 apply ext_inner_left ℂ; intro z
 let F(q:E4):= inner ℂ z (optx S A q v); let G(q:E4):= inner ℂ z (optx S M q v); have hc:Continuous F:= continuous_const.inner (village S v A); have hc':Continuous G:= continuous_const.inner (village S v _)
 have he': F 0=G 0:= congrFun (touchedSt _ _ hc hc' (fun f=> by rw [show (∫ y,f y*F y)= _ from sell_in S z v _ f, show (∫ y,f y*G y)= _ from sell_in S z v _ f]; exact congrArg (inner ℂ z) (h f))) 0
 unfold F G at he'; rw [vroot,vroot] at he'; exact he'
-- range of common shelf
open NSF.Boundary
variable {D:Submodule ℂ H}
variable {G:NSF.Gauge} {L':NSF.Register G} {A':NSF.Table L'} {W:NSF.Boundary.Surface A'} {R:A'.Rotation}{j:A'.RealSpin}
variable {Row:Sentence A' → D}{T:Letter A' → Module.End ℂ D}
variable (X:Wightman A') (u:WordLiftSt X (H:=H) D Row T)(h:X.Realizes (W:=W) R j)
local notation "W#"=> X.operators
include h u
lemma pocket_span_st : LinearMap.range u.pocket.toLinearMap=span ℂ (range Row):=by
 apply le_antisymm
 · let F:=(W#).vector; rintro x ⟨v,rfl⟩; obtain ⟨v,p⟩:=v; change v∈ (W#).domain at p; rw[h.total.cyclic] at p
   apply Submodule.span_induction (p:=fun v (_:v∈ Submodule.span ℂ (range F))=>∀ x:(W#).domain, x.val=v→ u.pocket x∈ span ℂ (range Row)) ?_ ?_ ?_ ?_ p (⟨v,h.total.cyclic.symm ▸ p⟩:(W#).domain) rfl
   · rintro x ⟨a,rfl⟩ y w; rw [show y=(W#).evaluates a from Subtype.ext w,u.litPage]; exact Submodule.subset_span (mem_range_self ..)
   · intro z p; rw [show z=0 from Subtype.ext p,map_zero]; exact zero_mem _
   · intro i j x y a b w p; let U:=(⟨i,h.total.cyclic.symm ▸ x⟩: (W#).domain); let V:=(⟨j,h.total.cyclic.symm ▸ y⟩: (W#).domain); rw [show w=U+V from Subtype.ext p,map_add]; exact add_mem (a _ rfl) (b _ rfl)
   intro c x y a w p; let U:=(⟨x,h.total.cyclic.symm ▸ y⟩: (W#).domain); rw [show w=c • U from Subtype.ext p,map_smul]; exact smul_mem _ _ (a _ rfl)
 apply Submodule.span_le.mpr; rintro x ⟨v,rfl⟩; exact ⟨_,u.litPage v⟩
lemma ray_closes_st : LinearMap.range u.rays.toLinearMap=((span ℂ (range Row)).map D.subtype).topologicalClosure:=by
 let p:= (W#).domain; have hP: Dense (p:Set X.operators.H):= h.total.everywhere
 let U:=span ℂ (range Row); let Φ:= U.map D.subtype
 have ht(v:(W#).domain):u.pocket v∈ U:= by unfold U; rw [←pocket_span_st X u h]; exact LinearMap.mem_range_self u.pocket.toLinearMap v
 apply le_antisymm
 · rintro y ⟨x,rfl⟩; change u.rays x∈ Φ.topologicalClosure; haveI hx:NeBot (𝓝[↑p] x):= (mem_closure_iff_nhdsWithin_neBot).mp (hP x); apply IsClosed.mem_of_tendsto Φ.isClosed_topologicalClosure (u.rays.continuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:=(p:Set X.operators.H)))); filter_upwards[self_mem_nhdsWithin] with v y; change u.rays v ∈ Φ.topologicalClosure; rw [show u.rays v = (u.pocket ⟨v,y⟩).1 from u.town ⟨v,y⟩]; exact Φ.le_topologicalClosure (Submodule.mem_map_of_mem (ht _))
 · apply Submodule.topologicalClosure_minimal; swap
   · exact u.rays.isometry.isClosedEmbedding.isClosed_range
   rintro y ⟨a,p,rfl⟩; obtain ⟨v,hv⟩:= ((pocket_span_st X u h).symm ▸ p : a∈ LinearMap.range u.pocket.toLinearMap); exact ⟨_,(u.town v).trans (congrArg (fun x:D=>x.val) hv)⟩
#print axioms pay_dead_st
#print axioms valise_pays_enoughSt
#print axioms ray_closes_st
end YM.PanSt
end
