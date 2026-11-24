import GaugeFieldConstruction.Bison
/-!
# U3-multiplier E. Scope. No arbitrary basis shift between sectors. Left-multipliers must commute on same trajectory.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6400
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Empire Fathom Payroll Function Filter Set TopologicalSpace YM.Analysis MeasureTheory Points Bulb Palace Module RawBank Stage Row
open Floor Wick Invoice Gap Sailing
open scoped Topology BigOperators ContDiff
open Phys Flux.One
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
section Left
variable {Y:Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
lemma obtain_one (L:Y→ₗ[ℂ]Module.End ℂ Y) (u:Y) (h:Injective (fun x:Y=> L x u)) (v:∀ x y, Commute (L x) (L y)): ∃! x,L x=1 := by
  have w:=LinearMap.surjective_of_injective (f:=L.flip u) h -- check
  obtain ⟨x,e⟩:= w u; change L x u=u at e
  refine ⟨x,LinearMap.ext (fun y=> ?_),fun z hz=> h ?_⟩
  · obtain ⟨k,rfl⟩:=w y
    change L x (L k u)=_; rw [show L x (L k u)=_ from LinearMap.congr_fun (v x k) u] -- eta
    change L k (L x u)=_; rw [e]; rfl
  exact (show (L z) u = (L x) u from Eq.trans (show L z u=u by rw [show L z=1 from hz]; rfl) e.symm) 
end Left
variable {X : Type*} {ℱ : Filter X} {S : City} {q:X→Carat}
    (H : Blush S ℱ q) {P:Axis→Across} {L : Sheds S P} (C:Supplies L)
local notation "Ls"=> Tot S P L
variable (y:Scope L)
structure Seeing (S : City) (p:Sheds S P) (q:X→Carat) where
  f:X→ Tot S P p≃ₗ[ℂ]Tot S P p
  a:Tot S P p→ₗ[ℂ]Bundle
  inj:Injective a

def Seeing.clears (U:Seeing S L q) (ℱ:Filter X):Prop:=∀ i, Dips ℂ ℱ (fun k=>earning (q k) (U.f k i)) (totalIx (U.a i)).val
private instance ftS: Module.Finite ℂ ↥SymT:= finiteInvariant ..
private instance (p:Sheds S P) : Module.Finite ℂ ↥(Tot S P p):= @FiniteDimensional.finiteDimensional_submodule ℂ SymT _ _ _ _ _
private instance co: AddCommGroup ↥(LinearMap.ker divergence):= @Submodule.addCommGroup ℂ _ _ _ _ _

lemma Blush.promo {S:City} {u:ℕ→Carat} (p:Blush S atTop u) (w:ℕ→ℕ) (h:StrictMono w): Blush S atTop (u ∘ w) where
  pair z b v:=(p.pair z b v).comp h.tendsto_atTop
  trio a b c v h':=(p.trio a b c v h').comp h.tendsto_atTop
  weak:=p.weak.comp h.tendsto_atTop
lemma sweepA (p : Sheds S P) {u : ℕ→Carat} (v:Blush S atTop u): ∃ i : ℕ→ℕ, StrictMono i ∧ ∃ Q : Seeing S p (u ∘ i), Q.clears atTop:= by
  obtain ⟨g,h,j,w,F,H⟩:=priceSweep (fun i=> (earning (u i):Tot S P p→ₗ[ℂ] SymT)) (fun i=>(u i).t.symm.injective.comp Subtype.val_injective)
  have hb x:g x∈ Conserved:= survives (v.promo _ w) (fun i=>F i x) (g x) (H x)
  let q:= supply.symm.toLinearMap ∘ₗ g.codRestrict Conserved hb
  have hu : Injective q:= supply.symm.injective.comp (fun x y E=>h (Subtype.mk.inj E))
  refine ⟨j,w,⟨F,q,hu⟩,fun i=>?_⟩
  change Dips ℂ _ (fun k=> (earning _) (F k i)) (supply (q i)).val
  rw [show supply (q i)=g.codRestrict _ hb i from supply.apply_symm_apply _]; exact H i

-- find relative unit of the limit space from product limit then return to actual
namespace Seeing
variable (U: Seeing S L q) (p: U.clears ℱ)

def cranked (k:X): (Module.End ℂ Ls)→ₗ[ℂ] Module.End ℂ Ls:= ((LinearMap.llcomp ℂ Ls Ls Ls) (U.f k).symm.toLinearMap) ∘ₗ (LinearMap.llcomp ℂ Ls Ls Ls).flip (U.f k).toLinearMap

def link (k:X) : Ls→ₗ[ℂ] Module.End ℂ Ls:= U.cranked k ∘ₗ ((((q k).κ⁻¹^4) • (C.heart y)) ∘ₗ (U.f k).toLinearMap)
lemma quote (k:X) (x r : Ls): link C y U k x r= (U.f k).symm (trade C y (q k) (U.f k x) (U.f k r)) :=rfl
-- naming

def vest : Ls→ₗ[ℂ] SymT := Conserved.subtype ∘ₗ (totalIx ∘ₗ U.a)
lemma own : Injective U.vest:=Subtype.val_injective.comp (supply.injective.comp U.inj)

variable [ℱ.NeBot]
include p H in
lemma multiply (x z:Ls): ∃ w:Ls,U.a x*U.a z=U.a w ∧ Dips ℂ ℱ (fun k=> link C y U k x z) w:=by
  let u k:= U.f k x; let v k:= U.f k z
  let F k :=(earning (q k):Ls→ₗ[ℂ] SymT) ∘ₗ (U.f k).toLinearMap
  have he:= grows U.vest F U.own (fun x=> (show Dips ℂ _ _ _ from p x))
    (fun k=> U.link C y k x z) (totalIx (U.a x * U.a z)).val (show Dips ℂ ℱ (fun k=> F k (link C y U k x z)) (totalIx (U.a x * U.a z)).val from by
      refine constant (beats H C y u v (U.a x) (U.a z) (p x) (p z)) (Eventually.of_forall fun k=>?_); unfold F; simp only [LinearMap.comp_apply]; rw [quote C y]; rw [LinearEquiv.coe_coe, (U.f k).apply_symm_apply])
  obtain ⟨t,h,u⟩:=he; refine ⟨t,supply.injective (Subtype.ext u.symm),h⟩

include p H in
lemma manageable (x:Ls) (u : ∀ z,U.a z*U.a x=U.a z) (z:Ls) : Dips ℂ ℱ (fun k=>link C y U k z x) z :=by
  obtain ⟨t,h,p⟩:= multiply H C y U p z x; rw [u] at h; exact U.inj h ▸ p

lemma version (k:X) (x) (h:Injective (fun v:Ls=> link C y U k v x)): Injective (fun i:Ls=> C.heart y i (U.f k x)):= by
  let Q:= U.f k
  intro a b e
  have H: Q.symm a=Q.symm b:=h (by
    change link C y U k (Q.symm a) x=link C y U k (Q.symm b) x; rw [quote C,quote C]; unfold trade; change Q.symm (_ • ((C.heart y) (Q _) (Q x)))=Q.symm (_ • (C.heart y (Q _) (Q x))); rw [Q.apply_symm_apply,Q.apply_symm_apply,show C.heart y a (Q x)=C.heart y b (Q x) from e])
  exact Q.symm.injective H

lemma ruler (t : Ls) (h:C.heart y t=1) (k:X): let r:=(q k).κ; link C y U k ((U.f k).symm (r^4 • t))=1 := by
  intro r
  apply LinearMap.ext; intro v
  rw [quote C,(U.f k).apply_symm_apply]; unfold trade; rw [map_smul (C.heart _),LinearMap.smul_apply,h,Module.End.one_apply]; change (U.f k).symm ((r⁻¹)^4 • r^4 • _)=_; rw [smul_smul,← mul_pow,inv_mul_cancel₀ (q k).nζ,one_pow,one_smul,(U.f k).symm_apply_apply]; rfl

include H p
lemma paidUnit : ∃ (D : District) (t: Ls), Live D ∧ C.heart y t=1 ∧ (∀ z:Ls,C.heart y z=1→z=t) ∧
    Dips ℂ ℱ (fun k=>earning (q k) ((q k).κ^4 • t)) (totalIx (payment D)).val ∧ ∃ z:Ls,U.a z=payment D := by
  haveI : Nontrivial ↥Ls:= finrank_pos_iff.mp (counts L y).1
  obtain ⟨D,h,x,v,u⟩:= unitS U.a U.inj (fun a b=> by obtain ⟨w,p,_⟩:=multiply H C y U p a b; exact ⟨w,p.symm⟩)
  have R:= ringed (f:=fun k=> (link C y U k).flip x) (p:=ℱ) (L:=LinearMap.id) (fun z => manageable H C y U p x u z) injective_id
  obtain ⟨k,hk⟩:=R.1.exists
  obtain ⟨t,T,hT⟩:= obtain_one (C.heart y) (U.f k x) (version C y U k x hk) (C.compatible y)
  refine ⟨D,t,h,T,hT, ?_,x,v⟩
  let Z k:=(U.f k).symm ((q k).κ^4 • t)
  have ht:Dips ℂ ℱ Z x := R.2 Z x (by
    refine constant (fixed x) (Eventually.of_forall fun k=>?_)
    change x=link C y U k (Z k) x; rw [show link C y U k (Z k)=1 from ruler C y U t T k]; rfl)
  have he:=trav (h:=U.vest) (H:=fun k=> earning (q k) ∘ₗ (U.f k).toLinearMap) (fun x=> p x) Z x ht
  change Dips ℂ _ _ (totalIx (U.a x)).val at he; rw [v] at he
  exact constant he (Eventually.of_forall fun k=> congr_arg (earning (q k)) ((U.f k).apply_symm_apply _))
end Seeing

-- returned E is c-real.
lemma uniform {t: Ls} (p:C.heart y t=1): C.heart y (sbar L t)=1:= by
  apply LinearMap.ext; intro v
  change C.heart y (sbar _ _) v=v; rw [← sbar_twice L v]
  rw [← C.conjugated,p,Module.End.one_apply] -- both occurrences
lemma sincere (t:Ls) (e: C.heart y t=1) (v:∀ t',C.heart y t'=1→ t'=t): sbar L t=t:= v _ (uniform _ _ e)
lemma bit_px (v : District) (h:Live v): payment v≠0 := by
  intro p
  have ht:= congr_arg Prod.fst p
  rcases h with h | ⟨i,h⟩
  · change activates v.g=(0:ℂ) at ht; simp [activates,h] at ht
  have hv:=congr_fun (congr_arg Prod.snd p) i; change activates (v.f i)=0 at hv; simp [activates,h] at hv
#print axioms Seeing.paidUnit
end YM.GaugeFieldConstruction.Ember
