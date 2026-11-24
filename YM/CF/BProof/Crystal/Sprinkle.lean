import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
/-! Using one decoration per distinct vertex or letter. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Sprinkle
open Function Finset
open scoped BigOperators Classical
variable {V:Type*}[DecidableEq V]{f:V→Type*}[∀ i,Fintype (f i)][∀ i,DecidableEq (f i)]
def Smooth(u:Finset (Sigma f)):=Set.InjOn Sigma.fst (u:Set (Sigma f))
abbrev down (u: Finset (Sigma f)):=u.image Sigma.fst
def Cap(f:V→Type*)[∀ i,Fintype (f i)][∀ i,DecidableEq (f i)] (S:Finset V):= {i: Finset (Sigma f) // Smooth i ∧ down i=S}
abbrev Pick(f:V→Type*) (S:Finset V):=∀ i: ↑S,f i.val
def slip {S:Finset V}(p:Pick f S): (↑S) ↪ Sigma f:= ⟨fun i=>⟨i.val,p i⟩,fun i j h=> Subtype.ext (congrArg Sigma.fst h)⟩
def mater {S:Finset V}(p:Pick f S): Finset (Sigma f):= univ.map (slip p)
lemma smoothM {S:Finset V}(p:Pick f S): Smooth (mater p):=by
 intro i hi j hj u; obtain ⟨a,l,rfl⟩:= mem_map.mp hi; obtain ⟨b,k,rfl⟩:=mem_map.mp hj; rw [show a=b from Subtype.ext u]
lemma downM {S:Finset V}(p:Pick f S): down (mater p)=S:=by ext i; constructor; rintro u; obtain ⟨j,h,rfl⟩:=mem_image.mp u; obtain ⟨a,k,rfl⟩:= mem_map.mp h; exact a.property; intro h; exact mem_image.mpr ⟨slip p ⟨i,h⟩,mem_map_of_mem _ (mem_univ _),rfl⟩
theorem canv (S:Finset V)(u:Finset (Sigma f))(h:Smooth u)(k:down u=S):∃ p: Pick f S, mater p=u:=by
 have he(i:↑S):∃ q:f i.val, Sigma.mk i.val q∈u:=by obtain ⟨⟨x,j⟩,v,hx⟩:= mem_image.mp (show i.val∈down u from k.symm ▸ i.property); change x=i.val at hx; subst x; exact ⟨j,v⟩
 choose p hp using he; refine ⟨p,?_⟩; ext i; constructor; rintro a; obtain ⟨j,b,rfl⟩:=mem_map.mp a; exact hp j; intro e; have he:i.1∈ S:= k ▸ mem_image_of_mem Sigma.fst e; let b:↑S:= ⟨i.1,he⟩; exact mem_map.mpr ⟨b,mem_univ _,h (hp b) e rfl⟩
lemma materInj (S:Finset V): Injective (mater (f:=f) (S:=S)):=by
 intro p q u; funext i; obtain ⟨b,_,h⟩:=mem_map.mp (show slip p i∈mater q from u ▸ mem_map_of_mem (slip p) (mem_univ i)); obtain rfl:b=i:=Subtype.ext (congrArg Sigma.fst h); exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm -- tune
variable [Fintype V]
def span (f:V→Type*)[∀ i,Fintype (f i)][∀ i,DecidableEq (f i)] (S: Finset V): Finset (Finset (Sigma f)):= univ.filter fun i=>Smooth i∧down i=S
lemma mem_span (S:Finset V)(i:Finset (Sigma f)) : i∈span f S↔ Smooth i∧ down i=S:= by simp [span]
lemma beds (f:V→Type*)[∀ i,Fintype (f i)][∀ i,DecidableEq (f i)](S:Finset V): span f S=Finset.univ.map (⟨mater (S:=S), materInj S⟩: Pick f S ↪ Finset (Sigma f)):=by
 ext x; rw [mem_span,mem_map]; constructor; rintro ⟨a,b⟩; obtain ⟨p,e⟩:=canv S x a b; exact ⟨p,mem_univ _,e⟩; rintro ⟨p,e,rfl⟩; exact ⟨smoothM p,downM p⟩
variable {E F:Type*}
lemma sumDown [AddCommMonoid E](G:Finset (Sigma f)→E): (∑ u:Finset (Sigma f), if Smooth u then G u else 0)=∑ i: Finset V,∑ u∈span f i,G u:=by
 simp_rw [span,sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i _; by_cases h:Smooth i; simp [h]; simp [h]
lemma sum_span [AddCommMonoid E](S:Finset V)(G:Finset (Sigma f)→E): (∑ i∈span f S,G i)=∑ i:Pick f S,G (mater i):=by rw [beds,sum_map]; rfl
omit [Fintype V] [∀ i,Fintype (f i)] in -- tune mater included Fintype?
lemma prodSlip [CommMonoid E](S:Finset V)(G:Sigma f→ E)(u:Pick f S) : (∏ i∈mater u,G i)=∏ i:↑S,G (slip u i):=prod_map ..
lemma lifted [CommSemiring E](S:Finset V)(G:Sigma f→ E) : (∏ i∈S, ∑ j:f i,G ⟨i,j⟩)=∑ i∈ span f S, ∏ j∈i,G j:=by
 rw [sum_span]; rw [←Finset.prod_attach S,show S.attach=(univ:Finset ↑S) from rfl]; -- tune wrong sign
 rw [Fintype.prod_sum]; apply sum_congr rfl; intro j _; exact (prodSlip ..).symm
end YM.CF.BProof.Sprinkle
