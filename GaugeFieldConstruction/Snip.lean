import GaugeFieldConstruction.Seas

/-!
# Finite-dim ballpark prices, rank/open forms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Sailing
open Function Filter Module Metric
open scoped Topology BigOperators
variable {F : Type*} [NontriviallyNormedField F] {A X Y U B : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable {p : Filter A}
lemma excursion {l:A→X→ₗ[F]Y} {q : X→ₗ[F]Y} (h:Dips F p l q) (x:X): Dips F p (fun k=>l k x) (q x) := maps h (LinearMap.applyₗ (R:=F) x) -- check
lemma lived {l:A→ U→X} {q} (h:Dips F p l q) (x:U): Dips F p (fun k=> l k x) (q x):=maps h (LinearMap.proj x)
lemma seen {l : A→F} {v} : Dips F p l v ↔ Tendsto l p (𝓝 v) := by
  constructor; exact fun h=>h LinearMap.id
  intro h g; have he f : g f=f*g 1:= by rw [← smul_eq_mul,← map_smul,smul_eq_mul,mul_one] -- instance
  rw [show (fun k=> g (l k))=fun k=> l k*g 1 from funext fun k=> he (l k),he v]; exact h.mul_const _

variable [FiniteDimensional F X]
-- need only X finite for action
lemma trav {H : A→X→ₗ[F]Y} {h : X→ₗ[F]Y} (u:∀ x:X,Dips F p (fun k=>H k x) (h x)) (x:A→X) (z:X) (w:Dips F p x z): Dips F p (fun i=>H i (x i)) (h z) := by
  let B:=Module.finBasis F X
  let I:=Fin (Module.finrank F X)
  have T (k): Dips F p (fun i => B.coord k (x i) • H i (B k)) (B.coord k z • h (B k)):= chip (u (B k)) (w (B.coord k))
  have e (k:X→ₗ[F]Y) (v : X): ∑ i:I,B.coord i v • k (B i)=k v:= by simp_rw [← map_smul,← map_sum]; rw [show ∑ i:I,B.coord i v • B i=v from B.sum_repr v]
  have E:= gathers Finset.univ (fun i _=> T i)
  rw [e] at E; exact constant E (Eventually.of_forall (fun i=> e _ _))
lemma dots {H:A→ U→X} {v : U→ X} [Fintype U] (h : ∀ i:U,Dips F p (fun k=> H k i) (v i)):Dips F p H v := by
  let P : (U→X) →ₗ[F] (U × (X→ₗ[F]F))→F:= LinearMap.pi fun i=> i.2 ∘ₗ LinearMap.proj i.1
  have hp : Injective P := by
    let B:=Module.finBasis F X
    intro a b e; ext1 i; apply B.equivFun.injective; ext1 j; exact congr_fun e (i,B.coord j)
  exact truth P hp fun i=> h i.1 i.2
lemma dotted {H:A→ X→ₗ[F]Y} {v:X→ₗ[F]Y} [FiniteDimensional F Y] (h : ∀ i:X,Dips F p (fun k=> H k i) (v i)): Dips F p H v:= by
  let P : (X→ₗ[F]Y) →ₗ[F] (X × (Y→ₗ[F] F))→ F:=LinearMap.pi fun i=>i.2 ∘ₗ LinearMap.applyₗ i.1
  have hp : Injective P := by
    let B:=Module.finBasis F Y
    intro a b e; ext1 i; apply B.equivFun.injective; ext1 j; exact congr_fun e (i,B.coord j)
  exact truth P hp fun i=>h i.1 i.2

-- rank lower
lemma venture (g : X→ₗ[F] Y): ∃ U : LinearMap.range g→ₗ[F] X, g ∘ₗ U=(LinearMap.range g).subtype:=by
  obtain ⟨G,hG⟩:= g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict; exact ⟨G,LinearMap.ext fun x=>congr_arg Subtype.val (LinearMap.congr_fun hG x)⟩
variable {P : X→ₗ[F]U→F} {l:A→X→ₗ[F]U→F} (u:Injective P) (v:Scores F p P l) [CompleteSpace F]
lemma ranks (v:Scores F p P l): ∀ᶠ k in p,Module.finrank F (LinearMap.range P) ≤ Module.finrank F (LinearMap.range (l k)):= by
  obtain ⟨L,H⟩:=venture P
  have he i (x:LinearMap.range P) :Tendsto (fun k=>l k (L x) i) p (𝓝 ((P ∘ₗ L) x i)):= v i _
  filter_upwards [(insight (p:=p) (show Injective (P ∘ₗ L) from by rw [H]; exact Subtype.val_injective) (show Scores F p (P ∘ₗ L) (fun k=> l k ∘ₗ L) from fun i x=> he i x)).1] with k hk
  exact LinearMap.finrank_le_finrank_of_injective (f:=(l k).rangeRestrict ∘ₗ L) (fun x y h=> hk (congr_arg Subtype.val h))
variable {L : X→ₗ[F]Y} {f:A→ X→ₗ[F]Y}
variable (h : ∀ x : X,Dips F p (fun k=> f k x) (L x))
include h
lemma ringed (u:Injective L) : (∀ᶠ k in p,Injective (f k)) ∧ ∀ (x:A→X) (z:X), Dips F p (fun k=> f k (x k)) (L z) → Dips F p x z :=by
  let YL : Y→ₗ[F] (Y→ₗ[F] F)→F := LinearMap.pi id
  have he : Injective YL:= by
    intro a b v; by_contra w; obtain ⟨q,T⟩ := Module.Projective.exists_dual_ne_zero F (sub_ne_zero.mpr w)
    exact T ((q.map_sub a b).trans (sub_eq_zero.mpr (congr_fun v q)))
  have Q:=insight (show Injective (YL ∘ₗ L) from he.comp u) (show Scores F p (YL ∘ₗ L) (fun k=>YL ∘ₗ f k) from fun i x=> h x i)
  exact ⟨Q.1.mono fun i h x y p=>h (congr_arg YL p), fun x z h=>Q.2 x z h⟩
lemma sampled : ∀ᶠ k in p,Module.finrank F (LinearMap.range L) ≤ Module.finrank F (LinearMap.range (f k)):= by
  obtain ⟨V,e⟩:=venture L
  filter_upwards [(ringed (f:=fun k=>f k ∘ₗ V) (p:=p) (L:=L ∘ₗ V) (fun x=> h (V x)) (show Injective (L ∘ₗ V) from by rw [e]; exact Subtype.val_injective)).1] with k hk
  exact LinearMap.finrank_le_finrank_of_injective (f:=(f k).rangeRestrict ∘ₗ V) (fun x y h=> hk (congr_arg Subtype.val h))
-- factoring of tests
end YM.GaugeFieldConstruction.Fathom.Sailing
