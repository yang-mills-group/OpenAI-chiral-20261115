import YM.SU5.Relativistic.Colony
import Mathlib.Data.List.ProdSigma
/-!
Adapted Pannier.Emperor. Applies Column costs.
# Representation of disjoint copies with native widths.
not assuming even tiling. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet
open RG
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{k:ℕ}

variable (L:List (Cliplet n k))
variable {j w d u t:ℕ}{γ γ' τ E R:ℝ}{M:Tulip.Male}
structure Company (j:ℕ)(M:Tulip.Male)(w d u t:ℕ)(γ γ' τ E R:ℝ)(L:List (Cliplet n k)) : Prop where
  granted: ∀ A∈L,Column j M w d u t γ γ' τ E R A
  lock : L.Pairwise (fun a b => Disjoint a.broad b.broad)

variable {L} {A:Cliplet n k}
namespace Company
variable (h:Company j M w d u t γ γ' τ E R L)
lemma alone (p:Column j M w d u t γ γ' τ E R (n:=n) (k:=k) A): Company j M w d u t γ γ' τ E R [A]:= ⟨fun a e=> (List.mem_singleton.mp e).symm ▸ p,List.pairwise_singleton _ _⟩ -- tune A implicit
include h
lemma distinct {A B:(Cliplet n k)} (p:A∈ L)(q:B∈ L)(u:A ≠ B): Disjoint A.broad B.broad:= by
 have e:= h.lock; clear h -- proof term?
 induction L with
 | nil=>contradiction -- simp
 | cons C L ih=>
    rcases List.pairwise_cons.mp e with ⟨g,v⟩
    rcases List.mem_cons.mp p with p|p' <;> rcases List.mem_cons.mp q with q|q'
    · exact (u (p.trans q.symm)).elim
    · subst C; exact g _ q'
    · subst C; exact (g _ p').symm
    exact ih p' q' v
lemma permit {D:Finset (Seat n)}(p:whereV L⊆ D): AtSupport false D (probe L):=by
 induction L with
 | nil=>exact AtSupport.oneM D
 | cons A L ih=>
    let W:=(h.granted _ (List.mem_cons_self)).atCost; change A.broad∪whereV L ⊆ D at p
    rw [probe_cons]; exact (W.mono (subset_trans subset_union_left p)).mulM (ih ⟨fun B g=>h.granted B (List.mem_cons_of_mem _ g),(List.pairwise_cons.mp h.lock).2⟩ (subset_trans subset_union_right p))
lemma corsage : AtSupport false (whereV L) (probe L) := h.permit (subset_refl _)
lemma nodup (p:0<k) : L.Nodup:= by
 induction L with
 | nil=>exact List.nodup_nil
 | cons C L ih=>
    obtain ⟨g,v⟩:= List.pairwise_cons.mp h.lock
    refine List.nodup_cons.mpr ⟨fun t=>?_,ih ⟨fun i w=> h.granted _ (List.mem_cons_of_mem _ w),v⟩⟩
    obtain ⟨a,w⟩:=(h.granted _ List.mem_cons_self).rich p; exact disjoint_left.mp (g C t) w w
lemma tack (U:List (Cliplet n k))(q:Company j M w d u t γ γ' τ E R U)(e:Disjoint (whereV L) (whereV U)) : Company j M w d u t γ γ' τ E R (L++U):= ⟨fun a u=>(List.mem_append.mp u).elim (h.granted _) (q.granted _),List.pairwise_append.mpr ⟨h.lock,q.lock,fun i u a v=> e.mono (where_ge _ u) (where_ge _ v)⟩⟩
lemma shorter {U: List (Cliplet n k)} (p:U.Sublist L): Company j M w d u t γ γ' τ E R U:= ⟨fun A w=> h.granted _ (p.mem w), List.Pairwise.sublist p h.lock⟩ -- tune
lemma Corset {A:(Cliplet n k)}(p:A∈L): Distant (w+d) A.s (Stripes L\ A.s):=by
 intro x hx y hy; obtain ⟨ht,hg⟩:= mem_sdiff.mp hy; obtain ⟨i,u,e⟩:= (stripes_at ..).1 ht
 have hx':y∈ i.broad:=(h.granted _ u).enter e
 exact (h.granted _ p).abyss _ hx _ (mem_compl.mpr (fun v=>disjoint_left.mp (h.distinct p u (fun X=> hg (X.symm ▸ e))) v hx'))
lemma meet : Stripes L ⊆ whereV L := fun i (p:i∈ Stripes L) => by obtain ⟨A,w,h'⟩:= (stripes_at ..).1 p; exact where_ge L w ((h.granted A w).enter h')
lemma sparse : Sparse d (Stripes L):=by
 intro i v l w g; obtain ⟨A,u,p⟩:= (stripes_at ..).1 v; by_cases t:l∈ A.s; exact (h.granted _ u).far i p l t g
 exact (h.Corset u i p l (mem_sdiff.mpr ⟨w,t⟩)).trans' (Nat.le_add_left ..)
lemma cloud (i:Axis)(s₀:ℤ)(p:∀ b,twist (carR i s₀ n) (sp b j M (1:Pane n))=sp (!b) j M (1:Pane n)) : Company j M w d u t γ γ' τ E R (L.map (fun a=> a.mirror i s₀)):=by
 constructor
 · intro A z; obtain ⟨a,hp,rfl⟩:=List.mem_map.mp z; exact (h.granted a hp).trace i s₀ (p a.rev)
 apply List.pairwise_map.mpr; exact h.lock.imp (fun {a b} p=> (disjoint_image ((show Involutive _ from fling_there (n:=n) i s₀).injective)).2 p)
end Company
end YM.CF.Pannier.Chancel.ScreeV
