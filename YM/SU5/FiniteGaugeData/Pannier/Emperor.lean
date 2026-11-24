import YM.SU5.FiniteGaugeData.Pannier.PinchGut
import Mathlib.Data.List.ProdSigma
/-!
# Representation of disjoint copies with native widths.
not assuming even tiling. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet
open RG
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{k:ℕ}
namespace Cliplet
variable (L:List (Cliplet n k))
variable {j w d t:ℕ}{γ τ:ℝ}{M:Tulip.Male}
-- footprint unions
def whereV : Finset (Seat n) := L.foldr (fun a b=> a.broad ∪ b) ∅
def Stripes : Finset (Seat n) := L.foldr (fun a b=> a.s∪ b) ∅
def probe : Mark n:= (L.map Cliplet.frame).prod
structure Flight (j:ℕ)(M:Tulip.Male)(w d t:ℕ)(γ τ:ℝ)(L:List (Cliplet n k)) : Prop where
  granted: ∀ A∈L,Perron j M w d t γ τ A
  lock : L.Pairwise (fun a b => Disjoint a.broad b.broad)

@[simp] lemma probe_nil : probe ([]:List (Cliplet n k))=(1:Mark n) := rfl
@[simp] lemma probe_cons (A:(Cliplet n k)) : probe (A::L) = A.frame*probe L:= rfl
lemma probe_at (x:Fields n) : probe L x=(L.map (fun A=> A.frame x)).prod:=by induction L with|nil=>rfl|cons i L ih=> rw [probe_cons,Pi.mul_apply,ih]; rfl
lemma whereV_at (x:Seat n) : x∈whereV L↔∃ A∈L,x∈ A.broad:=by induction L with|nil=> simp [whereV] | cons A L ih=>change x∈A.broad∪whereV L ↔ _; simpa [mem_union,ih,or_and_right,exists_or]
lemma stripes_at (x:Seat n): x∈ Stripes L↔∃ A∈ L,x∈ A.s:=by induction L with|nil=>simp [Stripes]|cons A L ih=> change x∈ A.s∪ Stripes L ↔ _; simpa only [mem_union,ih,List.mem_cons, or_and_right, exists_or, exists_eq_left]
lemma stripes_ge{A:(Cliplet n k)}(p:A∈L): A.s ⊆ Stripes L:= fun _ h=> (stripes_at ..).2 ⟨_,p,h⟩
lemma where_ge{A:(Cliplet n k)}(p:A∈L): A.broad⊆ whereV L:= fun _ h=> (whereV_at ..).2 ⟨_,p,h⟩
lemma combine (L':List (Cliplet n k)):whereV (L++L')=whereV L ∪ whereV L' := by ext; simp [whereV_at,or_and_right,exists_or]
lemma probe_combine(U:List (Cliplet n k)):probe (L++U)=probe L*probe U:=by unfold probe; rw [List.map_append,List.prod_append]
variable {L} {A:Cliplet n k}
namespace Flight
variable (h:Flight j M w d t γ τ L)
lemma alone (p:Perron j M w d t γ τ (n:=n) (k:=k) A): Flight j M w d t γ τ [A]:= ⟨fun a e=> (List.mem_singleton.mp e).symm ▸ p,List.pairwise_singleton _ _⟩ -- tune A implicit
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
    obtain ⟨a,w⟩:=(h.granted _ List.mem_cons_self).broad_pos p; exact disjoint_left.mp (g C t) w w
lemma tack (U:List (Cliplet n k))(q:Flight j M w d t γ τ U)(e:Disjoint (whereV L) (whereV U)) : Flight j M w d t γ τ (L++U):= ⟨fun a u=>(List.mem_append.mp u).elim (h.granted _) (q.granted _),List.pairwise_append.mpr ⟨h.lock,q.lock,fun i u a v=> e.mono (where_ge _ u) (where_ge _ v)⟩⟩
lemma shorter {U: List (Cliplet n k)} (p:U.Sublist L): Flight j M w d t γ τ U:= ⟨fun A w=> h.granted _ (p.mem w), List.Pairwise.sublist p h.lock⟩ -- tune
lemma Corset {A:(Cliplet n k)}(p:A∈L): Distant (w+d) A.s (Stripes L\ A.s):=by
 intro x hx y hy; obtain ⟨ht,hg⟩:= mem_sdiff.mp hy; obtain ⟨i,u,e⟩:= (stripes_at ..).1 ht
 have hx':y∈ i.broad:=(h.granted _ u).enter e
 exact (h.granted _ p).halo_sp _ hx _ (mem_compl.mpr (fun v=>disjoint_left.mp (h.distinct p u (fun X=> hg (X.symm ▸ e))) v hx'))
lemma meet : Stripes L ⊆ whereV L := fun i (p:i∈ Stripes L) => by obtain ⟨A,w,h'⟩:= (stripes_at ..).1 p; exact where_ge L w ((h.granted A w).enter h')
lemma sparse : Sparse d (Stripes L):=by
 intro i v l w g; obtain ⟨A,u,p⟩:= (stripes_at ..).1 v; by_cases t:l∈ A.s; exact (h.granted _ u).far i p l t g
 exact (h.Corset u i p l (mem_sdiff.mpr ⟨w,t⟩)).trans' (Nat.le_add_left ..)
lemma capPrice {R:ℝ} (p:∀ A∈ L,HearthB R (sp A.rev j M (1:Pane n)) A.s) (t':∀ b,IsStarProjection (sp b j M (1:Pane n)))(x:Fields n)(g:0≤R):
    ‖probe L x‖≤ (1+R)^(L.length*k):=by
 induction L with
 | nil=> simp
 | cons A L ih=>
    rw [probe_cons,Pi.mul_apply,List.length_cons, add_comm L.length, Nat.add_mul,one_mul,pow_add]
    exact (norm_mul_le ..).trans (mul_le_mul ((h.granted _ (List.mem_cons_self)).price (p _ List.mem_cons_self) (t' _) x) (ih (h.shorter (by simp)) (fun A w=>p _ (List.mem_cons_of_mem _ w))) (norm_nonneg _) (by positivity))
lemma reflect {R:ℝ} (i:Axis)(s₀:ℤ)(p:∀ b,twist (carR i s₀ n) (sp b j M (1:Pane n))=sp (!b) j M (1:Pane n))(e:∀ (b:Bool)(S:Finset (Seat n)),Sparse d S → HearthB R (sp b j M (1:Pane n)) S): Flight j M w d t γ τ (L.map (fun a=> a.mirror i s₀)):=by
 let f:=fun A:Cliplet n k=> A.mirror i s₀; constructor
 · intro A u; obtain ⟨a,hp,rfl⟩:=List.mem_map.mp u; exact Perron.mirror_p _ _ _ (h.granted a hp) (p a.rev) (e a.rev a.s (h.granted a hp).far).1 -- tune arg order
 apply List.pairwise_map.mpr; exact h.lock.imp (fun {a b} p=> (disjoint_image ((show Involutive _ from fling_there (n:=n) i s₀).injective)).2 p)
omit h
lemma reflect_consistent (L:List (Cliplet n k))(i:Axis)(s₀:ℤ): whereV (L.map (fun a=> a.mirror i s₀))= hyphen i s₀ (whereV L) :=by induction L with|nil=> simp [hyphen,whereV]|cons a L ih=> change (a.mirror i s₀).broad ∪ whereV (L.map (fun a=>a.mirror i s₀)) = Finset.image ((plane i s₀).anon n) (a.broad ∪ whereV L); rw [ih,image_union]; rfl -- syntax
lemma reflect_probes (L:List (Cliplet n k))(i:Axis)(s₀:ℤ): probe (L.map (fun a=> a.mirror i s₀))= reflMark i s₀ (probe L) :=by
 induction L with
 | nil=> exact funext (fun x=> (theta_one _).symm)
 | cons a L ih=>
    rw [List.map_cons,probe_cons,probe_cons,ih]; funext x; unfold reflMark; simp only [Pi.mul_apply,theta_mul]; rfl
end Flight
end Cliplet
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Cliplet.Flight.meet
#print axioms YM.CF.Pannier.Chancel.Cliplet.Flight.reflect
