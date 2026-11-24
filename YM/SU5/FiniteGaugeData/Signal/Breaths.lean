import YM.CF.Continuum.Current
import YM.CF.Matter.Mass
import YM.SU5.FiniteGaugeData.Signal.LocalWork
/-!
# Scherzo. Nonzero class is on *actual torus* first-link with SAME selected gen & chiral sector.
 Multiple upper sources permitted; all at nodes OTHER THAN the input apertures T (≥1 lattice space).
 Exactly one removal factor (spin 2) at each NAME (these chosen distinct on the torus).
 -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Scherzo
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Advance Reef Hom Tenant Branch
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator Pointwise ComplexConjugate
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
variable {n m:Side}

abbrev Flavor := Window.Family
def tube (T:Finset (Site n))(l:Flavor)(i: Finset SpinIdx):= (univ : Finset (Single n)).filter fun p=> p.1.1∈T∧p.1.2∈ i ∧ family p.2=l
variable (l: Flavor)(S:Finset (Site n))

def removals (i:Site n): Submodule ℂ (FC (Single n)):= Submodule.span ℂ (Fock.takeF '' (tube {i} l {2}:Set (Single n)))
def arrivals: Submodule ℂ (FC (Single n)):= Submodule.span ℂ (Fock.put '' (tube S l plusHalf:Set (Single n)))
def books (i:Site n): Submodule ℂ (FC (Single n)):= removals l i*arrivals l S

def generous (L:List (Site n)) := (L.map (books l S)).prod
variable {I:Type*}[Fintype I][LinearOrder I]
private lemma within_ℂ_remove (T:Finset I)(x:Ket I)(u:withinM T x): Fock.remove x∈ Submodule.span ℂ (takeF '' (T:Set I)):=by
 rw [remove_def]; refine Submodule.sum_mem _ (fun i _=>?_); by_cases h:i∈T; · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,h,rfl⟩)
 rw [closedCut_iff.mp u i h,star_zero,zero_smul]; exact Submodule.zero_mem _
private lemma within_ℂ_create (T:Finset I)(x:Ket I)(u:withinM T x): create x∈Submodule.span ℂ (Fock.put '' (T:Set I)):=by rw [create_def]; refine Submodule.sum_mem _ (fun i _=>?_); by_cases h:i∈T; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,h,rfl⟩); rw [closedCut_iff.mp u i h, zero_smul]; exact Submodule.zero_mem _

lemma removed_mem {x:Ket (Single n)} {i: Site n} (p: withinM (tube {i} l {2}) x):Fock.remove x ∈ removals l i := within_ℂ_remove _ _ p -- tune
lemma arrival_mem {x:Ket (Single n)} (p: withinM (tube S l plusHalf) x): create x∈arrivals l S:= within_ℂ_create _ _ p
lemma books_l (x:Site n)(q p: Ket (Single n))(a:withinM (tube {x} l {2}) q)(f:withinM (tube S l plusHalf) p): Fock.remove q *create p∈books l S x:= Submodule.mul_mem_mul (removed_mem l a) (arrival_mem l S f)
-- sector helpers
open Reed (Fine)
def slender (S:Finset I)(T:Finset I)(v:Bool):Submodule ℂ (FC I) where
 carrier:={x| Fine S T v x}
 zero_mem':= Fine.empty _
 smul_mem':=fun c x u=> Fine.scale u _
 add_mem':= Fine.add
lemma core_price (i:Site n){T:Support (More n)}(e:node i∈T)(t:∀ i∈S,node i∈T) : books l S i≤ slender (Tset n) (modesIn n T) false:=by
 let W:=Tset n; let V:=modesIn n T; have hu:removals l i≤ slender W V true:= by refine Submodule.span_le.mpr ?_; rintro _ ⟨⟨⟨j,k⟩,x⟩,u,rfl⟩; change (_,x)∈ tube {i} l {2} at u; simp [tube] at u; rcases u with ⟨rfl,rfl,p⟩; rw [←remove_take]; exact fine_remove _ (within_basis _ _ (mem_compl.mpr (fun p=> (by decide: (2:SpinIdx)∉plusHalf) ((mem_Tset ..).1 p)))) (within_basis _ _ ((modes_at ..).2 e))
 have hv :arrivals l S ≤ slender W V true:= by refine Submodule.span_le.mpr ?_; rintro _ ⟨⟨⟨j,k⟩,x⟩,u,rfl⟩; change (((j,k),x):Single n)∈tube S l plusHalf at u; simp only [tube,mem_filter,mem_univ,true_and] at u; rw [←create_put]; exact fine_create _ (within_basis _ _ ((mem_Tset ..).2 u.2.1)) (within_basis _ _ ((modes_at ..).2 (t _ u.1)))
 exact Submodule.mul_le.mpr (fun x p y q=>Fine.grow (show Fine _ _ _ _ from hu p) (show Fine _ _ _ _ from hv q))
lemma fits(L:List (Site n)){T:Support (More n)}(h:∀ i∈S,node i∈T)(t:∀ i∈L,node i∈T): generous l S L≤ slender (Tset n) (modesIn n T) false:=by
 induction L with
 | nil=> exact Submodule.one_le.mpr Reed.Fine.one
 | cons x L ih=> simp only [generous,List.map_cons,List.prod_cons]; exact Submodule.mul_le.mpr fun i p j q=> Fine.grow (show Fine _ _ false i from core_price l S x (t x List.mem_cons_self) h p) (show Fine _ _ false j from ih (fun i v=>t i (List.mem_cons_of_mem _ v)) q)

section rotation
variable (g: Seat n → SU.E)
local notation "T"=>tradew n g
local notation "X" i:max=> twist (quantU (tradew n g)) i
lemma carries (L:Finset SpinIdx){x:Ket (Single n)}(p: withinM (tube S l L) x): withinM (tube S l L) (acts (tradew n g).val x):=by
 apply sectorwiseCut _ p; rintro ⟨i,k⟩ p ⟨j,m⟩ v;
 simp [tube] at p v; by_cases h:j=i; swap; · simp [tradew,jump_apply,h]
 subst j; simp only [tradew,jump_apply,Equiv.refl_apply,if_true]; exact neq_block _ (fun u=> v p.1 p.2.1 (u.trans p.2.2)) -- tune
lemma still (L:Finset SpinIdx){x:Ket (Single n)}(p: withinM (tube S l L) x): withinM (tube S l L) (acts (star (tradew n g).val) x):=by
 apply sectorwiseCut _ p; rintro ⟨i,k⟩ p ⟨j,m⟩ u; rw [Matrix.star_apply]; simp [tube] at p u; by_cases h:i=j; swap; · simp [tradew,jump_apply,h];
 subst i; simp only [tradew,jump_apply,Equiv.refl_apply,if_true]; rw [neq_block (g (node j.1)) (b:=m) (a:=k) (fun e=> u p.1 p.2.1 (e.symm.trans p.2.2)),star_zero]

lemma twist_books (i:Site n){x:FC (Single n)}(h:x∈books l S i): X x∈books l S i:=by
 have hr (x)(p:x∈removals l i) : twist (quantU (tradew n g)) x∈ removals l i:= by
    induction p using Submodule.span_induction with
    | mem x p=> obtain ⟨x,p,rfl⟩:= p; rw [←remove_take,twist_remove]; exact removed_mem l (carries l _ g _ (within_basis _ _ p))
    | zero=> rw [map_zero]; exact Submodule.zero_mem _
    | smul c x p u=> rw [twist_scalar]; exact Submodule.smul_mem _ _ u
    | add c x p u t y=> rw [map_add]; exact Submodule.add_mem _ t y
 have hp(x)(h:x∈arrivals l S) : twist (quantU (tradew n g)) x∈arrivals l S:=by
    induction h using Submodule.span_induction with
    | mem x p=> obtain ⟨x,p,rfl⟩:= p; rw [←create_put,twist_create]; exact arrival_mem l S (carries l S g _ (within_basis _ _ p))
    | zero=> rw [map_zero]; exact Submodule.zero_mem _
    | smul c x p t=> rw [twist_scalar]; exact Submodule.smul_mem _ _ t
    | add c x p u t y=> rw [map_add]; exact Submodule.add_mem _ t y
 unfold books at h ⊢; refine Submodule.mul_induction_on h ?_ ?_
 · intro x p y q; rw [map_mul]; exact Submodule.mul_mem_mul (hr x p) (hp y q)
 intro i j k p; rw [map_add]; exact Submodule.add_mem _ k p
lemma twist_grip (L:List (Site n)){x:FC (Single n)}(p:x∈generous l S L):X x ∈ generous l S L:=by
 induction L generalizing x with
 | nil=> change x∈(1:Submodule ℂ (FC (Single n))) at p; rw [Submodule.one_eq_span, Submodule.mem_span_singleton] at p; obtain ⟨vN,rfl⟩:=p; rw [twist_scalar,map_one]; exact Submodule.smul_mem _ _ (Submodule.one_le.mp (le_refl (1:Submodule ℂ (FC (Single n)))))
 | cons i L ih=> change x∈books l S i * generous l S L at p; change _∈books l S i * generous l S L; exact Submodule.mul_induction_on p (fun b p t q=>by rw [map_mul]; exact Submodule.mul_mem_mul (twist_books l S g i p) (ih q)) (fun i j k p=> by rw [map_add]; exact Submodule.add_mem _ k p)
end rotation
end YM.CF.Signal.Scherzo
