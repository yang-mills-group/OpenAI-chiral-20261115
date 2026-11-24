import YM.SU5.FiniteGaugeData.Mirage.Sheet
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
open SU Scree
variable {S R:Support (More N)}{t:List (Site N)}
inductive Chord (σ τ:Window.Family)(N:Side)(R:Support (More N)): List (Site N) → FC (Single N) → Prop
| unit : Chord σ τ N R [] 1
| zero (t: List (Site N)): Chord σ τ N R t 0
| grow {t:List (Site N)}{A:FC (Single N)} : Chord σ τ N R t A → (i:Site N) → ∀ x∈ capU σ i, ∀ y∈ lumen τ R, Chord σ τ N R (i::t) (A*(put x*takeF y))
| add {t:List (Site N)} {A B:FC (Single N)} : Chord σ τ N R t A→ Chord σ τ N R t B→Chord σ τ N R t (A+B)
| mul {t:List (Site N)}{A:FC (Single N)}: Chord σ τ N R t A→(c:ℂ)→Chord σ τ N R t (c • A)

variable {A B:FC (Single N)} (p:Chord σ τ N R t A)
-- linear envelope, even horizon
noncomputable def harpyM (σ τ:Window.Family)(N:Side)(R:Support (More N))(t:List (Site N)): Submodule ℂ (FC (Single N)) where
 carrier :={A | Chord σ τ N R t A}
 add_mem':= fun {_ _} p q=>Chord.add p q
 zero_mem':= Chord.zero _
 smul_mem':= fun i _ p=> Chord.mul p i
lemma Chord.sum {X:Type*}(Z:Finset X)(f:X→ FC (Single N))(g:∀ i∈ Z,Chord σ τ N R t (f i)):Chord σ τ N R t (∑ i∈Z,f i) := Submodule.sum_mem (harpyM σ τ N R t) g
-- smear lemma: support from within (requires actual exact zero outside grade). Lower officially REMOVE (sign convention insignificant, registered)
lemma Chord.action (i: Site N)(x y:Ket (Single N))(hx: withinM (capU σ i) x)(hy:withinM (lumen τ R) y)(p:Chord σ τ N R t A) : Chord σ τ N R (i::t) (A * (create x* remove y)) := by
 simp only [create_def, remove_def,sum_mul,mul_sum]; refine Chord.sum _ _ fun b _=> Chord.sum _ _ fun a _=>?_
 rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.mul_smul_comm,Algebra.mul_smul_comm]; by_cases h:a∈ capU σ i <;> by_cases g:b∈ lumen τ R
 · exact ((p.grow i a h b g).mul _).mul _
 · rw [(within_test ..).mp hy _ g,star_zero,zero_smul,smul_zero]; exact Chord.zero _
 · rw [(within_test ..).mp hx _ h, zero_smul]; exact Chord.zero _
 rw [(within_test ..).mp hx _ h,zero_smul]; exact Chord.zero _
lemma Chord.fines (g:Chord σ τ N R t A)(p:∀ x∈t,node x∈ S)(q:R⊆S): Reed.Fine (Tset N) (modesIn N S) false A := by
 induction g with
 | unit=> exact .one
 | zero=> exact .empty _
 | @grow t A r i x u y v h=>
    rw [← create_put, ← remove_take]; refine (h (fun x hx=> p x (List.mem_cons_of_mem i hx))).grow ((fine_create _ (within_basis _ _ ?_) (within_basis _ _ ?_)).grow (fine_remove _ (within_basis _ _ ?_) (within_basis _ _ ?_)))
    · exact ((is_cap ..).1 u).1
    · exact (modes_at ..).2 (((is_cap ..).1 u).2.2.symm ▸ p i (List.mem_cons_self ..))
    · exact mem_compl.mpr (((is_lumen ..).1 v).1)
    exact (modes_at ..).2 (q (((is_lumen ..).1 v).2.2))
 | add _ _ a b=>exact (a p).add (b p)
 | mul _ c ih=>exact (ih p).scale c
lemma Chord.wind (g:Site (More N)→SU.E)(p:Chord σ τ N R t A) : Chord σ τ N R t (flipsP g A) := by
 have he {x y:Single N} (p: x.1≠y.1 ∨ family x.2≠ family y.2): shadeP g x y=0 := by
    rw [show shadeP g x y = if x.1=y.1 then (matter (g (node x.1.1))).val x.2 y.2 else 0 from rfl]; split; next t=> exact neq_block _ (p.resolve_left (not_not.mpr t))
    all_goals rfl -- indentation
 have hx {v:Finset (Single N)}(t:∀ i∈v,∀ a:Single N,a.1=i.1→family a.2=family i.2→a∈v)(i:Single N)(p:i∈v) : withinM v (acts (shadeP g) (basisKet i)):= (within_test ..).mpr (fun a w=>by rw [basis_act]; apply he; apply Classical.or_iff_not_imp_left.mpr; intro u; exact fun b=>w (t i p a (not_not.mp u) b))
 have ht (i :Single N):i∈ Tset N ↔ i.1.2∈plusHalf:= grade_one _ _
 induction p with
 | unit=> rw [flips_one]; exact .unit
 | zero=> rw [map_zero]; exact .zero _
 | @grow t A r i x u y v ik=>
    rw [map_mul,map_mul, ← create_put, ← remove_take,flipsP,twist_create,twist_remove]; apply Chord.action _ _ _ (hx _ x u) (hx _ y v) ik
    · intro j v a u c; rw [is_cap,ht]; rw [is_cap,ht] at v; rw [u,c]; exact v -- all changes?
    intro j v a u c; rw [is_lumen,ht]; rw [is_lumen,ht] at v; rw [u,c]; exact v
 | add _ _ a b=>rw [map_add]; exact a.add b
 | mul _ z k=>rw [flipsP,twist_scalar]; exact k.mul _

-- center phase under *local* center Gauge, not trace (diagonal). Specific generator. Port this into result after dressing (& support).
lemma Chord.centerP (i:Site N)(z:node i∉ R)(p:Chord σ τ N R t A): flipsP (lamp i) A= (SU.z^(powerS σ))^(t.count i) • A:=by
 induction p with
 | unit=> rw [flips_one]; simp
 | zero=> simp
 | @grow t A r a x v y u ih=>
    have he: i≠ y.1.1:=fun h=> z (h.symm ▸ ((is_lumen ..).1 u).2.2); rw [map_mul,map_mul,←remove_take,←create_put, show flipsP _ _= _ from twist_create (tradew _ (lamp i)) (basisKet x), show flipsP (lamp i) _=_ from twist_remove (tradew _ (lamp i)) (basisKet y), shade_here y i, shade_here x i, if_neg he, ih]; by_cases p:i=a <;> simp [((is_cap ..).mp v).2.2,((is_cap ..).mp v).2.1,p,Eq.comm (a:=a) (b:=i),pow_succ',smul_smul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
 | add _ _ a b=> rw [map_add,a,b,smul_add]
 | mul _ z t=> change twist _ (z • _) =_; rw [twist_scalar]; rw [show twist _ _= _ from t]; exact smul_comm ..

end YM.CF.Window.Mirage
