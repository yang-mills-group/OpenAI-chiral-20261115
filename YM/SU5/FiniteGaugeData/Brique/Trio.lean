import YM.SU5.FiniteGaugeData.Brique.Visit
import YM.CF.Continuum.Current
import YM.CF.Matter.Mass
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Spire Tenant Fock Fock.Brique Tulip Dial Fir Buffered Skye
attribute [local instance] opCStarAlgebra
variable {N:Side} {σ : Window.Family} {S R : Support (More N)} {t:List (Site N)} {k:ℕ}
/- One left handed species with native separation stencil. R in gauge sites reserved for removals; t in matter sites reserved for creations (list, one at each site in t exactly). Permit all spin/colors in that gradation (Tset = exactly Upper). No coinciding z with R to be claimed on observables. Gauge-covariance PLUS this excludes product states. -/
def classOf (σ:Window.Family)(N:Side): Finset (Single N):= univ.filter fun i=> i.2∈ colors σ
lemma in_class (σ:Window.Family)(i:Single N) : i∈classOf σ N ↔ family i.2=σ:=by simp [classOf,colors]
def capU (σ:Window.Family)(x:Site N): Finset (Single N):=Tset N ∩ (classOf σ N ∩ atSites {x})
lemma is_cap (x:Site N)(a:Single N): a∈capU σ x ↔ a∈Tset N ∧ family a.2=σ ∧ a.1.1=x:=by simp [capU,in_class]
def lumen (σ:Window.Family)(R:Support (More N)):= (Tset N)ᶜ ∩ (classOf σ N ∩ modesIn N R)
lemma is_lumen (R:Support (More N))(a:Single N) : a∈lumen σ R ↔ a∉Tset N ∧ family a.2=σ ∧ node a.1.1∈R:=by simp [lumen,in_class]
inductive Trio (σ:Window.Family)(N:Side)(R:Support (More N)): List (Site N) → FC (Single N) → Prop
| unit : Trio σ N R [] 1
| zero (t: List (Site N)): Trio σ N R t 0
| grow {t:List (Site N)}{A:FC (Single N)} : Trio σ N R t A → (i:Site N) → ∀ x∈ capU σ i, ∀ y∈ lumen σ R, Trio σ N R (i::t) (A*(put x*takeF y))
| add {t:List (Site N)} {A B:FC (Single N)} : Trio σ N R t A→ Trio σ N R t B→Trio σ N R t (A+B)
| mul {t:List (Site N)}{A:FC (Single N)}: Trio σ N R t A→(c:ℂ)→Trio σ N R t (c • A)
local notation "Κ" => FC (Single N)
variable {A B:FC (Single N)} (p:Trio σ N R t A)
-- linear envelope, even horizon
noncomputable def syllabus (σ:Window.Family)(N:Side)(R:Support (More N))(t:List (Site N)): Submodule ℂ (FC (Single N)) where
 carrier :={A | Trio σ N R t A}
 add_mem':= fun {_ _} p q=>Trio.add p q
 zero_mem':= Trio.zero _
 smul_mem':= fun i _ p=> Trio.mul p i
lemma Trio.sum {X:Type*}(Z:Finset X)(f:X→ FC (Single N))(g:∀ i∈ Z,Trio σ N R t (f i)):Trio σ N R t (∑ i∈Z,f i) := Submodule.sum_mem (syllabus σ N R t) g
-- smear lemma: support from within (requires actual exact zero outside grade). Lower officially REMOVE (sign convention insignificant, registered)
lemma Trio.action (i: Site N)(x y:Ket (Single N))(hx: withinM (capU σ i) x)(hy:withinM (lumen σ R) y)(p:Trio σ N R t A) : Trio σ N R (i::t) (A * (create x* remove y)) := by
 simp only [create_def, remove_def,sum_mul,mul_sum]; refine Trio.sum _ _ fun b _=> Trio.sum _ _ fun a _=>?_
 rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.mul_smul_comm,Algebra.mul_smul_comm]; by_cases h:a∈ capU σ i <;> by_cases g:b∈ lumen σ R
 · exact ((p.grow i a h b g).mul _).mul _
 · rw [(within_test ..).mp hy _ g,star_zero,zero_smul,smul_zero]; exact Trio.zero _
 · rw [(within_test ..).mp hx _ h, zero_smul]; exact Trio.zero _
 rw [(within_test ..).mp hx _ h,zero_smul]; exact Trio.zero _
lemma Trio.fines (g:Trio σ N R t A)(p:∀ x∈t,node x∈ S)(q:R⊆S): Reed.Fine (Tset N) (modesIn N S) false A := by
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
lemma homes_cash (S T:Support (More N)){F: FC (Single N)}(p:Reed.Fine (Tset N) (modesIn N S) false F)(q:S⊆T):Reed.Fine (Tset N) (modesIn N T) false F:= fine_enlarge (modes_monotone q) p
-- Individual markers can be transported even if their chosen orientation is not gauge-covariant. (linear span will remain this payload)
abbrev shadeP (g:Seat N→SU.E): Op (Single N) := (tradew N g).val
abbrev flipsP (g:Seat N→SU.E) := twist (quantU (tradew N g))
variable (g:Seat N→SU.E)
private lemma shade_k (x y:Single N): shadeP g x y= if x.1=y.1 then (matter (g (node x.1.1))).val x.2 y.2 else 0:=rfl
lemma grade_one {x : Site N}(i:SpinIdx)(b:SU.Slot):((x,i),b)∈ Tset N ↔ i∈ plusHalf:= mem_Tset x i b -- y unused; rm
lemma flips_one : flipsP g (1:Κ)=1:=by rw [flipsP,twist_formula,mul_one]; exact (quantU (tradew N g)).property.2
lemma Trio.wind (p:Trio σ N R t A) : Trio σ N R t (flipsP g A) := by
 have he {x y:Single N} (p: x.1≠y.1 ∨ family x.2≠ family y.2): shadeP g x y=0 := by
    rw [shade_k]; split; next t=> exact neq_block _ (p.resolve_left (not_not.mpr t))
    all_goals rfl -- indentation
 have hx {v:Finset (Single N)}(t:∀ i∈v,∀ a:Single N,a.1=i.1→family a.2=family i.2→a∈v)(i:Single N)(p:i∈v) : withinM v (acts (shadeP g) (basisKet i)):= (within_test ..).mpr (fun a w=>by rw [basis_act]; apply he; apply Classical.or_iff_not_imp_left.mpr; intro u; exact fun b=>w (t i p a (not_not.mp u) b))
 have ht (i :Single N):i∈ Tset N ↔ i.1.2∈plusHalf:= grade_one _ _
 induction p with
 | unit=> rw [flips_one]; exact .unit
 | zero=> rw [map_zero]; exact .zero _
 | @grow t A r i x u y v ik=>
    rw [map_mul,map_mul, ← create_put, ← remove_take,flipsP,twist_create,twist_remove]; apply Trio.action _ _ _ (hx _ x u) (hx _ y v) ik
    · intro j v a u c; rw [is_cap,ht]; rw [is_cap,ht] at v; rw [u,c]; exact v -- all changes?
    intro j v a u c; rw [is_lumen,ht]; rw [is_lumen,ht] at v; rw [u,c]; exact v
 | add _ _ a b=>rw [map_add]; exact a.add b
 | mul _ z k=>rw [flipsP,twist_scalar]; exact k.mul _

-- center phase under *local* center Gauge, not trace (diagonal). Specific generator. Port this into result after dressing (& support).
def powerS (σ:Window.Family): ℕ:= if σ.2 then 2 else 4
lemma central_eigen (i:Single N) : SU.charge i.2=powerS (family i.2):= by
 unfold family powerS SU.charge; cases i.2.2 <;> rfl
noncomputable abbrev lamp (i: Site N): Seat N→SU.E:= Function.update 1 (node i) SU.central
lemma shade_here (x:Single N)(i:Site N) : acts (shadeP (lamp i)) (basisKet x)=if i=x.1.1 then SU.z^(powerS (family x.2)) • basisKet x else basisKet x :=by
 apply PiLp.ext; intro y; rw [basis_act,shade_k]; by_cases h:y.1=x.1; swap
 · rw [if_neg h]; split <;> simp [(show y≠x from fun p=> h (congrArg Prod.fst p))]
 let g:= lamp i; rw [if_pos h,h]; change (matter (g (node x.1.1))).val y.2 x.2=_; by_cases p:i=x.1.1;
 · rw [if_pos p]; unfold g; rw [lamp,p,update_self, SU.by_charge,Matrix.diagonal_apply]; rw [central_eigen y]; by_cases e:y.2=x.2
   · have he:= Prod.ext h e; rw [show y=x from he]; simp
   simp [e,(show y≠x from fun v=> e (congrArg Prod.snd v))]
 rw [if_neg p,show g (node x.1.1)=1 from update_of_ne (Tenant.needle.ne (Ne.symm p)) .., map_one, show ((1:UNI SU.Slot)).val= _ from rfl]; change (1: Op SU.Slot) _ _=_; by_cases e:y.2=x.2
 · have he:= Prod.ext h e; rw [show y=x from he]; simp
 simp [e,(show y≠x from fun v=> e (congrArg Prod.snd v))]
local notation "Λ" => SU.z^(powerS σ)
lemma Trio.centerP (i:Site N)(z:node i∉ R)(p:Trio σ N R t A): flipsP (lamp i) A= (SU.z^(powerS σ))^(t.count i) • A:=by
 induction p with
 | unit=> rw [flips_one]; simp
 | zero=> simp
 | @grow t A r a x v y u ih=>
    have he: i≠ y.1.1:=fun h=> z (h.symm ▸ ((is_lumen ..).1 u).2.2); rw [map_mul,map_mul,←remove_take,←create_put, show flipsP _ _= _ from twist_create (tradew _ (lamp i)) (basisKet x), show flipsP (lamp i) _=_ from twist_remove (tradew _ (lamp i)) (basisKet y), shade_here y i, shade_here x i, if_neg he, ih]; by_cases p:i=a <;> simp [((is_cap ..).mp v).2.2,((is_cap ..).mp v).2.1,p,Eq.comm (a:=a) (b:=i),pow_succ',smul_smul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
 | add _ _ a b=> rw [map_add,a,b,smul_add]
 | mul _ z t=> change twist _ (z • _) =_; rw [twist_scalar]; rw [show twist _ _= _ from t]; exact smul_comm ..
lemma powerS_nonunit (σ:Window.Family) : SU.z^(powerS σ)≠1 := fun t=>by have he:= SU.z_prim.dvd_of_pow_eq_one _ t; unfold powerS at he; split at he <;> norm_num at he -- tune
end YM.CF.Window.Brique
