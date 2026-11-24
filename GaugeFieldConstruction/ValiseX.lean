import GaugeFieldConstruction.FormeH
import GaugeFieldConstruction.Velab
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry
section
variable {n:Side}{α β I:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β]
-- Generic Tool charges indexed by label world always include powers `$ℓ^|T|`. use nonzero fulfillment only on own-valid. Same on Press3/Medal2/Firm/Mask. B normally Cleaf. DollarEP θ(r).
variable (σ:I→ Site n)
variable {E:Type}[AddCommMonoid E][Module ℂ E]
def Pub (L:Finset I)(o: Support n):Prop:= L∈realm_C σ∧ poke_F σ o L
abbrev postT (M:Type)(α I:Type):= (Finset I × α) → M -- Heave
abbrev dues(I α:Type):=Finset I×α
def keepArc (W: α→Support n) (V:postT E α I):Prop:=∀ i:dues I α,V i≠0→ Pub σ i.1 (W i.2)
def Canz (H:Type) [AddCommMonoid H][Module ℂ H] (V:dues I α→H)(x:Key I)(j:α):= ∑ k∈ realm_C σ,pine k x • V (k,j)
-- choose uncurried direct abbrev.Memory
variable (V:dues I α→E)
lemma puff_add (G:dues I α→ E)(x:Key I)(i:α):Canz σ E (V+G) x i=Canz σ E V x i+Canz σ E G x i:=by unfold Canz; simp_rw [Pi.add_apply,smul_add, sum_add_distrib]
lemma puff_zero(x:Key I)(i:α):Canz σ E (fun _:dues I α=> (0:E)) x i=0:=by unfold Canz; simp
-- coefficient certification template
variable (X:α→Support n)
structure BondM (X:α→Support n)(σ:I→Site n)(T: dues I α→E→ℝ→Prop)(A:dues I α→ ℝ)(F:dues I α→E) : Prop where
 lit(i): T i (F i) (A i)
 gist(i):0≤A i
 pin:keepArc σ X F
-- T laws pre-h dynamically parameter r. invariant includes implicit Shape stamps.T.Journal.
structure ReefX (T:dues I α→E→ℝ→Prop):Prop where
 tele(i) : T i (0:E) 0
 join(i)(x y:E)(a b:ℝ):T i x a→T i y b→ T i (x+y) (a+b)
namespace ReefX
variable {T:dues I α→E →ℝ→Prop}
lemma registry_plus (p:ReefX T){U U':dues I α→ E}{A A':dues I α→ ℝ}(x:BondM X σ T A U)(y:BondM X σ T A' U'):BondM X σ T (A+A') (U+U') :=by
 refine ⟨fun i=>p.join _ _ _ _ _ (x.lit i) (y.lit i),fun i=>add_nonneg (x.gist _) (y.gist _),fun i g=>?_⟩
 by_cases a:U i=0
 · apply y.pin; exact fun h=> g (by change U i+U' i =0; rw[a,h,zero_add])
 exact x.pin i a
lemma registry_zero (p:ReefX T): BondM X σ T 0 0:= ⟨fun i=>p.tele i,fun i=>le_rfl,fun i g=>False.elim (g rfl)⟩
lemma registry_sum (p:ReefX T){k:Type*} (L:Finset k)(V:k→ dues I α→ E)(A:k→ dues I α→ ℝ)(c:∀ i∈L,BondM X σ T (A i) (V i)): BondM X σ T (∑ i∈L,A i) (∑ i∈L,V i):=by
 induction L using Finset.induction_on with
 | empty => rw[sum_empty,sum_empty]; exact registry_zero _ _ p
 | insert a L h ih=> rw[sum_insert h,sum_insert h]; exact registry_plus _ _ p (c a (mem_insert_self ..)) (ih (fun i h=>c i (mem_insert_of_mem h)))
end ReefX
omit σ
variable (B:dues I α→ℝ)
abbrev AxeX (X:α→Support n)(F:dues I α→ℝ): α→ℝ:=fun x=>∑ T:Finset I,F (T,x)
abbrev pointX (X:α→Support n)(F:dues I α→ℝ)(c:Support n→ℝ)(y:Site n):= postG X (AxeX X F) c y
def zoneD (W:α→Support n)(x:dues I α): Support n:=W x.2 -- tune variable order
lemma pointX_0(y:Site n)(c:Support n→ℝ):pointX X (0:dues I α→ℝ) c y=0:=by unfold pointX postG postY; simp[AxeX,Lattice.Corona.Hive.beam]
lemma pointX_π (y:Site n)(c:Support n→ℝ): postG (zoneD X) B c y = pointX X B c y :=by
 unfold pointX postG postY AxeX Lattice.Corona.Hive.beam; rw[sum_filter (p:=fun i:Finset I×α=>_),Fintype.sum_prod_type]; simp_rw[zoneD]; rw[sum_comm]; rw[sum_filter]; apply sum_congr rfl; intro i _; by_cases h:y∈ X i; simp_rw [if_pos h]; rw [sum_mul]; simp_rw [if_neg h,sum_const_zero]
lemma pointX_add (A:dues I α→ℝ)(c:Support n→ℝ)(y:Site n): pointX X (B+A) c y=pointX X B c y+pointX X A c y:=by unfold pointX postG postY AxeX Lattice.Corona.Hive.beam; simp_rw[Pi.add_apply, Finset.sum_add_distrib, add_mul,Finset.sum_add_distrib]
lemma pointX_sum (y:Site n)(c:Support n→ℝ){k:Type*}(L:Finset k)(V:k→dues I α→ ℝ): pointX X (∑ i∈L,V i) c y=∑ i∈L,pointX X (V i) c y:=by
 induction L using Finset.induction_on with
 | empty => rw[sum_empty,sum_empty,pointX_0]
 | insert a L h ih=> rw[sum_insert h,sum_insert h,pointX_add,ih]
lemma pointX_gene (p:∀ i,0≤ B i)(c:Support n→ℝ)(v:∀ i,0≤ c i)(y:Site n): 0≤pointX X B c y:=by rw[←pointX_π]; exact sum_nonneg fun j _=>mul_nonneg (p _) (v _)
end
section alloc
variable {n:Side}{α I E:Type}[LinearOrder I][Fintype I][Fintype α] [DecidableEq α]
variable [AddCommMonoid E][Module ℂ E]
variable (T: α)(S:List I)(X:α→Support n)(σ:I→Site n)(A:E)
def clipK {E:Type}[Zero E] (σ:I→Site n)(i:α)(L:List I)(b:E) : dues I α→ E:= fun x=> if ψS σ L ∧ x=(L.toFinset,i) then b else 0
lemma allot_sum {T': dues I α→ E→ ℝ→Prop}(p:ReefX T')(e:ℝ)(c:0≤e)(t:ψS σ S→T' (S.toFinset,T) A e)(w:ψS σ S→A≠0 → Pub σ S.toFinset (X T)):BondM X σ T' (clipK σ T S e) (clipK σ T S A):=by
 constructor
 · intro i; unfold clipK; split
   next h=> rw[h.2]; exact t h.1
   exact p.tele i
 · intro i; unfold clipK; split; exact c; exact le_rfl
 intro i h; unfold clipK at h; split at h
 next g=> rw[g.2]; exact w g.1 h
 exact False.elim (h rfl)
lemma allot_C (e:ℝ)(p:ψS σ S)(A':Support n→ℝ)(y:Site n):pointX X (clipK σ T S e) A' y= if y∈ X T then e*A' (X T) else 0:=by
 rw[←pointX_π]; unfold postG postY clipK Lattice.Corona.Hive.beam; simp_rw[p,true_and,ite_mul,zero_mul]; rw [Finset.sum_filter,Finset.sum_eq_single (S.toFinset,T)]
 · unfold zoneD; dsimp only; simp
 · intro i _ h; split_ifs <;> first | rfl | exact False.elim (h ‹_›)
 simp
lemma allot_le (e:ℝ)(c:0≤ e)(A':Support n→ℝ)(q:∀ i,0≤ A' i)(y:Site n):pointX X (clipK σ T S e) A' y ≤ if y∈ X T then e*A' (X T) else 0:=by
 by_cases v:ψS σ S; · exact (allot_C _ _ _ _ _ v _ _).le
 rw[show clipK σ T S e=0 from (funext fun i=>if_neg (fun h=>v h.1)),pointX_0]; split; exact mul_nonneg c (q _); exact le_rfl
end alloc
end YM.CF.Scree.Ing
end
