import YM.CF.Pastry.Pie
import YM.CF.Skye.Bent
import YM.CF.Tap.Havana
import YM.CF.Proa.Lily
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]{r:ℕ}
lemma Wtrans (b:Bool){A:FC n}{s}(h:Flour s A): Flour s (windX b A):=by
 cases b; exact h
 rw [h.pin,win_sum]; apply Flour.sum
 intro i p; rw [win_c, show windX true (poke i)=(poke i) from ?_]; exact (Flour.point p).smul _
 clear p; induction i using Finset.induction_on with
 | empty=> rw [poke,Poly.tag_void,win_i]
 | insert i z p g=> unfold poke; rw [Poly.tag_any _ _ _ p,win_c,win_m, show windX true ((cane n).term i)=_ from put_clear i, show windX true ((cane n).tag z)= _ from g]; congr 1; exact parity_star ..
abbrev opBool:Equiv.Perm Bool:=⟨not, not, Bool.not_not,Bool.not_not⟩
def spice (U:UNI n)(a:Bool) : UNI (LeanV n):= if a then
 -- jump Boolean inversion, send u→!u. matrix at u input or output check jump
 ⟨jump (opBool) (fun (u:Bool)=> (thread (invFilm U) u).val), jump_unitary _ _ (fun u=>(thread _ u).property)⟩ else closeV U
lemma spirit (U:UNI n)(u:Bool)(i:n): twist (quantU (n:=LeanV n) (spice U true)) (wire u i)= ∑ j,(thread (invFilm U) (!u)).val j i • wire (!u) j:=by
 rw [wire,twist_p]; unfold prong; rw [Fintype.sum_prod_type]; simp only [spice, ↓reduceIte]; rw [sum_eq_single (!u)]; simp only [jump_apply]; simp [wire]; intro a _ p; simp [jump_apply,p]; simp
abbrev sauce (b r:Bool)(U:UNI n):FC (LeanV n)→FC (LeanV n):= sings (b.xor r) (quantU (spice U r))
def paintR (b r:Bool)(U:UNI n):ribbon n→ₐ[ℝ]ribbon n where
 toFun A:=⟨sauce b r U A.val,Flour.pivot (n:=LeanV n) (spice U r) (Wtrans (b.xor r) (fineShape A))⟩
 map_add' x y:= Subtype.ext (by change sauce b r U (x.val+y.val)=sauce b r U _+_; simp only [sauce,singT,win_a,map_add])
 map_one':= Subtype.ext (by change sauce b r U 1=(1:FC (LeanV n)); rw [sauce,singT,win_i,map_one])
 map_zero':= Subtype.ext (by change sauce b r U 0=(0:FC (LeanV n)); rw [sauce,singT,win_z,map_zero])
 commutes' c:=Subtype.ext (by rw [Algebra.algebraMap_eq_smul_one]; change sauce b r U (c • 1)=c • 1; rw [sauce,singT,win_r,win_i,map_smul,map_one])
 map_mul' x y:=Subtype.ext (by change sauce b r U (x.val*y.val)=_ *_; exact singm ..)
-- intertwiner Φ acts on every formal even term (not just projected symbols)
lemma cumin (b r:Bool)(U:UNI n)(A:FC n)(z:ℂ):Spire.tourP U b r (z • A)=cSignX (b.xor r) z • Spire.tourP U b r A:=by
 cases r; simp [Spire.tourP,singT,win_c,twist_scalar]
 change theta U (windX b _)=_; rw [win_c,theta_smul]; congr 1; cases b <;> simp [cSignX]
lemma nomZ(b r:Bool)(U:UNI n)(A B:FC n): Spire.tourP U b r (A*B)=Spire.tourP U b r A * Spire.tourP U b r B:=by cases r; exact singm ..; change theta U (windX b _)=_; rw [win_m,theta_mul]; rfl
lemma nutmeg(b r:Bool)(U:UNI n){I:Type*}(S:Finset I)(F:I→FC n):Spire.tourP U b r (∑ i∈S,F i)=∑ i∈S, Spire.tourP U b r (F i):=by
 classical
 cases r<;> simp [Spire.tourP,singT,win_sum,theta_sum]; -- tune
lemma tour_c(b r:Bool)(U:UNI n):Continuous (Spire.tourP U b r):=by cases r; exact (breeze _).comp (typ_l _); exact (theta_cont _).comp (typ_l _)
end YM.CF.Scree
