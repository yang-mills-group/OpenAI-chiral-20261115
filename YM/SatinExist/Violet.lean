import YM.SatinExist.Xenia
import YM.SatinExist.Regale
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
namespace Xara
variable (K:Calibration)(S T:Finset Cover)(x y:Cover)
/-- s removal generation, t gives creation. -/
abbrev GemUT:= Fin 3 × Fin 3 × Fin 2 × Fin 2
abbrev clone (A:GemUT) (a b:SU.F):= bum K x y A.1 A.2.1 a b A.2.2.1 A.2.2.2
abbrev sheen (A:GemUT): Dome K:=∑ a:SU.F, clone K x x A a a
variable (A B:GemUT)
lemma shine_mat: PureMatter K (sheen K x A):=by intro m i u; change (((screenHall K).val (sheen K x A)) m i)=(((screenHall K).val (sheen K x A)) m u); unfold sheen; rw [map_sum]; simp_rw [Finset.sum_apply]; rfl
lemma shine_local(p:nodeC x∈S) : sheen K x A ∈ bay K S true:= Submodule.sum_mem (bay K S true).toSubmodule (by
    intro i _; exact bum_bay K S x x _ _ i i _ _ p p)
-- cost scaling
open Ballad Ballad.Chalice
abbrev stoneOf (A:GemUT):Stone:= (((A.2.1,false),A.1), A.2.2.2,A.2.2.1)
lemma goldletter (n:ℕ) (N:Side): Wort x (stoneOf A) n (K.c N) = Twah.gold n • (sheen K x A).val N:=by
 funext V; rw [words]; simp only [Pi.smul_apply]; apply congrArg
 change _= ((screenHall K).val (∑ a:SU.F, clone K x x A a a)) N V; rw [map_sum, Finset.sum_apply,Finset.sum_apply]; symm
 refine sum_bij (fun i _=> Bun A.2.1 i) (fun i _=> mem_filter.mpr ⟨mem_univ _,rfl⟩) ?_ ?_ (fun x _=>rfl)
 · intro i _ j _ p; exact Sum.inr_injective (congrArg Prod.snd p)
 rintro ⟨a,b|b⟩ q; · cases (congrArg Prod.snd ((mem_filter.mp q).2))
 have h:a=A.2.1:=congrArg Prod.fst ((mem_filter.mp q).2)
 subst a; exact ⟨b,mem_univ _,rfl⟩
variable {E:Dome K→ₗ[ℂ]ℂ} (r: MatterWard K E) (p:Disjoint S T) (e:nodeC x∈ S)(l:nodeC y∈ T) (a b c d:SU.F)
include p r e
lemma deemed (f:Dome K)(F:PureMatter K f)(q:f∈bay K T true): E (sheen K x A*f) = 5* E (clone K x x A a a*f):=by
 dsimp only [sheen]; rw [sum_mul,map_sum]; rw [sum_congr rfl (fun i _=>same_diag K T x _ _ _ _ f r F q (Finset.disjoint_left.mp p e) i a),sum_const,card_univ,nsmul_eq_mul]; simp [SU.F]
include l
lemma card_cost : E (sheen K x A*sheen K y B)= 25*E (clone K x x A a a * clone K y y B b b):=by
 rw [deemed K S T x A r p e a (sheen K y B) (shine_mat K _ _) (shine_local K T y B l), mul_comm (clone ..), deemed K T S y B r p.symm l b _ (bum_mat K _ _ _ _ _ _ _ _) (bum_bay K _ _ _ _ _ _ _ _ _ e e),mul_comm (clone K y ..)]; ring
variable (w z:Cover)(v:nodeC w∈S)(q:nodeC z∈T)
include v q
open Ballad
lemma limits (h:ℝ)(hp:0≤h)(t:‖E (sheen K x A*sheen K y B)‖ ≤ h): ‖E (clone K x w A a b* clone K y z B c d)‖ ≤ if x=w ∧ y=z then h else 0:= by
 let C:= clone K x w A a b; let D:=clone K y z B c d
 have f:D∈bay K T true:= bum_bay K T _ _ _ _ _ _ _ _ l q
 have f': C∈bay K S true:= bum_bay K S _ _ _ _ _ _ _ _ e v
 have h1:=disjoint_left.mp p e; have h2:=disjoint_left.mp p.symm l
 have hu:nodeC x∉ T:=h1; have ht:nodeC y∉S:=h2
 by_cases i:x=w; swap; · rw [if_neg (fun z=> i z.1),offNode K T x w A.1 A.2.1 a b A.2.2.1 A.2.2.2 D r (bum_mat K _ _ _ _ _ _ _ _) f hu i (Finset.disjoint_left.mp p v),norm_zero]
 by_cases j:y=z; swap; · rw [if_neg (fun z=> j z.2),mul_comm,offNode K S y z _ _ c d _ _ C r (bum_mat K _ _ _ _ _ _ _ _) f' ht j (Finset.disjoint_left.mp p.symm q),norm_zero]
 rw [if_pos ⟨i,j⟩]; subst w z
 by_cases i:a=b; swap; · rw [not_diag K T _ _ _ a b _ _ D r (bum_mat K _ _ _ _ _ _ _ _) f hu i,norm_zero]; exact hp
 by_cases j:c=d; swap; · rw [mul_comm,not_diag K S _ _ _ c d _ _ C r (bum_mat K _ _ _ _ _ _ _ _) f' ht j,norm_zero]; exact hp
 subst b d
 rw [card_cost K S T _ _ _ _ r p e l a c,norm_mul] at t
 exact (le_mul_of_one_le_left (norm_nonneg _) (show 1≤ ‖(25:ℂ)‖ from by norm_num)).trans t
#print axioms limits
end Xara
end YM.CF.Buffered.Afterglow.Six
