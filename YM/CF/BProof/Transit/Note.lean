import YM.CF.Hive.Beam
import YM.CF.Fixed.Fine
import YM.CF.BProof.Garden.Wheat
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive
attribute [local instance] opCStarAlgebra
variable {n:Type}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
abbrev stung(S:List (Oboe n))(b:Bool) : Prop:=S.length%2= b.toNat
inductive Chord (b: Bool) : FC n→ Prop
| null: Chord b 0
| set (D:List (Oboe n)) : stung D b→ Chord b (Hive.drum D)
| add {A B}:Chord b A→Chord b B→Chord b (A+B)
| scale {A}:Chord b A→∀ z:ℂ,Chord b (z • A)
namespace Chord
variable {a b:Bool} {S T:Finset n} {A B:FC n}
lemma beat (p:Chord a A)(h:Chord b B) : Chord (a.xor b) (A*B):=by
 induction p with
 | null=> rw [zero_mul]; apply Chord.null
 | add _ _ i j=> rw [add_mul]; exact (i).add (j)
 | scale _ c i=> rw [Algebra.smul_mul_assoc]; exact i.scale _
 | set D g =>
    induction h with
    | null=> rw [mul_zero]; apply Chord.null
    | add _ _ i j=> rw [mul_add]; exact i.add j
    | scale _ c i=> rw [Algebra.mul_smul_comm]; exact i.scale _
    | set L k=> rw [show drum D*drum L=_ from (by simp [Hive.drum] : drum D*drum L=drum (D++L))]; apply Chord.set; unfold stung at *; rw [List.length_append]; cases a <;> cases b <;> simp at * <;> omega
lemma full (g:Fock.Sector S a A):Chord a A:=by
 induction g with
 | zero=> apply Chord.null
 | one=> exact Chord.set (n:=n) [] rfl
 | up i _=> simpa [Hive.drum,Hake.bell] using Chord.set (n:=n) (b:=true) [(true,i)] rfl
 | down i _=> simpa [Hive.drum,Hake.bell] using Chord.set (n:=n) (b:=true) [(false,i)] rfl
 | add _ _ i j=> exact i.add j
 | mul _ _ i j=> exact i.beat j
 | scale _ c i=> exact i.scale _
lemma keys_of_chord(h:Chord false A):Keys A:=by induction h with| null=>exact .null| set D h=> exact .roll D (Nat.even_iff.mpr h)| add _ _ i j=>exact .plus i j| scale _ c i=> exact .col c i
end Chord

lemma tilt_region {S T: Finset n}{a : Bool}{A:FC n}(p:Sector S a A)(h: twist U (cutM S)=cutM T): Sector T a (twist (quantU U) A):=by
  have he i (v:i∈S) : Sector T true (twist (quantU U) (put i)) := by rw [←create_put,twist_create]; exact Sector.makeP _ (by rw [←h,←Fock.swivel,cut_basis,if_pos v])
  induction p with
  | zero=> rw [map_zero]; apply Sector.zero
  | one=> rw [map_one]; exact .one
  | up i p=> exact he i p
  | down i p=> rw [takeF,map_star]; exact (he i p).contr
  | mul _ _ i j=> rw [map_mul]; exact i.mul j
  | add _ _ i j=> rw [map_add]; exact i.add j
  | scale _ c i=> rw [twist_scalar]; exact i.scale c
lemma twist_sector {S T : Finset n}{a:Bool}{A:FC n} (p:Sector S a A)(h:twist U (cutM S)=cutM T): Sector T a (Spire.tourP U false b A):=by cases b; exact tilt_region U p h; exact theta_carries U p h
lemma pay_s (A:FC n): ‖Spire.tourP U false b A‖=‖A‖:=by cases b; exact twist_norm ..; exact (twist_norm _ (cc A)).trans (norm_cc _)
end YM.CF.BProof.Bide
