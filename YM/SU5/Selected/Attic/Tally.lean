import YM.SU5.Selected.Dais.Rank
import YM.SU5.FiniteGaugeData.Pannier.Veldt
/-!
# Many identity-subtractions. Keep factor costs before seeking any path-tail threshold.
Here tilt by total Access degree. Copy arguments of ShelfFog.lean & preserve communication. This is an operator inequality, not using any of the gauge-calibration estimates
(and doesn't hold without the phase/orthogonality/Wick data stated). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Fixed Skye Pastry
open Damask
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n ι : Type*}[LinearOrder n][Fintype n]
-- permits epsilon-power estimates independent of k. Note the same orientation in D. for pricing.

open Dais.Parity
variable [Nonempty n]

namespace Folder
variable {X Y Y' A A':ι→FC n}{b:Bool}{r E:ℝ}{M W:Wave n}{G:FC n}
    (p:Folder X Y Y' A A' b r E M W G)
local notation "ℓ" => fun i:ι=> together (X i) (Y i)
local notation "℮" => fun i:ι=> X i*(Y' i-Y i)
local notation "ℸ" => fun i:ι=> together (X i) (Y' i)
include p
variable {P:Op n}(hpQ:IsStarProjection P){τ:ℝ} (hτ:0<τ)(hT:τ≤1){deg:ℕ}(gG:Riser deg G)(e:0<E)(c:0<r)(t:E ≤ 1)
local notation "B"=> E*(r+2)
local notation "C"=> E*(r+3)
omit p in
lemma all_p {P':Op n}{m:ℕ}{L':ι→FC n} (e:∀ i,Letter (L' i))(k:List ι)(U:Wave n)(v:Access P' m U): Access P' (m+k.length) (acts (fo L' k) U):=by
 induction k with
 | nil=> rw [List.length_nil, Nat.add_zero, show fo L' []=1 from rfl,act_one]; exact v
 | cons i k ih=> rw [List.length_cons,←Nat.add_assoc, show fo L' (i::k)= L' i*fo L' k from rfl,act_mul]; exact access_letter ih (e i)
local notation "P₀" D:max=> ‖driftW (cards P τ) M‖ * τ⁻¹^ D
include hpQ hτ hT gG e t c
lemma glamQ (L:List ι)(U:Wave n)(k:ℕ)(d:Pause A k U)(h:L.Nodup) {D R:ℕ} (wd:deg+2*L.length+R≤ D)(dR: Access P R U) : ‖inner ℂ M (acts (fo (ℓ) L*G) U)‖ ≤ (E*(r+2))^L.length*(‖G‖*(‖U‖*E⁻¹^k))*(P₀ D) := by
 obtain ⟨x,a,b⟩:= p.shuffle L h
 rw [act_mul,p.still L h,b,act_smul,inner_smul_right,norm_mul,a,one_mul,act_mul]
 let x0:= fo A L; have he (L : List ι):‖fo X L‖≤1:=by
    induction L with
    | nil=> simp [fo]
    | cons i l ih=> -- ih premises? shuffle deps
       rw [fo,List.map_cons,List.prod_cons]; apply (norm_mul_le ..).trans; exact (mul_le_mul (p.lifetime i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
 have hf:= deposit G A' r _ p.pitch p.switched p.change p.box p.price e t d c
 let y:=acts (fo A L) (acts G U); have hz: Access P (deg+R+L.length) y:= all_p (L':=A) (fun i=> ⟨_,p.pitch i⟩) L _ (gG _ _ _ dR); let T:= acts (fo X L) y; have ht:Access P D T:=(all_p p.near L _ hz).mono (by omega)
 apply (income (M:=M) ht hpQ hτ hT).trans; rw [←mul_assoc ‖driftW (cards P τ) M‖]; apply le_trans (mul_le_mul_of_nonneg_left (show ‖T‖ ≤ _ from ((Graph.spentS _ _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (he L))).trans (hf L)) (by positivity)); rw [mul_comm]

omit hpQ hτ hT gG e c t
private lemma riot (i:ι): (ℸ) i=(ℓ) i+(℮) i:=by unfold together; simp only [mul_sub]; abel
include hpQ hτ hT gG e c t
lemma tenderQ (l k:List ι) (ψ:Wave n) (K:ℕ) (h:Pause A K ψ) (g:(k++l).Nodup){R F0:ℕ}(wd:deg+2*(k.length+l.length)+R≤F0)(w0:Access P R ψ):
    ‖inner ℂ M (acts (fo (ℓ) k * fo (ℸ) l * G) ψ)‖ ≤ B^k.length*C^l.length * (‖G‖ * (‖ψ‖ * E⁻¹^K)) * (P₀ F0):= by
 let q:=(B); let r':=(C); have hp:0<q:=by unfold q; positivity
 have hR:0<r':=by unfold r'; positivity
 change _≤ (q^(k.length)*r'^(l.length)*_)*(P₀ F0)
 induction l generalizing k K R ψ with
 | nil=> simp only [fo,List.map_nil,List.prod_nil,mul_one,List.length_nil,pow_zero] at *; exact p.glamQ hpQ hτ hT gG e c t _ ψ _ h (by simpa using g) (by simpa using wd) w0 -- tune order
 | cons i l ih=>
    have he (j): Letter (A j):= ⟨b,p.pitch j⟩
    let H:= (℮) i; have ha:‖H‖ ≤ E^3:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (p.lifetime i)).trans (p.frost i))
    let a:= fo (ℓ) k; let v:= (acts H ψ); have hv: Pause A (K+2) v:=by unfold v; rw [show H=X i*(Y' i-Y i) from rfl,act_mul]; exact pause_one (p.near i) he (pause_one (p.roar i) he h)
    have hn: (k++l).Nodup:=g.sublist (List.Sublist.append (List.Sublist.refl k) (List.Sublist.cons i (List.Sublist.refl l))) -- ?. .sublist
    let ℓ' := fo (ℸ) l
    have ht(r:List ι):Commute H (fo (ℸ) r):=by induction r with| nil=> exact Commute.one_right H| cons i' L ih=> exact (p.mail i i').mul_right ih
    have h':Commute H (ℓ'*G):= (ht l).mul_right (p.parcel i)
    let F:= fo (ℓ) (k++[i]); let A':= (ℸ) i
    have hI(j:ι) : fo (ℓ) (k++[j])=a*(ℓ) j:=by simp [fo,a]
    change ‖inner ℂ M (acts (a * (A'*ℓ')* G) ψ)‖≤ _
    let D:= ‖G‖*(‖ψ‖* E⁻¹^K)
    rw [show a*(A'*ℓ')*G= F *ℓ'*G+(a*ℓ'*G)*H from ?_,act_add,inner_add_right]; swap
    · unfold A'; rw [p.riot i]; change a * ((_+H)*_) *_= _; rw [show F= _ from (show F=a* (ℓ) i from hI i)]; rw [add_mul, mul_add, add_mul]; simp only [mul_assoc]; rw [h'.eq]; simp only [mul_assoc]
    apply (norm_add_le ..).trans; rw [act_mul (a*ℓ'*G)];
    have hf := ih (k++[i]) ψ K h (by simpa using g) (by simp at wd ⊢; omega) w0 -- local ih closure incl l fixed
    apply (add_le_add hf ((ih k v _ hv hn (R:=R+2) (by rw [List.length_cons] at wd; omega) (by unfold v H; rw [act_mul]; exact access_letter (access_letter w0 (p.roar i)) (p.near i))).trans _)).trans_eq (show q^(k++[i]).length*r'^l.length*D*(P₀ F0)+(q^k.length*r'^l.length*D* E*(P₀ F0))=q^k.length*r'^(i::l).length*D*(P₀ F0) from ?_)
    swap
    · rw [List.length_cons,List.length_append,List.length_singleton,pow_succ,pow_succ]
      have Ht:r'=q+E:=by unfold q r'; ring
      rw [Ht]; ring
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_trans (Graph.spentS n H ψ) (mul_le_mul_of_nonneg_right ha (norm_nonneg _))) (by positivity)) (norm_nonneg G)) (by positivity)) (by positivity)).trans_eq ?_
    unfold D; rw [pow_add E⁻¹]; field_simp


end Folder
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Folder.tenderQ
#print axioms YM.CF.Pannier.Chancel.Folder.glamQ
