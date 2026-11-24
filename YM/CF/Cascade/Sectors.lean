import YM.CF.Cascade.Basque
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma wedgeP {n:Type*}[DecidableEq n][Fintype n]{P:Op n}(h:IsStarProjection P): ‖P‖≤1:=by have hp:= CStarRing.norm_star_mul_self (x:=P); rw [show star P=P from h.2,h.1] at hp; nlinarith
variable {M:Male}{J:InJ Slot n}{T:Op Slot}
lemma wedge_on {n:Type*}[DecidableEq n][Fintype n][Nonempty n](V:UNI n): ‖V.val‖=1:=by have hx:= CStarRing.norm_star_mul_self (x:=V.val); rw [V.property.1,norm_one] at hx; nlinarith [norm_nonneg V.val]
lemma saV {S:Type}[DecidableEq S][Fintype S]{A:Op SpinIdx}(p:A*A=A)(s:star A=A):‖(A ⊗ₖ (1:Op S))‖≤1:=by
 apply wedgeP; constructor
 · unfold IsIdempotentElem; rw [op_kron_mul,mul_one,p]
 unfold IsSelfAdjoint; rw [op_star_kron,star_one,s]
lemma unitH(S:Type)[DecidableEq S][Fintype S](i:Site n):‖fuel S j M.val (mel i)‖≤1:=by
 unfold fuel; have ht:= firm_bar j M.val M.property (base_subset_realCube zone_pos (mel_h i)); rw [show (Aop*bar j M.val _)⊗ₖ (1:Op S)= (Aop⊗ₖ (1:Op S))*(bar j M.val (mel i)⊗ₖ (1:Op S)) by rw [op_kron_mul,mul_one]]; exact (norm_mul_le ..).trans (mul_le_one₀ (saV AOne Aadj) (norm_nonneg _) (saV ht.1 ht.2))
lemma fence (H:Foot T j M.val J):‖J 0‖≤1:=by
 rw [H.around]; unfold subHub hub; rw [twist_formula]; let V:= spatialU n Slot
 apply (norm_mul_le ..).trans; refine mul_le_one₀ ?_ (norm_nonneg _) ((norm_star _).trans_le (wedge_on V|>.le)); apply (norm_mul_le ..).trans; exact mul_le_one₀ (wedge_on V|>.le) (norm_nonneg _) (jump_bound _ _ zero_le_one (fun i=>unitH Slot i))
lemma kroner (p:0<a)(h:0<b)(j:ℕ)(z:1≤j):∃ C:ℝ,0<C∧∃ i:ℕ,∀ {N:Side}{T:Op Slot}{J:InJ Slot N}{M: Male},Foot T j M.val J→i≤ N.val→ Even N.val→Aroma.bill J a ≤ b→ b2 (Met J) a≤b→∀ x: Air N,‖x‖≤1→ |palmH J x|≤ C*N.val*(Fintype.card (Site N):ℝ):=by
 obtain ⟨D,hD,i,H⟩:= priceGreen z; let Y:ℝ:= ↑(Fintype.card (coneA Slot)); let W:= Y*b; let C:= Y + D*((2*W)^2+W^2); have hy:0<Y:=by unfold Y; positivity
 have hx:0<W:=by unfold W; positivity
 have ht:0<C:=by unfold C; positivity
 refine ⟨C,ht,i,fun {n T J M} P he hg hj hr x hx'=>?_⟩
 let m:=(Met J 0)⁻¹; let f:=JD (Met J) x; let A:= JG (Met J) x x; let v:= Fintype.card (Site n); let Q:ℝ:= (n.val:ℝ)*v; have hp:0≤Q:=by have hn:= side_pos n; positivity
 have hu: kg m≤ D*Q:=by unfold Q; rw [←mul_assoc]; exact H P he hg
 have hm:‖f‖ ≤ 2*W:=by let A:=JD J x; rw [show f=_ from legM P.smooth x]; apply (norm_add_le ..).trans; apply ((add_le_add (norm_mul_le ..) (norm_mul_le ..))).trans; rw [norm_star,norm_star,two_mul]; have hx := pass_p J P.smooth P.curve p.le h.le hj x hx'; exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) (fence P)).trans hx) ((mul_le_of_le_one_left (norm_nonneg _) (fence P)).trans hx)
 have hA:‖A‖≤W:= pass_z (Met J) (met_ray _ P.smooth) (met_curve _ P.curve) p.le h.le hr x hx'
 have hv : kg (m*f) ≤ (D*Q)*(2*W)^2:= (kg_b ..).trans (mul_le_mul hu (pow_le_pow_left₀ (norm_nonneg _) hm _) (sq_nonneg _) ((kgN _).trans hu))
 have hk : kg (m*A) ≤ (D*Q)*W^2:= (kg_b ..).trans (mul_le_mul hu (pow_le_pow_left₀ (norm_nonneg _) hA _) (sq_nonneg _) ((kgN _).trans hu))
 let T':= Q*C; have hQ: |(Matrix.trace ((m*f)*(m*f)-m*A)).re|≤ T':=by
    rw [Matrix.trace_sub,Complex.sub_re]; refine (abs_sub _ _).trans ((add_le_add ((kg_d ..).trans hv) ((kg_c ..).trans (add_le_add_right hk _))).trans ?_); unfold T' C; have hh : (Fintype.card (Tx n Slot):ℝ) ≤ Q*Y:=by
       unfold Tx; rw [Fintype.card_prod, Nat.cast_mul]; apply mul_le_mul_of_nonneg_right _ hy.le; exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast n.property)
    linarith only [hh]
 rw [show palmH J x= (1/2:ℝ)*(Matrix.trace ((m*f)*(m*f)-m*A)).re from ?_, abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (by norm_num)).trans (hQ.trans_eq (by unfold T' Q; ring))
 rw [show m*f*(m*f)=m*f*m*f from (mul_assoc ..).symm]; exact P.issue x
end YM.CF.Cascade
