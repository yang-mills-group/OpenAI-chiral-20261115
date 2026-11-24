import YM.SU5.Exchange.Pipe.Latch
import YM.SU5.Exchange.Pipe.Raw
/-!
Transport the *short-footprint* source-kernel schedule as well as the
pre-truncation budget. Needed for using plus and minus displacements of the
VERY same truncated J stencil in our marked observable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG Vow MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side} {F : SOp N} {o : Seat N} {a b d : ℝ} {k : ℕ}
local notation "Ω" => Single N

/-- As for `jul_sells`, now keeping root and truncation inside the licence. -/
theorem Trunk.transportSweep (p : Trunk o F k a b d) (s : Sweep N) :
    Trunk (boxA s o) (julStep s F) k a (Tenant.quota^2*b) d := by
  obtain ⟨T,C,h,v,H,q⟩ := p.home
  refine ⟨jul_sells s p.pay,?_⟩
  let Q : Sa N ≃ Sa N :=
    ⟨actY s⁻¹,actY s,fun R => by simpa only [inv_inv] using seeS s⁻¹ R, seeS s⟩
  let A := noteU s⁻¹
  let Z (R : Sa N) := Mx s d (T (Q.symm R))
  let B (R : Sa N) : Toll Ω := A (C (Q.symm R))
  have HZ (R : Sa N) : Z (Q R) = Mx s d (T R) := by simp only [Z,Equiv.symm_apply_apply]
  have HB (R : Sa N) : B (Q R) = A (C R) := by simp only [B,Equiv.symm_apply_apply]
  have hd : 0 ≤ Tenant.quota := (by norm_num : (0:ℝ) ≤ 16).trans quota_bound
  refine ⟨Z,B,?_,?_,?_,?_⟩
  · intro R
    obtain ⟨S,rfl⟩ := Q.surjective R
    rw [HZ, HB]
    exact mini _ _ _ _ (h S)
  · intro R hR
    obtain ⟨S,rfl⟩ := Q.surjective R
    have hp : C S ≠ 0 := by
      intro ht
      apply hR
      rw [HB,ht]; unfold A noteU; ext; simp
    have hx := v S hp
    change boxA s o ∈ actY s⁻¹ S ∧ (actY s⁻¹ S).card < _
    exact ⟨by simp [actY,sitU,hx.1], by simpa only [actY,card_map] using hx.2⟩
  · rw [← Equiv.sum_comp Q (fun R : Sa N => Branch.rent a R * ledgerV (B R))]
    simp_rw [HB]
    apply le_trans _ (mul_le_mul_of_nonneg_left H (sq_nonneg _))
    rw [mul_sum]; apply sum_le_sum; intro i _
    rw [Branch.rent,show (Q i).card=i.card from card_map ..,mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    unfold A noteU ledgerV; simp_rw [normU,mul_sum]
    let L (x y j k : Ω) := jLL s⁻¹ x j*jLL s⁻¹ y k*C i j k
    change ∑ x:Ω,∑ y:Ω,∑ j:Ω,∑ k:Ω,L x y j k ≤ _
    simp_rw [sum_comm (f:=fun y (j:Ω)=> ∑ k:Ω,L _ y j k)]
    rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [sum_comm (f:=fun y k=> L _ y j k)]; rw [sum_comm]; apply sum_le_sum; intro k _
    unfold L; simp_rw [←Finset.sum_mul,←Finset.mul_sum]; rw [←Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ ((h i).nonn _ _)
    exact (mul_le_mul (ρ_K ..) (ρ_K ..) (sum_nonneg fun t _=>norm_nonneg _) hd).trans_eq (by ring)
  intro x
  rw [← Equiv.sum_comp Q (fun R : Sa N => Z R x)]
  change ech s⁻¹ (F (Sour.fog s d x).val)= _; rw [q]
  simp_rw [HZ]; unfold ech; rw [singT,win_sum,map_sum]; rfl

theorem Trunk.station {x : Site N} (p : Trunk (node x) F k a b d) (y : Site N) :
    Trunk (node y) (co_Ψ y x F) k a (Tenant.quota^2*b) d := by
  rw [show node y=boxA (taxiPlus (y-x)) (node x) from (by rw [platforms, add_sub_cancel])]
  exact p.transportSweep _

end YM.CF.Swell
