import YM.CF.Continuum.GraspPolar
import YM.CF.Pic.Cash
/-! Reference mass price: only polynomial suppression even with tuned holonomy. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Dial Peaks Cascade Vault Paige
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B N m:Side}{j n:ℕ}{r d c x κ b t:ℝ}{O:Odd L.val}{Y:Pricing j L O (Thread j)} {P:Grasp Y B d}{hP:Pearl P}
lemma window_angle {j:ℕ}(h:1 ≤ j)(p:0<r): ∃ (v:ℝ)(k:ℕ), 0<v ∧ ∀ N:Side, Even N.val → ∀ M:Jill.Male,
    let T:=needlesView N; v*(N.val:ℝ)^(-(k:ℤ)) * iceK j T M r ≤ ∏ i:Stag N,disk j M (Kea.angle T i):=by
  obtain ⟨u,C,e,b,t⟩:= tiltLower j h; obtain ⟨A,F⟩:= risky_card j h r p
  let B:= min 1 (u/(r*Real.pi^2)); have hv:0<B:=lt_min one_pos (by positivity); refine ⟨B^A,16*A,pow_pos hv _,fun N p' M=>?_⟩; intro T; let k:=N.val; have ht:(1:ℝ)≤k:=Nat.one_le_cast.mpr N.property; let a:=((k:ℝ)^16)⁻¹; let X:=risky T j M r
  have ha:0<a:=by unfold a; positivity
  let y:=B*a; let g(i:Stag N):=disk j M (Kea.angle T i); let f(i):=Jill.cup N j M r (Kea.angle T i); have hy:0<y:=mul_pos hv ha; have he:y≤1:=by
    have hx:B≤1:=min_le_left ..; refine le_trans (mul_le_of_le_one_right hv.le (inv_le_one_of_one_le₀ (one_le_pow₀ ht))) hx
  have hs(i): (if i ∈ X then y else 1)*f i ≤ g i:=by
    by_cases k':i∈X
    · rw [if_pos k']; have hw:= (mem_filter.mp k').2; unfold f; rw [Jill.cup,max_eq_left (show g i ≤ _ from hw)]
      apply le_trans ?_ (t N p' M i).1; calc
        y*(r*pinch N^2) ≤ u/(r*Real.pi^2)*a*(r*pinch N^2) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right ..) ha.le) (by positivity)
        _ = _:= by unfold a k pinch; rw [zpow_neg,zpow_ofNat]; field_simp
    rw [if_neg k',one_mul,show f i=max _ _ from rfl,max_eq_right (show _ ≤ g i from (lt_of_not_ge (fun x=>k' (mem_filter.mpr ⟨mem_univ _,x⟩))).le)]
  apply le_trans ?_ (prod_le_prod ?_ (fun i _=> hs i))
  rotate_left
  · intro i _; apply mul_nonneg _ (cup_p M p _).le; split_ifs; exact hy.le; exact zero_le_one
  rw [prod_mul_distrib]; unfold iceK; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _=> (cup_p M p _).le); rw [prod_ite]; rw [prod_const, prod_const_one,mul_one, show univ.filter (·∈X) =X by ext; simp]
  apply le_trans ?_ (pow_le_pow_of_le_one hy.le he (F N p' (needles N) T M)); apply le_of_eq; unfold y a k; rw [mul_pow, _root_.zpow_neg, _root_.zpow_natCast,inv_pow, ←pow_mul]; -- trims
lemma tiltMass (D:Pic.Span hP κ b x c t r n) : ∃ (v:ℝ)(k:ℕ),0<v ∧ ∀ m:Side,n ≤ (CSide m B).val→∀ (M:Jill.Male), let N:= CSide m B; v*(N.val:ℝ)^(-(k:ℤ))*Kea.angel m P M ≤ ‖Kea.AMP m P (needles N) M‖:=by
  obtain ⟨v,k,z,H⟩:= window_angle D.p D.rP; refine ⟨v*b,k,mul_pos z D.pos,fun m e M=>?_⟩; let N:= CSide m B; let S:=needlesView N; obtain ⟨u,X⟩:= D.plan m e; intro N'; dsimp only at *; let d:=v*(N'.val:ℝ)^(-(k:ℤ))
  rw [rich u D.eP M X (needles N') (needlesView N'),show v*b*_*_=d*(b*Kea.angel m P M) from ?_]; swap; · unfold d; ring
  exact le_trans (mul_le_mul_of_nonneg_left (D.powV m e M (needles N) S).1 (by unfold d; positivity)) (H N X.1 M)
end YM.CF.Window
