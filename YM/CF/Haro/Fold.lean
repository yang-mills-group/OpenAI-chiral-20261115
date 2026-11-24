import YM.CF.Prism.Gale
import YM.CF.Yaw.Oar
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Hake Urn
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable(G:Ratio c f)(ho:Odd G.count.val)(T:Script Male)(u:Use j G.count T)(M:Male)
-- momentum rooted at FIRST OUTPUT endpoint, charge full per x even after reassign.RE.Loses 4 exactly
abbrev perk(x y:Single c):= (1+separation (place_x x) (place_x y):ℝ)^m
private lemma ship (a:ℝ)(h:0<a): ∃ C:ℝ,0<C∧∀ y:ℝ,0≤y→ gum m y≤ C*Real.exp (a*y):=by
 let x:=a/(m+1); let F:=max 1 x⁻¹; have ht:0<x:=div_pos h (by positivity); have hv:0<F:=lt_of_lt_of_le one_pos (le_max_left ..)
 refine ⟨F^m,pow_pos hv _,fun y hy=>?_⟩; unfold gum; calc
   _ ≤ (F*Real.exp (x*y))^m:=by
      have hx: y≤ F*(x*y):=by rw [←mul_assoc]; exact le_mul_of_one_le_left hy ((inv_le_iff_one_le_mul₀ ht).mp (le_max_right ..))
      have hp:1≤F:=le_max_left ..; have hv:= Real.add_one_le_exp (x*y)
      refine pow_le_pow_left₀ (by positivity) ?_ _; nlinarith only [hx,hp,mul_le_mul_of_nonneg_left hv (zero_le_one.trans hp)]
   _ ≤_:=by
      rw [mul_pow,←Real.exp_nat_mul]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity); rw [←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ hy; unfold x; field_simp; nlinarith
lemma sting (x y:Single c)(i:Single f): perk m x y≤ Tap.streak G m i x * Tap.streak G m i y:=by
 unfold perk Tap.streak gum; rw [←mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _; have hp:(separation (place_x x) (place_x y):ℝ)≤ (dish G i x+dish G i y:ℝ):= by
    unfold dish; rw [separation_comm _ (place_x x)]; exact_mod_cast separation_triangle (place_x x) _ (place_x y)
 have hx:0≤ (dish G i x:ℝ):=by positivity
 have hq:0≤ (dish G i y:ℝ):=by positivity
 nlinarith only [hp,hx,hq,mul_nonneg hx hq]
omit u
include e h
lemma grove (p:4 ≤ j) (ht:2≤ m) : ∃ C:ℝ,0<C ∧∀ {c f:Side}(G:Ratio c f)(ho:Odd G.count.val)(T:Script Male)(u:Use j G.count @T)(M:Male)(F:Cover→ Pal)(W:Momentum→ Pal)(k:ℝ),0 ≤ k→Reads F W→RailP m F k→NullW (potion j M W)→∀ x:Single c,
 let P:=funde j M f 1; let B:Op (Single c):=(fan G ho @T j false M [])ᴴ *(1-P)*love f (cart f F)*P*fan G ho @T j true M []; paidX (perk m x) (fun y:Single c=> B x y) ≤ C*k/G.count.val:=by
 obtain ⟨a,U,v,b,H⟩:=bluff j e h false; obtain ⟨D,r,L⟩:= ship m a v; obtain ⟨R,w,J⟩:= Tap.giant j m e p ht true
 let C:=D*U*R; refine ⟨C,by positivity,fun {c f} G ho T u M F W k hp X Y Z x=> ?_⟩; intro P B
 let V:=fan G ho @T j false M []; let K:=love f (cart f (Tern j M F))*fan G ho @T j true M []; let M':ℝ := G.count.val; let L':= followV [] G.count; let Y':= R*k* lace 2 G.count; have ht: B = Vᴴ*K:=by
    unfold K B; rw [←show (1-P)*love f (cart f F)*P=love f (cart f (Tern j M F)) from winP j m (by omega) M F k Y]; unfold V; simp_rw [Matrix.mul_assoc]
 have hv : ∑ i:Single f, Tap.streak G m i x*‖V i x‖≤ D*(U*(M'^4 * L')):=by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left ((H G ho @T u M).hip x) r.le); rw [Finset.mul_sum]; apply sum_le_sum; intro i _; let E:=arch G (pine j G.count ho @T false M G 1)
    rw [←fan_s G ho @T j u e false M i x]
    rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact L (dish G i x) (Nat.cast_nonneg _)
 rw [ht]; have he:0 ≤ M':= Nat.cast_nonneg _; have hm:0 ≤ Y':=by unfold Y' lace; positivity
 let Q(i:Single f)(y:Single c):=perk m x y
 unfold paidX; simp_rw [Matrix.mul_apply]; calc
   _ ≤ ∑ i:Single f,(Tap.streak G m i x*‖V i x‖)* (∑ y,Tap.streak G m i y * ‖K i y‖):=by
      simp_rw [Finset.mul_sum]; rw [sum_comm]; apply sum_le_sum; intro y _
      have hp0:0≤perk m x y:=by unfold perk; positivity
      refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) hp0).trans ?_; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; rw [norm_mul, Matrix.conjTranspose_apply,norm_star]; refine (mul_le_mul_of_nonneg_right (sting m G x y i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq ?_; ring
   _ ≤ ∑ i:Single f, (Tap.streak G m i x*‖V i x‖)* Y':=by
      apply sum_le_sum; intro i _; exact mul_le_mul_of_nonneg_left (J G ho @T u M F W k X Y Z i) (mul_nonneg (streak_pos ..) (norm_nonneg _))
   _ ≤ D*(U*(M'^4 * L'))*Y':=by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hv hm
   _ = _:=by
      unfold C Y' L' lace followV; change D*(U*(M'^4*(Real.sqrt M'/M'^(0+2:ℕ))))*(R*k*(Real.sqrt M'/M'^(2+2:ℕ)))=D*U*R*k/M'; have hq:0<M':= side_pos _; field_simp; generalize h:Real.sqrt M'=u'; have hl : u'^2=M':=by rw [←h,Real.sq_sqrt he]
      ring_nf; rw [hl]; ring -- tune
end YM.CF.Haro
