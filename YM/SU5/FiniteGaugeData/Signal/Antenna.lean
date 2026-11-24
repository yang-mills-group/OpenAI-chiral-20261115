import YM.SU5.FiniteGaugeData.Signal.Dressing
import YM.SU5.FiniteGaugeData.Signal.OceanPort
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea Supplies
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
namespace Sparkle
variable {N:Side}{a b u v:ℝ}{i j d k:ℕ}
open OrbitPort LocalPlane Retain

private lemma marks {α:Type*}[Fintype α](U:α↪ Site N) (f: Site N→ℝ) {s:ℝ} (t:0 ≤ s)(h:∀ i,s ≤ f (U i)): Fintype.card α *s^2 ≤ ∑ j:Site N,f j^2 :=by
 apply le_trans (b:=∑ j∈ (univ:Finset α).map U, f j^2); · rw [sum_map,←nsmul_eq_mul,←card_univ,←sum_const]; exact sum_le_sum (fun i _=>pow_le_pow_left₀ t (h i) _)
 apply sum_le_sum_of_subset_of_nonneg (subset_univ _); exact fun _ _ _=>sq_nonneg _
lemma pmBound (u:Site N) : Bound Real.pi (pm u):= by
 apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr; intro a; change ‖principal (u a)‖ ≤ _; rw [Real.norm_eq_abs,abs_le]; exact ⟨(inZone _).1.le,(inZone _).2⟩

theorem countScale (j:ℕ)(h:1≤j): ∃ C:ℝ,0<C∧ ∀ᶠ N:Side in atTop, Even N.val → Pad j N ∧ ∀ (M:Jill.Male)(x:Ket SpinIdx)(v:Site N)(l:Slot), C*‖x‖^2 ≤ ‖acts (funde j M N 1) (capsule v l x)‖^2:=by
 obtain ⟨r,s,t,p,E⟩:=zip h; obtain ⟨v,W⟩:=gave j h; let a:= r*(Real.pi/4)^2; let b:= min 1 (Real.sqrt a); let d:= b/8; have hx:0<b:= lt_min zero_lt_one (by unfold a; positivity); have ht:0<d:=div_pos hx (by norm_num)
 let l:= d/4/ Real.sqrt s; have hL:0<l:=by unfold l; positivity
 obtain ⟨u,f,g⟩:=funded l hL; let C:=u⁻¹^4*(d/2)^2; refine ⟨C,by unfold C; positivity,?_⟩; filter_upwards [g,eventually_ge_atTop (⟨v+16,by omega⟩:Side)] with n hn v' h0; change v+16 ≤ n.val at v'; obtain ⟨k,d',d₂,b'⟩:= hn; have hb:b≤1:=min_le_left ..; have hf:= W n h0 (by omega)
 refine ⟨hf,fun M x v t'=>?_⟩; rw [nightly M hf, receipt]; let P(z:Site n):= ‖acts (bar j M.val (tmap (pm z))) x‖; let l':=d/2*‖x‖; have hi: (k:ℝ)^4*l'^2 ≤ ∑ i:Site n,P i^2:=by
   rcases le_total ‖acts (1-Aop) x‖ (d*‖x‖) with H|H
   · have HE := show n.val/4+k ≤ n.val by omega
     let J:=grid (N:=n) (k:=n.val/4) (d:=k) HE; have ht2(i:Axis→Fin k): a≤ disk j M (pm (J i)):= calc
       _ ≤ r*‖pm (J i)‖^2:= by unfold a; gcongr; exact frame_high d' (by omega) i
       _ ≤ _:= (E M _ (pmBound (J i))).1
     have hp:b^2≤a:= (pow_le_pow_left₀ hx.le (min_le_right ..) 2).trans_eq (Real.sq_sqrt (show 0 ≤ a from by unfold a; positivity))
     refine le_trans ?_ (marks J P (show 0 ≤ l' from by unfold l'; positivity) (fun i=> (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (show d≤b from (by unfold d; linarith)) (by norm_num : (0:ℝ) ≤ 2)) (norm_nonneg x)).trans (forecast j a d b hx hb hp ht.le (by unfold d; linarith) M _ (pmBound _) (ht2 i) x H)))
     simp [Axis]
   have HE:= show 0+k ≤ n.val by omega
   let J:= grid HE; have ht2(i:Axis→Fin k): disk j M (pm (breadth n 0 k i)) ≤ (d/4)^2:= (E M _ (pmBound (breadth n 0 k i))).2.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ((frame_low (by omega : 4*k≤ n.val) i).trans d₂) 2) p.le).trans_eq (by unfold l; rw [div_pow,Real.sq_sqrt p.le]; field_simp)) -- ℝ rational
   refine le_trans ?_ (marks (N:=n) (grid (N:=n) HE) P (show 0≤l' from by unfold l'; positivity) (fun i=> temper j d ht (show d≤1 by unfold d; linarith) M (pm (breadth n 0 k i)) (pmBound _) (ht2 i) _ H)); simp [Axis]
 let y:= (n.val:ℝ); have hy:0<y:= nPos n; apply le_trans ?_ (mul_le_mul_of_nonneg_left hi (pow_nonneg (inv_nonneg.mpr hy.le) 4)); have hz: u⁻¹ ≤ y⁻¹*k:=by field_simp; linarith only [b']
 change C * _ ≤ y⁻¹^4* _; apply le_trans ?_ (show ((y⁻¹*k)^4)* (d/2)^2*‖x‖^2≤_ from le_of_eq (by unfold l'; ring)); unfold C; gcongr
end Sparkle
end YM.CF.Signal
#print axioms YM.CF.Signal.Sparkle.countScale
