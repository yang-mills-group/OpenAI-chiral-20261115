import YM.CF.Cascade.Toll
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
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
local notation "dη"=>Aroma.port
local notation "μN"=> Ember.pinch
lemma angelV (p:0<k)(x:4≤j)(y:4≤t)(L:Side):∃ C:ℝ,0<C∧∃ n:ℕ,∀ (P:Flight j t),P.L=L→∀ N:Side,n≤ N.val→|‖angel k P (dη N) 0‖^2*(L.val:ℝ)^2-1|≤ C/N.val:=by
 obtain ⟨a,A,h,hp,H⟩:=angel_pr p x y; obtain ⟨n,v⟩:= neck (lt_min h (div_pos (inv_pos.mpr (side_pos L)) hp)); let C:=A*Real.pi; let w:=(L.val:ℝ)⁻¹
 have hc:0<C:=mul_pos hp Real.pi_pos; have he:0<w:=by unfold w; positivity
 refine ⟨3*C*L.val,by positivity,n, fun P f N e=>?_⟩
 let V:=angel k P (dη N) 0; have hx:=H P (dη N) (by rw [norm_p]; exact (v N e).trans_le (min_le_left ..)); rw [norm_p,show (P.L.val:ℂ)⁻¹=(w:ℂ) by rw [f]; unfold w; push_cast; rfl] at hx
 have hu : |‖V‖-w|≤C/N.val:=by
    have he:‖(w:ℂ)‖=w:=by simp [abs_of_pos he]
    rw [← he]; apply (abs_norm_sub_norm_le (a:=V) (b:=(w:ℂ))).trans; apply hx.trans_eq; unfold C Ember.pinch; ring
 have hm : C/N.val≤w:=by
    have hk:= (lt_div_iff₀ hp).mp ((v N e).trans_le (min_le_right a _)); apply le_of_eq_of_le _ ((mul_comm _ _).trans_le hk.le); unfold C Ember.pinch; ring
 change |‖V‖^2*(L.val:ℝ)^2-1| ≤ _
 have hv:w*(L.val:ℝ)=1:=inv_mul_cancel₀ (side_pos _).ne'; have hs:‖V‖ ≤ 2*w:=by have he:= (abs_le.mp (hu.trans hm)).2; linarith
 let l:ℝ:= L.val; have hl:0≤l:=Nat.cast_nonneg _
 rw [show ‖V‖^2*l^2-1 = (‖V‖-w)*(‖V‖+w)*l^2 by unfold w l; field_simp; ring, abs_mul,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) he.le),abs_of_nonneg (pow_nonneg hl _)] -- tune expression
 apply ((mul_le_mul_of_nonneg_right (mul_le_mul hu (show ‖V‖+w≤3*w by linarith) (add_nonneg (norm_nonneg _) he.le) (by positivity)) (pow_nonneg hl 2))).trans_eq; unfold w l; field_simp -- tune
lemma boundL (p:0<k)(x:4≤j)(y:4≤t)(L:Side)(h:0<a):∃ C:ℝ,0<C ∧∀ (P:Flight j t),P.L=L→∀ (c f:Side)(u:Ratio c f), u.count=L→3≤card_c c→∀ H:Momentum→ℝ,(∀ q:Momentum,physical q→ |H q| ≤ a*f.val*date f)→ |(∑ i∈(univ:Finset (Site P.L)).erase 0,‖angel k P (dη c) i‖^2 * H (aliasAt (dη c) i)) / base_u c| ≤ C/c.val:=by
 obtain ⟨V,hV,D⟩:= vexp p x y; let C:= ↑(Fintype.card (Site L))* V^2 *(a *L.val *(L.val:ℝ)^4)*Real.pi^2; have hc:0<C:=by unfold C; positivity
 refine ⟨C,hc,fun P v c f U t r H g=>?_⟩; have hp: dη c∈baseCube:=by rw [←mon0 r]; exact mon_mem ..
 let R:= (univ:Finset (Site P.L)).erase 0; let h':ℝ:=L.val; let l:= μN c; let F:=(V*l^2)^2*(a*f.val*date f); have hF:0≤ F:=by unfold F; have hd:= date_pos f; positivity
 have ht(i:Site P.L)(v:i∈R): |‖angel k P (dη c) i‖^2 * H (aliasAt (dη c) i)|≤ F:=by
    rw [abs_mul,abs_of_nonneg (by positivity :0≤ ‖angel k P (dη c) i‖^2)]; apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ?_ _) (g _ (alias_real hp.1 _)) (abs_nonneg _) (by positivity :0≤(V*l^2)^2); exact (D P i (mem_erase.mp v).1 _ hp (by simp [Aroma.port,Ember.spark])).trans_eq (by rw [areaC]) -- tune
 have he:f.val=c.val*L.val:= U.exact_size.trans (by rw [t]); have hm:date f=date c*h'^4:=by unfold date h'; rw [site_card,site_card]; simp [More,he]; ring
 rw [abs_div,abs_of_pos (base_p c),div_le_iff₀ (base_p c)]; apply (abs_sum_le_sum_abs ..).trans; refine (sum_le_sum (fun i hi=>ht i hi)).trans ?_; rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show (R.card:ℝ) ≤ Fintype.card (Site P.L) by exact_mod_cast (card_le_univ R)) hF).trans_eq; unfold F; rw [he,hm,v]; unfold h' C base_u l Ember.pinch; push_cast; field_simp
 -- tune use calc
end YM.CF.Cascade
