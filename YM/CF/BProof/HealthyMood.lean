import YM.CF.BProof.FrameRead

/-! Consequences of the N face tests and license on eq:B-healthy neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Face
open Function SU Lattice Cube Mag Filter Metric Set MeasureTheory Finset
open scoped Matrix.Norms.Frobenius Topology Classical BigOperators
local notation "G" => SU.group
variable {s : Side}
variable (K : Chart G)

/-- multipower delay independent of period. -/
abbrev fine (y : ℝ) := coin y 0 (-1/4) 0

lemma bounds : ∃ C > (0:ℝ), ∀ᶠ y:ℝ in atTop, ∀ (s:Side)(U:Sheet s) p u,
    Mood K y U p u → ∀ i, group.chord (read U p i) ≤ C*mA y := by
 let C:=1+‖B0‖
 have hc:0<C:=lt_of_lt_of_le one_pos (le_add_of_nonneg_right (norm_nonneg _)); have u:= zero_lt_one.trans_le K.C_one
 refine ⟨K.C*C,mul_pos u hc,?_⟩
 filter_upwards [(coin_purchases (a:=0) (b:=-1/8) (c:=0) (by norm_num)).eventually (ge_mem_nhds one_pos)] with y hy
 intro s U p k h i
 let T:=read U p i; let x:= tilt K y U p
 have hz:= (h.1 i).le
 have he : ‖x‖≤C := (norm_le_norm_sub_add x (orbit k)).trans (add_le_add (h.2.2.trans hy) (Mag.turn_norm k⁻¹ B0).le) -- tune
 have hV := K.exposes _ hz
 calc
   _ = group.chord (group.lieExp (logG G T)) := by rw [show group.lieExp (logG G T) =T from hV.2]
   _ ≤ K.C*‖logG G T‖ := K.step _ hV.1
   _ ≤ K.C*(mA y*C) := by
        have hg:=show 0<mA y from coin_pos ..
        apply mul_le_mul_of_nonneg_left _ u.le
        have hi: ‖x i‖≤C:= le_trans (PiLp.norm_apply_le _ i) he -- lookup
        change ‖(mA y)⁻¹ • slog K T‖≤C at hi
        rw [slog_leg _ _ hz,norm_smul,Real.norm_of_nonneg (by positivity)] at hi; exact (inv_mul_le_iff₀ hg).mp hi
   _ = _:=by ring

lemma launch_face {D : ℝ} (hD : 0<D) : ∃ C : ℝ,0<C ∧ ∀ᶠ y:ℝ in atTop,
    ∀ (s:Side)(U:Sheet s)(p : Space s),
      (∀ i, cd G (comm y (f₁ i) (f₂ i)) (read U p i) ≤ D * wc y) →
      ∀ i, Mood K y U p (orient K y U p i) ∧ cd G (orient K y U p i) (center i) ≤ C*fine y := by
 obtain ⟨C, hC,H⟩ := Mag.log_background K D hD
 obtain ⟨u,b,hu,hb,h⟩:= Mag.a_frame
 let k:=3*C; have hk:0<k:=mul_pos (by norm_num) hC
 refine ⟨u*k, mul_pos hu hk,?_⟩
 filter_upwards [H, (coin_budget (a:=0) (b:= -1/4) (e:=0) (f:=0) (c:=0) (d:=0) (by norm_num) k b hb), (coin_budget (a:=0) (b:= -1/4) (e:= -1/8) (f:=0) (c:=0) (d:=0) (by norm_num) k 1 one_pos)] with y H hx hz
 intro s U p hl
 let x:=tilt K y U p
 have he(i):= H i _ (hl i)
 have ht : ‖x-B0‖ ≤ k*fine y:=by
    have hw (i:Fin 3) : ‖(x-B0) i‖≤ C*fine y := by
      change ‖(mA y)⁻¹ • _ - magnetic i‖ ≤ _
      have hU:= show 0 < mA y from coin_pos ..
      rw [slog_leg _ _ (he i).1.le,show (mA y)⁻¹ • logG G (read U p i) - magnetic i=(mA y)⁻¹ • (logG G (read U p i) - mA y • magnetic i) by rw [smul_sub, inv_smul_smul₀ hU.ne'], norm_smul,Real.norm_of_nonneg (by positivity)]
      apply le_trans (mul_le_mul_of_nonneg_left (he i).2 (by positivity)); apply le_of_eq; rw [mul_left_comm,coin_inv,coin_mul]; unfold fine; ring_nf
    have hu:0≤C*fine y:=mul_nonneg hC.le (coin_pos ..).le
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk.le (coin_pos ..).le),PiLp.norm_sq_eq_of_L2]; apply le_trans (b:=∑ _ : Fin 3,(C*fine y)^2) (sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hw i) _); simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; unfold k; change (↑(3:ℕ):ℝ)*(C*fine y)^2≤(3*C*fine y)^2; norm_num; nlinarith only [sq_nonneg (C*fine y)]
 have hr := ht.trans (by simpa using hx.le : k*fine y≤b)
 intro i
 let o:= orient K y U p i
 have hg : orbit o=orbit (lead x):=orient_orbit ..
 obtain ⟨j,hj⟩:=h x hr _ (lead_spec.2 x)
 constructor
 · unfold Mood fits; change inChart K U p ∧ (∀ a, ‖x-orbit o‖≤‖x-orbit a‖)∧‖x-orbit o‖ ≤ allowance y; rw [hg]
   exact ⟨fun i=> (he i).1, lead_spec.2 x, le_trans (lead_spec.2 x 1) (by rw [orbit_one]; exact ht.trans (by simpa using hz.le))⟩
 unfold orient; nth_rw 2 [← mul_one (center i)] -- check
 rw [cd_mul_left]; exact le_trans (near_p K y U p j) (le_trans hj (by rw [_root_.mul_assoc]; gcongr))

lemma label_pass {u v e : E} {i j : Fin 5} {δ η : ℝ}
    (h : cd G u (center i) ≤ δ) (g : cd G v (center j) ≤ δ) (p : group.chord e ≤ η) :
    cd G v (u*e) ≤ cd G (center i) (center j)+2*δ+η ∧ cd G (center i) (center j) ≤ cd G v (u*e)+2*δ+η := by
 have he := cd_triangle G (u*e) u (center i)
 have hh: cd G (u*e) u=group.chord e := by rw [cd_symm]; nth_rw 1 [← mul_one u]; rw [cd_mul_left,cd_one]
 rw [hh] at he
 have hi:= cd_triangle G v (center j) (u*e)
 have ho:= cd_triangle G (u*e) (center i) (center j)
 rw [cd_symm G (center j) _] at hi
 have hp:=cd_triangle G (center i) (u*e) (center j)
 rw [cd_symm G (center i) (u*e)] at hp
 have hq:= cd_triangle G (u*e) v (center j)
 rw [cd_symm G (u*e) v] at hq
 constructor <;> linarith

include K
lemma healthy_link (C B : ℝ) (hc : 0<C) (hb : 0<B) : ∀ᶠ y:ℝ in atTop, ∀ (u v e : E)(i j : Fin 5)(n : Fin 3),
    cd G u (center i) ≤ C*fine y → cd G v (center j) ≤ C*fine y → cd G (bg y n) e ≤ B*wc y →
    (Follow y u v e ↔ i=j) := by
 obtain ⟨D,hD,H⟩:= pay K
 obtain ⟨c,hk,h⟩:= separates
 filter_upwards [H, coin_budget (a:=0) (d:=0) (c:=0) (f:=0) (b:= -1/4) (e:= -1/8) (by norm_num) (2*C) (1/4) (by norm_num), coin_budget (a:=-1/4) (b:=3/8) (d:=0) (e:= -1/8) (c:=0) (f:=0) (by norm_num) D (1/4) (by norm_num), coin_budget (a:=-1/2) (b:=1/2) (d:=0) (e:= -1/8) (c:=0) (f:=0) (by norm_num) B (1/4) (by norm_num), (coin_purchases (a:=0) (b:= -1/8) (c:=0) (by norm_num)).eventually (gt_mem_nhds (show 0<c/2 from half_pos hk))] with y H hx hz hu hk'
 change 2*C*fine y<_*allowance y at hx; change D*aA y<_*allowance y at hz; change B*wc y<_*allowance y at hu; change allowance y<_ at hk'
 intro u v e i j n ha hv he
 have hp : group.chord e ≤ D*aA y+B*wc y := by rw [← cd_one]; exact (cd_triangle G 1 (bg y n) e).trans (add_le_add (H.1 n) he)
 obtain ⟨b,a⟩:= label_pass ha hv hp; unfold Follow; constructor
 · intro g; by_contra ht; have V:= h i j ht; linarith [show 0<allowance y from coin_pos ..]
 rintro rfl; rw [cd_self] at b; linarith [show 0<allowance y from coin_pos ..]
end YM.CF.BProof.Face
