import YM.CF.BPress.Hazel.Neon
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
abbrev beacon (v:ℝ):= pen (light z v) ((light_cost z).special _)
abbrev PricesU(K:ℝ≥0)(j: Fin 5): Prop:= LipschitzOnWith K (dict j) (Hotel ×ˢ Meadow.active) ∧ LipschitzOnWith K (neonT j) (Hotel ×ˢ Meadow.active)∧LipschitzOnWith K (beacon j) Hotel
lemma price_O : ∃ K:ℝ≥0, ∀j:Fin 5,PricesU K j:=by
 have he(j:Fin 5):∃ K,PricesU K j:=by
    obtain ⟨K,p⟩:= Smooth.lip_near (isCompact_Icc.prod isCompact_Icc) (f:=dict j) (s:= Hotel ×ˢ Meadow.active) (fun i h=>((dict_s j i h.1).2.of_le (by norm_num))); obtain ⟨L,h⟩:=Smooth.lip_near (isCompact_Icc.prod isCompact_Icc) (f:=neonT j) (s:=Hotel×ˢMeadow.active) (fun _ _=> (neon_smooth j).contDiffAt.of_le (by norm_num)); obtain ⟨u,m⟩:= Smooth.lip_near isCompact_Icc (s:=Hotel) (f:=light j) (fun i h=> (light_cost j).smooth.contDiffAt.of_le (by norm_num)); refine ⟨max (max K L) u,?_⟩; exact ⟨p.weaken ((le_max_left ..).trans (le_max_left ..)),h.weaken ((le_max_right ..).trans (le_max_left ..)), (m.weaken (le_max_right ..))⟩
 choose K h using he; refine ⟨univ.sup K,fun i=>?_⟩; have ht:K i ≤ _:= le_sup (s:= (univ:Finset (Fin 5))) (f:=K) (mem_univ i); exact ⟨(h i).1.weaken ht,(h i).2.1.weaken ht,(h i).2.2.weaken ht⟩
abbrev price₀:= price_O.choose
abbrev priceTone := max price₀ (max Meadow.κ_theme 1)
@[simp] lemma large_P : 1 ≤ priceTone:= le_trans (le_max_right ..) (le_max_right ..)
lemma feed: PricesU priceTone z:= by obtain ⟨p,q,t⟩:= price_O.choose_spec z; exact ⟨p.weaken (le_max_left ..),q.weaken (le_max_left ..),t.weaken (le_max_left ..)⟩
lemma Ω_theme : κ_theme ≤ priceTone:= le_trans (le_max_left ..) (le_max_right ..)
lemma swivel_l (h:E) (A:ℝ→ Op SU.Slot)(p:LipschitzOnWith priceTone A Meadow.active) : LipschitzOnWith priceTone (fun x=>swivelC h (A x)) Meadow.active := by apply LipschitzOnWith.of_dist_le_mul; intro x a y b; rw [dist_eq_norm, Paint.iso,←dist_eq_norm]; exact p.dist_le_mul x a y b
lemma cast_smooth (h:E)(z:Fin 5)(t:ℝ) : ContDiff ℝ ∞ (castN h z t) := (swivel_smooth _).comp ((neon_smooth z).comp (f:=fun x=> (t,x)) (by fun_prop))
lemma d_smooth (h:u∈ Hotel): ContDiff ℝ ∞ (fun v=> dict z (u,v)):= contDiff_iff_contDiffAt.mpr fun i=> ((dict_s z (u,i) h).2).comp i (f:=fun v:ℝ=>(u,v)) (by fun_prop)
lemma o_cost {E:Type*}[PseudoMetricSpace E](x:ℝ×ℝ→E)(u:ℝ)(p:u∈ Hotel)(f:LipschitzOnWith priceTone x (Hotel×ˢ Meadow.active)) : LipschitzOnWith priceTone (fun v=> x (u,v)) Meadow.active :=by apply LipschitzOnWith.of_dist_le_mul; intro i a j b; exact (f.dist_le_mul (u,i) ⟨p,a⟩ (u,j) ⟨p,b⟩).trans (by simp)
lemma cast_healthy(h:E)(p:u∈Hotel): LipschitzOnWith priceTone (castN h z u) Meadow.active:=swivel_l _ _ (o_cost _ _ p (feed z).2.1)
-- depth cost of path parameters difference
lemma safe_h (z:Fin 5){u v t a:ℝ}(p:u∈Hotel)(q:v∈Hotel)(w:t∈ Meadow.active)(e:|u-v| ≤ a) : ‖dict z (u,t)-dict z (v,t)‖≤ priceTone*a ∧ ‖neonT z (u,t)-neonT z (v,t)‖≤ priceTone*a:=by
 have he (x:ℝ×ℝ→Op SU.Slot)(f:LipschitzOnWith priceTone x (Hotel ×ˢ Meadow.active)): ‖x (u,t)-x (v,t)‖≤ priceTone*a:=by rw [←dist_eq_norm]; apply (f.dist_le_mul (u,t) ⟨p,w⟩ (v,t) ⟨q,w⟩).trans; apply mul_le_mul_of_nonneg_left _ priceTone.property; simp [Real.dist_eq,e]
 exact ⟨he _ (feed z|>.1),he _ (feed z|>.2.1)⟩ -- tune

-- depth profile gamma(d'). fixed purchase R^dag after other thresholds. use smooth function bound (∈[0,1]) at scaled clipped. Want $R_H≥8*(R_P+10)$ for gamma(near)=0. Lips.* price_C. Need on d'≤R_H+1. prove on ℕ Lipsonic all d', normalize clipped to1. no smooth for d' beyond R_H needed (micro). gamma cap profile.
namespace Clipγ
abbrev gammaCap (D:Side)(k:ℕ) : ℝ:= ((min k D.val:ℕ):ℝ)/(D.val:ℝ)
abbrev gamma (D:Side)(k:ℕ):= Lute.Kite.bound (gammaCap D k)
lemma light_γ(D:Side)(k:ℕ):gammaCap D k∈ Hotel:=⟨by positivity,(div_le_one (nPos D)).mpr (by exact_mod_cast min_le_right ..)⟩
lemma lit(D:Side)(k:ℕ): gamma D k∈ Hotel:=mid_bound ..
lemma dark {D: Side}{k:ℕ}(f: k*8 ≤ D.val): gamma D k=0:=by apply bound_lo; unfold gammaCap; rw [div_le_div_iff₀ (nPos D) (by norm_num : (0:ℝ)<8),one_mul]; exact_mod_cast (show _ * 8 ≤ D.val from (Nat.mul_le_mul_right _ (min_le_left k D.val)).trans f) -- tune
lemma full {D: Side}{k:ℕ}(f:D.val ≤ k) : gamma D k=1:=by unfold gamma gammaCap; rw [min_eq_right f, div_self (nPos D).ne']; exact bounds01.2
lemma buy :∃ K:ℝ≥0,LipschitzOnWith K Lute.Kite.bound Hotel:=Smooth.lip_near isCompact_Icc (fun _ _=> bound_smooth.contDiffAt.of_le (by norm_num))
abbrev KP:=buy.choose
abbrev chk(D : Side):= (KP:ℝ)/(D.val:ℝ)
lemma γ_neigh {D:Side}{i j:ℕ}(p:i≤ j+1)(q:j≤ i+1): |gamma D i - gamma D j| ≤ chk D:=by
 have h:(min i D.val:ℝ) ≤ (min j D.val:ℝ)+1:= by exact_mod_cast (show min i D.val≤ min j D.val+1 by omega)
 have t:(min j D.val:ℝ) ≤ (min i D.val:ℝ)+1:= by exact_mod_cast (show min j D.val ≤ min i D.val+1 by omega)
 unfold gamma; apply (buy.choose_spec.dist_le_mul _ (light_γ D i) _ (light_γ D j)).trans
 rw [Real.dist_eq, chk,←mul_one_div]; apply mul_le_mul_of_nonneg_left _ KP.property; unfold gammaCap; rw [←sub_div, abs_div,abs_of_pos (nPos D)]; apply div_le_div_of_nonneg_right _ (nPos D).le; rw [abs_le]; push_cast; constructor <;> linarith
end Clipγ
end YM.CF.BPress.Hazel
