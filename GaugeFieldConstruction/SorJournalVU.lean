import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Mass
/-! Subpower means. upgrade some budgets to ANY R.On real.J.Keep asympt sup. -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
abbrev FuelVU (w t : ℝ):ℝ:= Real.exp (t*w)
abbrev TonalVU (f:Grouping)(w: Axis→ℝ)(s:ℝ):Grouping:=fun i=> width (FuelVU (w i) s) (f i)
def RealBudgetVU (δ:ℝ)(f:ℝ→ℝ):=∃ C:ℝ,0≤C ∧ ∀ᶠ u in atTop, ‖f u‖ ≤ C*FuelVU δ u
-- bandwidth comparison
lemma descentVU (w:ℝ)(n:ℕ)(t:ℝ)(h:(n:ℝ)≤t)(e:w≤0): FuelVU w t ≤ fuel w n :=Real.exp_le_exp.mpr <| mul_le_mul_of_nonpos_right h e
lemma boundFuelVU (w:ℝ)(n:ℕ)(t:ℝ)(h:t ≤ (n:ℝ)+1)(e:w≤0): Real.exp w*fuel w n≤FuelVU w t:=by
 rw [fuel,← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
lemma ceilingFuelVU (w:ℝ)(t:ℝ)(ht:0≤t): fuel w ⌊t⌋₊ ≤ Real.exp |w| * FuelVU w t:=by
 rw [FuelVU,← Real.exp_add]; apply Real.exp_le_exp.mpr
 by_cases h:w≤0
 · rw[abs_of_nonpos h]; nlinarith [Nat.self_sub_floor_lt_one t] -- tune
 rw [abs_of_nonneg (le_of_not_ge h)]; nlinarith [Nat.floor_le ht]
lemma spanBudgetVU (v:ℝ) (f:ℝ→ℝ) (C:ℝ)(p:0≤C)(g:ℕ→ℝ)(h:Budget v g) (e:∀ t:ℝ,0≤t→ |f t| ≤ C*‖g ⌊t⌋₊‖): RealBudgetVU v f:=by
 obtain ⟨x,hx,hg⟩:=h; refine ⟨C*x*Real.exp |v|,by positivity,?_⟩; filter_upwards [(tendsto_nat_floor_atTop (α:=ℝ)).eventually hg,eventually_ge_atTop 0] with t ht hu; apply (show ‖f t‖ ≤ _ from e _ hu).trans
 calc
    _ ≤ C*(x*fuel v ⌊t⌋₊):= mul_le_mul_of_nonneg_left ht p
    _= C*x*fuel v ⌊t⌋₊:=(mul_assoc ..).symm
    _≤ C*x*(Real.exp |v| * FuelVU v t):= mul_le_mul_of_nonneg_left (ceilingFuelVU v t hu) (mul_nonneg p hx)
    _ =_:=(mul_assoc ..).symm
lemma roomNormVU (f: Profile)(h: Ends f)(w:ℝ)(hw:w≤0): ∃ g: Profile,Plus g ∧ Ends g ∧ Reflects false g ∧ ∀ t:ℝ,0≤t→∀ p:ℝ,
      ‖width (FuelVU w t) f p‖≤width (fuel w ⌊t⌋₊) g p :=by
 obtain ⟨R,hR⟩:=h.room
 let C := SchwartzMap.seminorm ℝ 0 0 f
 let v:= max R 1
 let g:= (v*(C*(Real.exp (-w)))) • width v center
 have ha:0≤C:=apply_nonneg _ _
 have hc:0 < v:= lt_of_lt_of_le zero_lt_one (le_max_right ..)
 have hk:Plus g:= (center_plus.tall _ hc.le).scale _ (by positivity)
 refine ⟨g,hk,(center_ends.width _).scale _,(center_even.tall _).scale _,fun t ht p=>?_⟩
 let i:=⌊t⌋₊; let B:= fuel w i; let E:=FuelVU w t
 have hb: 0<B:=fuel_pos ..; have he:0<E:=Real.exp_pos _
 have hs:E≤B:=descentVU _ _ _ (Nat.floor_le ht) hw
 have hW:Real.exp w*B≤E:=boundFuelVU _ _ _ (by dsimp only [i]; linarith [Nat.self_sub_floor_lt_one t]) hw
 change ‖width E f p‖ ≤ width B g p
 by_cases h:f (p/E)=0
 · rw [width_at,h,mul_zero,norm_zero]; exact hk.tall B hb.le p
 have hu:|p/E|≤v:= (hR _ h).trans (le_max_left ..)
 have hz:|p/B/v|≤ 1:=by rw[abs_div,abs_div,abs_of_pos hb,abs_of_pos hc,div_le_one hc,div_le_iff₀ hb]; rw [abs_div,abs_of_pos he,div_le_iff₀ he] at hu; exact hu.trans (mul_le_mul_of_nonneg_left hs hc.le)
 rw [width_at,width_at]; unfold g; rw [_root_.smul_apply,width_at,center_plane _ hz,norm_mul,Real.norm_of_nonneg (inv_pos.mpr he).le]
 apply (mul_le_mul_of_nonneg_left (f.norm_le_seminorm ℝ _) (inv_pos.mpr he|>.le)).trans
 have hr:= inv_anti₀ (show 0<Real.exp w*B from mul_pos (Real.exp_pos w) hb) hW
 apply (mul_le_mul_of_nonneg_right hr ha).trans_eq
 rw [Real.exp_neg]; change _= B⁻¹*(v*_*(v⁻¹*1)); rw [mul_inv]; field_simp
lemma totalNormVU (Q:Finset Axis)(f: Grouping)(h:∀ i∈Q, Ends (f i))(w:Axis→ℝ)(hw:∀ i∈Q,w i≤0): ∃ g:Grouping, Colors Finset.univ g ∧ ∀ t:ℝ,0≤t→∀ p:E4, |crop Q (TonalVU f w t) p|≤ crop Q (mails w g ⌊t⌋₊) p:=by
 have hi i : ∃ g: Profile, Plus g ∧ Ends g ∧ Reflects false g ∧ (i∈Q→∀ t:ℝ,0≤t→∀ p:ℝ,‖TonalVU f w t i p‖ ≤ width (fuel (w i) ⌊t⌋₊) g p):=by
    by_cases hv:i∈Q; · obtain ⟨g,x,y,z,h⟩:=roomNormVU (f i) (h i hv) (w i) (hw i hv); exact ⟨g,x,y,z,fun _ =>h⟩
    exact ⟨center,center_plus,center_ends,center_even,fun h=>(hv h).elim⟩
 choose g hg e y u using hi; refine ⟨g,fun i _=>⟨e i,hg i,y i⟩,fun t ht p=>?_⟩
 change ‖crop _ _ _‖ ≤ crop _ _ _; unfold crop; rw[norm_prod]; exact Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i hi=> u i hi t ht (p i))
-- need ∃ opposite sign for line.P
lemma mixedAliveVU (l:Axis)(e:Axis→Bool)(h:Mixed (other l) e):∃ i∈other l,e i≠e l:=by
 obtain ⟨i,hi⟩:= exists_ne l; by_cases he:e i=e l
 · obtain ⟨j,hj,hh⟩:=h i (apart hi); exact ⟨j,hj,he ▸ Ne.symm hh⟩
 exact ⟨i,apart hi,he⟩
#print axioms totalNormVU
end YM.NSF.Outer
end
