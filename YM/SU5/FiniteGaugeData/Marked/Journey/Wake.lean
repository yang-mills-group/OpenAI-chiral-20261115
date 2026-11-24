import YM.SU5.FiniteGaugeData.Marked.Journey.Diamond

/-! # Norm control, explicit version also with UNMERGED normalized charges.
In the direct extraction we transfer convergence from the partner to sharp
by the fixed-*sup* estimate (`thaw`). It suffices, also for the L1
equicontinuity of the *limit*. We can, however, also keep explicitly the
local L1 tariff and the joint-link L1 norm interpretation on the actual
finite sharp readings: here prove them on the FiniteGaugeData actual-first election.
No new sequencers.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Py Heat

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
    (s :ℕ) {i k:ℕ}(p:Ferry Y s i k)
local notation "K"=> tent Y h
local notation "ν"=> momentm Y i s
local notation "τ"=> side Y i s
local notation "ρ"=> (Y.voyage i).CapeT s
local notation "λ₀"=> deltaL Y h i s
local notation "Γ"=> LocalLimit.Donor.divisionBill Y.meter Λ.C Y.τ s (Y.ivory k) (Y.ir i)

-- upgrade thaw to a bound relative to native cash (allow any Mark, Borel
-- suffices, not even necessarily chirally localized).
include p
lemma awaken (g:Buffered.Mark ((K).c ν))(w:Envelope g):
    ‖listen Y h i k s g-collector Y h i k p.depth s g‖ ≤ Γ * cash λ₀ g := by
  let f:=send Y h i s g
  suffices hv: ‖compass Y i k s f-solder Y i k p.depth s f‖ ≤ Γ*cash ρ f by
    change _ ≤ _
    have e:cash ρ f=cash λ₀ g:= @castCash _ _ (terrain Y h (Y.ir i) s) g _
    rw [←e]; exact hv
  let F:=f ∘ drawn ρ
  let X:=((Y.voyage i).X (Y.uv k)).gram s
  let Z:=((Y.voyage i).Q k p.depth).gram s
  change ‖Marks.ratio Λ.V Λ.U X ρ F-Marks.ratio Λ.V Λ.U Z ρ F‖ ≤ _
  have hf:Measurable ρ:= ((Y.voyage i).ownership s).paid.bill
  let A:= ratioField Λ.V X ρ Λ.U; let B:=ratioField Λ.V Z ρ Λ.U
  have he x:‖A x-B x‖ ≤ Γ:=p.fire.ratio_transfer x
  have ht:Envelope f:= castEnv (terrain Y h (Y.ir i) s) w
  have ha:= mark_integrable hf ht (Marks.can_evaluate Λ.V Λ.U _ _ p.fire.priceA) -- tune
  have hb:= mark_integrable hf ht (Marks.can_evaluate Λ.V Λ.U _ _ p.fire.priceH)
  rw [Marks.normalized,Marks.normalized]
  change ‖markedRead f ρ A-markedRead f ρ B‖ ≤ _
  unfold markedRead cash
  change ‖(∫ x,letterRead (f (drawn ρ x)) _ ∂city _)-(∫ x,letterRead (f (drawn ρ x)) _ ∂city _)‖ ≤ _
  rw [←integral_sub ha hb,←integral_const_mul]
  refine (norm_integral_le_integral_norm ..).trans (integral_mono_of_nonneg (Eventually.of_forall (fun _=>norm_nonneg _)) ((cashable hf ht).const_mul Γ) ?_)
  apply Eventually.of_forall; intro x
  change ‖letterRead (F x) (A x) - letterRead (F x) (B x)‖ ≤ Γ*_
  rw [←map_sub]
  exact (mark_bound ..).trans ((mul_le_mul_of_nonneg_left (he x) (norm_nonneg _)).trans_eq (mul_comm ..))
where
 castCash{m n:Side}(h:m=n)(f:Mark m)(l:Loom n):cash l (show Mark n from h ▸ f)=cash (show Loom m from h.symm ▸ l) f:=by subst n; rfl
 castEnv{m n:Side}{f:Mark m}(h:m=n)(v:Envelope f): Envelope (show Mark n from h ▸ f):=by subst n; exact v


variable (S:Finset Cover)
omit p
/-- Some uniform charges for all paid periods, don't need to thin even
periods or cutoffs, no `W`. On actual wide marked readings. -/
lemma Homes : ∃ D:ℝ, 0<D ∧ ∀ᶠ k:ℕ in atTop, ∀ i:ℕ,(Y.voyage i).kick ≤ k →
    let m:=momentm Y i s
    ∀ f:Mark ((tent Y h).c m), AtSupport false (S.image (wrap (More ((tent Y h).c m)))) f →
      ‖listen Y h i k s f‖ ≤ D * cash (deltaL Y h i s) f := by
  let Z:=duetCharge Y s
  obtain ⟨x,v,d⟩:= albums K S Z
  obtain ⟨A,H⟩:= eventually_atTop.mp ((momentum Y s).eventually d); let U:=Z*((momentm Y A s).val:ℝ)^4
  let D:=max x (Real.exp U); have hx:0<D:= lt_of_lt_of_le v (le_max_left ..)
  refine ⟨1+D,by positivity,?_⟩
  filter_upwards [ferry_all Y s, Y.UV.tendsto_atTop.eventually (LocalLimit.Donor.shrinks (T:=Y.meter) (C:=Λ.C) («τ»:=Y.τ) s Λ.b (by norm_num: (0:ℝ)<1))] with k v BV i u m f t
  have P':= v _ u; let R:=deltaL Y h i s; let a:= collector Y h i k P'.depth s; let X:= listen Y h i k s
  have he:= boxprice Y h i k P'.depth s P'.fire P'.enters
  have hk:‖a f‖≤ D * cash R f :=by
    rcases le_total A i with ha | ha
    · exact (H i ha R a he f t).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (cash_nonneg ..))
    refine (he.tally f t.env).trans (mul_le_mul_of_nonneg_right ((Real.exp_le_exp_of_le ?_).trans (le_max_right ..)) (cash_nonneg ..))
    have hx: (momentm Y i s).val ≤ (momentm Y A s).val:= (raised Y s).monotone ha
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hx) 4) (duetCharge_nn Y s)
  have hw:‖X f-a f‖ ≤ 1*cash R f:= (awaken Y h s P' f t.env).trans (mul_le_mul_of_nonneg_right (BV _ ((Y.voyage i).domain k u)) (cash_nonneg ..))
  exact (norm_sub_norm_le (X f) (a f)|>.trans hw |> sub_le_iff_le_add.mp).trans ((add_le_add_right hk _).trans_eq (add_mul ..).symm)

lemma Dab (u:Chorus)(x:Bracket S u):∃ D:ℝ,0<D ∧ ∀ᶠ i:ℕ in atTop, ∀ᶠ k:ℕ in atTop,∀ f:Purse S,‖sharp Y h s i k (note (tent Y h) f.val u)‖ ≤ D*Touch S l f.val:=by
  obtain ⟨D,d,H⟩:= Homes Y h s S; refine ⟨D,d,?_⟩
  filter_upwards [(momentum Y s).eventually (awning S K l)] with i t
  filter_upwards [H,eventually_ge_atTop (Y.voyage i).kick] with k hk v f
  refine (hk i v _ (x.harmony ▸ (note_t (tent Y h) u f.property x.tines).support (momentm Y i s))).trans ?_
  refine mul_le_mul_of_nonneg_left ((youth_limit Y h s i S f.property).trans ?_) d.le
  exact t _ (move_law Y h i s) (launch_toes Y h s i) _ f.property

/- Joint-link--even-matter reading with fixed matter part (including its
variation as a functional of all bounded Borel coefficients; unlike L∞ norm
continuity of the coefficient, relative to `Touch`).
No assertion of norm convergence in the space of measures. -/
variable {m n:ℕ→ℕ}
variable {I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
lemma ultimate (V:Universal Y h m n I E)(u:Chorus)(x:Bracket S u):∃ D:ℝ,0<D ∧ ∀ f:Purse S,‖E s (note (tent Y h) f.val u)‖ ≤ D*Touch S l f.val:=by
  obtain ⟨D,d,p⟩:= Dab Y h s S u x; refine ⟨D,d,fun f=>?_⟩
  have z:= V.together s (note K f.val u) ⟨⟨S,x.harmony ▸ note_t K u f.property x.tines⟩,by simp⟩
  apply le_of_tendsto z.periods.norm
  filter_upwards [V.pick.grow_i.tendsto_atTop.eventually p] with i t
  apply le_of_tendsto (z.inner (m i)).norm
  exact V.pick.grow_k.tendsto_atTop.eventually (t.mono fun k h=> h f)
end YM.CF.Buffered.Afterglow.Journey
#print axioms YM.CF.Buffered.Afterglow.Journey.Homes
