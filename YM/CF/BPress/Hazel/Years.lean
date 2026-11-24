import YM.CF.BPress.Hazel.Verdant
import YM.CF.BPress.Hazel.Shelter
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth} (z: Fin 5)
open Grid Wealth Locale Tunnel Bands Branch Clipγ Letter
-- geometry purchases chronology. $mesh X independent of $D,f$. choose B.blank later from P.L of schedule; choose needed large D. σ cap separately.
namespace Chrono
variable {ε q d m:ℝ} (r:Side)
abbrev η (q:ℝ):= q/8
abbrev earth(r:Side):= climate r / sphereRate
lemma earth_p:0<earth r:=div_pos (inv_pos.mpr (by positivity)) sphereRate_cost.positive
lemma pWeight(h:d≤earth r):sphereRate*d ≤ climate r:=by obtain z:=sphereRate_cost.positive; rw [mul_comm]; exact (le_div_iff₀ z).mp h
abbrev fruition(r:Side):= soil r
lemma moist(h:0< ε)(p:0<q) :∃ r:Side, Poses r ε (η q):= seed_capacity _ _ h (by unfold η; positivity)
def lease(r:Side)(q:ℝ)(D:ℕ): Prop:= (priceTone:ℝ)*(D:ℝ)⁻¹ < min (fruition r) (η q)
lemma widthQ (t:0<q): ∀ᶠ n:ℕ in atTop, lease r q n:=by
 have he:= (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (priceTone:ℝ); rw [mul_zero] at he; exact he.eventually (gt_mem_nhds (lt_min (by unfold fruition soil; positivity) (by unfold η; positivity))) -- tune
-- permissible prechoices with any bound d & blank. q>0 actual Worthy, can lower.
lemma boxing (k:ℕ) (t:0<q)(blank:Side) : ∃ G:GapSize,G.blank=blank ∧ k≤ G.collar ∧ lease r q (G.select 1).D:=by
 have he:= widthQ r t; obtain ⟨N,H⟩:= eventually_atTop.1 he; let D:=k+N; let B:GapSize:=⟨blank,D*blank.val,dvd_mul_left ..⟩; have ht:D≤ B.collar:=Nat.le_mul_of_pos_right _ blank.property
 exact ⟨B,rfl,by omega,(H _ (by rw [GapSize.D_select]; unfold D at ht; omega))⟩ -- tune
abbrev Ringmark:ℝ := (rangP+1)/2
abbrev heat :ℝ:= (1-Ringmark)/100
lemma deepC : 0 ≤ rangP ∧ rangP < Ringmark ∧ Ringmark <1:= ⟨capZ.1.le,by unfold Ringmark; linarith [capZ.2.1], by unfold Ringmark; linarith [capZ.2.1]⟩
lemma solid : 0 < heat∧ heat≤ Ringmark:=by unfold heat; constructor; linarith [deepC.2.2]; unfold Ringmark; linarith [deepC.1] -- tune
-- rental purchase of gamma profiles AFTER R.U & P, R_M can stretch arbitrarily
structure Buoyant (r:Side)(q:ℝ)(W:Rental):Prop where
 focus : (2*r.val+1)*8 ≤ W.T.val
 matureH : priceTone * chk W.H < η q
 matureT : η q + priceTone * (chk W.T*3) ≤ q
private lemma wHop (r:Side)(h:0<q)(A:ℝ)(l:ℕ):∃ d:Side,l≤d.val∧priceTone*(chk d*A) <q:=by
 have he:= ((tendsto_inv_atTop_zero.comp ((tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R:=ℝ))))).const_mul (KP:ℝ)); have ht:= (he.mul_const A).const_mul (priceTone:ℝ); rw [mul_zero,zero_mul,mul_zero] at ht; obtain ⟨i,h,u⟩:= ((eventually_ge_atTop l).and (ht.eventually (gt_mem_nhds h))).exists; refine ⟨⟨i+1,by omega⟩, Nat.le_succ_of_le h,?_ ⟩; unfold chk; rw [div_eq_mul_inv]; show (priceTone:ℝ)*(↑KP *(↑(i+1))⁻¹*A)<_; rw [Nat.cast_add,Nat.cast_one]; exact u -- tune let annotation
lemma leap (n m l:ℕ)(h:0<q): ∃ W:Rental, W.P=n ∧ m+6 ≤ W.U ∧ l≤ W.M ∧ Buoyant r q W:=by
 have hu:η q< q:=by unfold η; linarith
 obtain ⟨H,w,t⟩:= wHop r (q:=η q) (by unfold η; positivity) 1 ((n+1)*8); obtain ⟨T,g,t'⟩:= wHop r (sub_pos.mpr hu) 3 ((2*r.val+1)*8); let u:=m+6+H.val+2; refine ⟨⟨H,n,u,T, (u+T.val+n+2)+l,w,by unfold u; omega,Nat.le_add_right ..⟩,rfl,show m+6 ≤ u from (by unfold u; omega),Nat.le_add_left .., g, by simpa only [mul_one] using t,?_⟩; change η q+priceTone*(chk T*3) ≤ q; linarith only [t']
structure StageC (r:Side)(q δ:ℝ)(W:Rental)(B:BandWidth)(c:ℝ):Prop where
 speeds : Speed B W (soil r) (η q) c
 wage : c ≤ δ
 bear : μH*c ≤ δ
 radiusC : μH*c+ rangP ≤ Ringmark
lemma StageC.drop {δ₀ c z :ℝ}{W:Rental}{B:BandWidth}(h:StageC r q δ₀ W B c)(t:z≤c): StageC r q δ₀ W B z:=by
 have he:=sphereRate_cost.positive; have v:μH*z≤μH*c:= mul_le_mul_of_nonneg_left t (by unfold μH; positivity); exact ⟨⟨le_trans (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t he.le) (by norm_num)) le_rfl) h.speeds.gapG, le_trans (add_le_add (mul_le_mul_of_nonneg_right v (by norm_num)) le_rfl) h.speeds.gapH⟩,t.trans h.wage,v.trans h.bear, (add_le_add v le_rfl).trans h.radiusC⟩ -- tune "use" reserved?
lemma stage_γ (G:GapSize) {W:Rental}(h:Buoyant r q W)(A H:ℝ)(δ:ℝ)(p:lease r q (G.select 1).D)(t:0<δ) : ∀ᶠ y:ℝ in atTop, StageC r q δ W (G.select y) (price_p A H y) := by
 let φ:= levD (G.select 1); have ht:= (price_npl A H).drop; have hc:Tendsto (fun y=> sphereRate*price_p A H y*3+φ) atTop (𝓝 φ):= by simpa only [mul_zero,zero_mul,zero_add] using (((ht.const_mul sphereRate).mul_const 3).add_const φ)
 let ζ:=max φ (priceTone*chk W.H); have he:=ht.const_mul μH; rw [mul_zero] at he; have hu:= (he.mul_const 3).add_const ζ; rw [zero_mul,zero_add] at hu; filter_upwards [hc.eventually (ge_mem_nhds ((lt_min_iff.mp p).1)),hu.eventually (ge_mem_nhds (max_lt (lt_min_iff.mp p).2 h.matureH)), ht.eventually (ge_mem_nhds t), he.eventually (ge_mem_nhds t), he.eventually (ge_mem_nhds (sub_pos.mpr deepC.2.1))] with y b c l u e; change μH * _ ≤ _ at e; exact ⟨⟨b,c⟩,l,u,by linarith⟩
lemma duskY (G:GapSize)(W:Rental):∀ᶠ y in atTop,W.M≤Warm (G.select y):=by filter_upwards [G.marked_late.eventually_ge_atTop ((W.M*10:ℕ):ℝ)] with y h; unfold Warm; apply Nat.le_div_iff_mul_le (show 0<10 by norm_num) |>.2; exact_mod_cast h
end Chrono
open Chrono Pressure
variable {R:Hangar s}{X:Bands s B}{S:Seal (SiteX X R)} -- misorder S before X
variable {W:Rental}{H:Letter X}{U : Micro s}{r r' χ:Side}{K: Record r s}{c d q q':ℝ} (t:StageC r q d W B c)(u:Buoyant r q W)
include t u
theorem legit (g:Poses r q' (η q))(p:0≤ q)(L:Grip X W R S H U (soil r) (η q) c)(K:Record r s)(v: Rings U univ (climate r)): Stopped H K.key L q' q:=by
 have he: η q≤q:=by unfold η; linarith;
                                                                                                                                                                           --
 exact ⟨rfl,le_rfl,by unfold cloakT; rw [Record.K]; exact u.focus, t.speeds,g.1,g.2.trans he,u.matureT,v⟩ -- tune
end YM.CF.BPress.Hazel
