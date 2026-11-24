import YM.CF.Vp929.Ladder.Exponent

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L)
variable {d h x : ℝ} {D : ℝ → ℝ} {m N B : Side} {U : Grasp V.U B d} (W : GivenX V U) (J : Robes N V W) (N0 : ℕ)
lemma grant_music : ∃ (z : ℝ) (M : ℕ), 0<z ∧ ∀ {m : Side}, M ≤ m.val → ∀ k (A : V.L.Last U W.C m k), A.music z := by
  obtain ⟨z,p,M,H⟩:= sum_cost V.up V.gate V.note V.sp W.pearl V.a_o V.b_o V.d_o W.health V.tallX V.L W.C; exact ⟨z,M,p,@H⟩
lemma move_pay (z : ℝ) {k : ℕ} (A : V.L.Last U W.C m k) (p : A.music z) {i : ℕ} (e : i<k) :
    |A.move i| ≤ K.top.drift + billX R.L + z + |billC R.L| := by
  have ht: |A.shift i-billC R.L| ≤ z := by simpa using p i 1 e
  let a:= V.L.charge (k-1-i); have he : |a + billX R.L| + 1 ≤ K.top.drift:= V.L.bound _; unfold Gold.Last.move
  have h₁:= abs_sub (a+billX R.L) (billX R.L); rw [add_sub_cancel_right,abs_of_nonneg (Vale.pitch R.L)] at h₁; have h₂:= abs_add_le (A.shift i-billC R.L) (billC R.L); rw [sub_add_cancel] at h₂; refine (abs_add_le ..).trans ?_; linarith
lemma big (c : ℕ) : ∀ᶠ x : ℝ in atTop, c ≤ grainZ V W N0 x := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop c] with x hx; change _ ≤ radiusB x at hx; unfold grainZ; have : (1+radiusB x)≤ (100+N0)*(1+radiusB x) := Nat.le_mul_of_pos_left _ (by omega); omega
lemma tiny_size : ∀ᶠ x : ℝ in atTop, ∀ m : Side, grainZ V W N0 x ≤ m.val → commonQ R B m 0 ≤ Real.exp (-(R.L.val:ℝ)) := by
  let E:= Real.exp (-(R.L.val:ℝ)); have he:0<E:= Real.exp_pos _; obtain ⟨n,hn⟩:= exists_nat_gt (Real.pi/E)
  filter_upwards [big V W N0 n] with x p m hm; unfold commonQ; rw [pow_zero,div_one,div_le_iff₀ (by positivity)]
  have hx:n≤ (mid m B).val := (p.trans hm).trans (by change _≤ m.val*2*B.val; exact (le_trans (Nat.le_mul_of_pos_right _ two_pos) (Nat.le_mul_of_pos_right _ B.property)))
  exact (le_of_lt ((div_lt_iff₀ he).1 (lt_of_lt_of_le hn (show (n:ℝ) ≤ (mid m B).val from by exact_mod_cast hx)))).trans_eq (mul_comm ..)
abbrev Toned (L : Side) (x : ℝ) := ∀ i, Rue.IsleB SU.group (temp (hat L x i))
/-- Usable Months even include paying all smaller authorized meshes not used in the ladder. -/
structure Usable (z d0 : ℝ) (T : Month x 1 6 2 N0 V W) : Prop where
  walk : Walker T J z d0 D
  native (m : Side) : T.q ≤ m.val → commonQ R B m 0 ≤ Real.exp (- (R.L.val:ℝ))
  music₀ : 8*W.z ≤ x
lemma usable {M : ℕ} {z d0 : ℝ} (u : Chill_v D) (t : ∀ᶠ x in atTop, 0 ≤ D x) (p : ∀ {m : Side}, M ≤ m.val → ∀ k (A : V.L.Last U W.C m k), A.music z) :
    ∀ᶠ x in atTop, Toned R.L x → ∃ T : Month x 1 6 2 N0 V W, Usable (D:=D) V W J N0 z d0 T := by
  have he : 0 < billX R.L := mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1<R.L.val by have he:=V.tallX; omega)))
  obtain ⟨n,tq⟩:= eventually_atTop.mp ((eventual_prices (R:=R) he u t).and ((sizeK.tempo R.L).spine.eventually (ge_mem_nhds J.ht)))
  let C:= K.top.drift+billX R.L+z+|billC R.L|+billX R.L/512
  filter_upwards [eventually_ge_atTop n,eventually_ge_atTop d0,eventually_ge_atTop (8*W.z),eventually_ge_atTop (8*z), strip_large.eventually_ge_atTop (C*64),big V W N0 (max W.C.i (max M 61)),tiny_size V W N0, Month.fitX 6 2 N0 le_rfl le_rfl V W] with x e q v w y B' hv ht H
  obtain ⟨T,hT⟩:= ht 1 zero_lt_one
  have h:T.q=grainZ V W N0 x:=by rw [hT]; simp [grainZ,hat]
  let m:= oYY V N0 J x; have hx:T.q≤ m.val:= seat_size V 1 2 6 N0 T J h
  have hy: max W.C.i (max M 61)≤ m.val:=B'.trans (h ▸ hx); have hM : M ≤ m.val:= (le_max_left ..).trans ((le_max_right ..).trans hy); have hk(i) := (T.boot i).1
  refine ⟨T,⟨fun b k=> p (hM.trans b) k, ?_, w, h, fun i=> hk i ▸ (tq _ (e.trans (Vale.crown ..))).2,fun i=> hk i ▸ H i,(le_max_right ..).trans ((le_max_right ..).trans hy),hx,(le_max_left ..).trans hy,hv _ (h ▸ hx),q,fun x p=> (tq x (e.trans p)).1⟩,h ▸ hv,v⟩

  intro m b k A e'; refine le_trans (add_le_add_left (move_pay V W z A (p (hM.trans b) k A) e') (billX R.L /512)) ?_; change C≤ _; linarith

lemma toned_ae (L : Side) : ∃ E : ℝ, ∀ᵐ x ∂MeasureTheory.volume, E ≤ x → Toned L x := by
  obtain ⟨z,h⟩:= Rue.arrests; have hp(i) : Set.Countable {x:ℝ| z<x ∧ ¬ Rue.IsleB SU.group (temp (hat L x i))} := by
    apply Set.countable_of_injective_of_countable_image (f:=fun x => temp (hat L x i))
    · intro x hx y hy p; have := h.injOn (lt_of_lt_of_le (show z<x from hx.1) (Vale.crown ..)) (lt_of_lt_of_le (show z<y from hy.1) (Vale.crown ..)) p; exact add_right_cancel this
    refine (Rue.island SU.group).mono ?_; rintro x ⟨y,t,e⟩; subst x; exact t.2
  refine ⟨z+1,?_⟩; filter_upwards [ae_all_iff.mpr fun i:ℕ=> measure_eq_zero_iff_ae_notMem.mp ((hp i).measure_zero MeasureTheory.volume)] with x h e i
  by_contra q; exact h i ⟨by linarith,q⟩
end YM.CF.Py.Rate
