import YM.CF.BPress.Schedule
import YM.CF.BPress.Test
import YM.CF.Fixed.Way
import YM.CF.Girt.Oar

/-!
Actual interface, cf. manuscript eq:num and VolumeB-gate. `Py.Way` is a
  `Brioche` history on ONE FiniteGaugeData horizon (exists by MeterQ etc.). Use `wide_s` of
the imported library for the ridge quantifiers over n. B-estimates can use
this whole class of true histories at the specified schedule, *not* comparator densities.
Here and below claims proved uniformly on this class (not just the particular matched
trajectory of thm:Fit) do not license use of a comparator on unmatching trajectories.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory Filter Finset Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Tulip Fock Fixed Dial Spire
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {B M s : Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  (V: Grace K R L) {d:ℝ} {U:Grasp V.U B d}{W:GivenX V U} (N0 : ℕ)
  {Mstar : Side}(J:Robes Mstar V W)(q:Push.SectorMeasure.Chi)(h:ℝ)(R0 δ:ℝ→ℝ)

/-- `Way` = reference and actual betas, Cape etc. with `Pull_P`, masks and actual RG of block
integration; indices (i*,p,a)=(6,2,1). K.j=4 in use. -/
abbrev History := Way V 1 2 6 N0 J q h R0 δ
variable {x : ℝ} {n : ℕ}
structure Admit (X : Month x 1 6 2 N0 V W) (M : Side) : Prop where
  threshold : J.h ≤ M.val
  min : X.q ≤ (M*Mstar).val
  horizon : 61 ≤ (M*Mstar).val
variable {V N0 J q h R0 δ}
variable (X : History V N0 J q h R0 δ x M n) (j : ℕ)
local notation "N[" j "]" => cell M B R.L j

theorem gauge_size : (More N[j]).val=M.val*R.L.val^j * 4 * B.val := by
 unfold More cell CSide Vale.mesh; push_cast; ring
variable {j}
lemma span_size {X' : Month x 1 6 2 N0 V W} (T : MeterQ V 1 2 6 N0 J q h R0 δ x X')
    (A : Admit V N0 J X' M) : ∃ (S : ∀ n, History V N0 J q h R0 δ x (M*Mstar) n),
      (∀ n, (S n).val=X') ∧ ∃ (Y : Cape (M*Mstar) B R.L) (ρ : ℕ→ℝ),
      (∀ n, (S n).Y=Y) ∧ (∀ j, 0<ρ j) ∧
      ∀ n j, j<n→ ‖Complex.exp ((S n).E (j+1)).v‖ * ρ j ≤ ‖Complex.exp ((S n).E j).v‖ :=
    Py.wide_s V 1 2 6 N0 J q h R0 δ _ T _ A.threshold A.min A.horizon

lemma mantel (p : j≤n) : Mantle (x:=hat R.L x j) V J h (Vale.mesh M R.L j) (X.E j) (X.Y j):= Way.wears _ _ _ _ _ _ _ _ _ _ X j p
lemma history_prices (p : j≤n) : let y:= hat R.L x j; let F:= X.E j
    x ≤ y ∧ y/2 ≤ F.beta ∧ F.beta ≤ 2*y ∧ F.p.threshold=temp y ∧
    F.p.B=radiusB y ∧ F.p.supportExponent=1 ∧ F.slip=0 ∧ Roof _ J.k d J.n (X.Y j) := by
  let Y:= mantel X p
  let B':=(X.val.boot j); have he : (X.E j).p=X.val.a j:=(X.scale.note.owns j p).width.symm
  exact ⟨Vale.crown .., Y.hill.1, Y.hill.2, Y.fund, he ▸ B'.2.1, he ▸ B'.2.2.1,Y.due,Y.crown⟩ -- tune
lemma actual_gauge (p : j≤n) (z : Orbit N[j]) (g : Site (More N[j]) → SU.E) :
    rescaleOffset U (X.E j) (X.Y j) (Girt.gird g z) = effectK (tradew _ g).val (rescaleOffset U (X.E j) (X.Y j) z) := by
  have Y:= mantel X p
  rw [rescaleOffset,Pi.smul_apply,Girt.sweep (X.E j) (Y.wall ..) Y.close.leanJ.1 _ _ Y.crown _ _ W.pearl V.note Y.rest (warmJ V),Pi.smul_apply,effectK,effectK,map_smul]
lemma occupied (p : j≤n) (z : Orbit N[j]) :
    let A:=spar K.j (X.E j).J.M (X.Y j z)
    let a:=changeM U (X.Y j z) (X.E j).J.M
    IsStarProjection A ∧ Sea A a := by
  let H:=mantel X p; exact ⟨(U.broadness _ H.rest _).projection _ (H.crown.paid _), sea_g H.rest _ (H.crown.paid _) _⟩
lemma integrable_history (p : j≤n) {S : Support (More N[j])} {F : Fixed.Test N[j]} {C : ℝ} (t : IsMark S F C) :
    Integrable (integrand F (rescaleOffset U (X.E j) (X.Y j))) (city N[j]) := reading_integrable _ _ _ (Mantle.rich _ _ _ (mantel X p)) t
lemma reading_history_one (p : j≤n) :
    reading U (X.E j) (X.Y j) 1= Complex.exp (-(X.E j).v)* partitionZ (X.E n) U (X.Y n):=by rw [reading_one,scaledZ, X.scale.balance j p]
-- divisibility purchases (additional multiple & min size for further assertions).
theorem periods {X : Month x 1 6 2 N0 V W} {w : GapSize} {L' y : ℝ} (p : 1 ≤ w.rP y)
    (u : (w.select y).P=w.rawP y) (i k : ℕ) (P : Side) :
    ∃ (M : Side), i ≤ M.val ∧ Admit V N0 J X M ∧
     let s:=More (cell (M*Mstar) B R.L j)
     k ≤ s.val ∧ P.val ∣ s.val ∧ ∃ A : Bands s (w.select y), Dyadic w L' y A := by
  let W' := w.select y; let l:=W'.full; let R' := frameWidth L' y
  let D : Side:= ⟨ W'.P, W'.P_pos⟩
  let U : Side:= ⟨max i (max J.h (max X.q (max 61 (k+4)))),by omega⟩
  let Y : Side:=l*(2^(w.rP y+1)); let T : Side:= Y*(2*D); let Z:= T*R'; let M:= U*P*Z
  have elem (a b : Side) : a.val ∣ (a*b).val:= by change a.val ∣ a.val*b.val; exact dvd_mul_right ..
  have hd : U.val∣ M.val:= dvd_trans (elem ..) (elem ..); have he:=Nat.le_of_dvd M.property hd; have ht:=Nat.le_of_dvd (M*Mstar).property (elem M Mstar)
  change max i (max J.h (max X.q (max 61 (k+4)))) ≤ M.val at he
  refine ⟨M,by omega,⟨by omega,(show X.q ≤ M.val by omega).trans ht,(show 61≤M.val by omega).trans ht⟩,?_⟩; intro s
  have hs : M.val∣ s.val:= by
     refine dvd_trans (elem M Mstar) ?_; unfold s; rw [gauge_size]; exact ⟨_, show _ = _ * (R.L.val^j * (4*B.val)) from by ring⟩
  have hb := Nat.le_of_dvd s.property hs
  have hh : Z.val ∣ M.val:= dvd_mul_left ..
  have hx : Y.val ∣ s.val:= dvd_trans (elem ..) (dvd_trans (elem ..) (dvd_trans hh hs))
  change l.val * (2^(w.rP y+1)) ∣ s.val at hx
  constructor; · exact (show k ≤ M.val by omega).trans hb
  constructor; · exact dvd_trans (dvd_trans (dvd_mul_left ..) (elem (U*P) Z)) hs
  obtain ⟨a,ha⟩:=hx
  let e:= 2^(w.rP y+1); have e' : 4≤ e:= by
    apply pow_le_pow_right₀ (show (1:ℕ)≤2 by norm_num) (show 2≤ w.rP y+1 from by omega)
  have ha': s.val=W'.full.val * (e*a):= ha.trans (mul_assoc ..)
  have v:=s.property; have hX:0<e*a:= Nat.pos_iff_ne_zero.mpr fun g=> by rw [g,mul_zero] at ha'; exact Nat.ne_of_gt s.property ha'
  have hZ:4≤ e*a:= e'.trans (Nat.le_mul_of_pos_right _ (by by_contra! hh; rw [Nat.eq_zero_of_le_zero hh,mul_zero] at hX; omega))
  refine ⟨⟨⟨e*a,hX⟩,hZ,ha',?_⟩, p,u,dvd_mul_right ..,dvd_trans ?_ hs,dvd_trans (dvd_trans ?_ hh) hs,?_⟩
  · exact (even_two.pow_of_ne_zero (Nat.succ_ne_zero _)).mul_right _
  · exact dvd_trans (dvd_trans (show (2*D:Side).val∣ T.val from dvd_mul_left ..) (elem T R')) hh
  · change R'.val ∣ T.val* R'.val; exact dvd_mul_left ..
  have hw : 4 ≤ U.val:=by dsimp [U]; omega
  have hv : U.val ≤ (U*P).val:=Nat.le_of_dvd (U*P).property (elem U P)
  have hk : R'.val ≤ Z.val:=Nat.le_of_dvd Z.property (show R'.val∣ T.val*R'.val from dvd_mul_left ..)
  exact (Nat.mul_le_mul (hw.trans hv) hk).trans hb
end YM.CF.BPress
