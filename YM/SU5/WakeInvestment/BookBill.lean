import YM.SU5.WakeInvestment.Tilt
import SatinThinAbility

/-!
Fock estimate of `the construction notes` (WA.1), `X` arbitrary link/tag input ("V" there), right through the
finite `Compass` state (no assertion turning off failed-mask `Force` units). Uses Yoke's
`metroStress` leeway instead of grey-cell counting. Explicit below including before cancellation
of $D_{0,s}$. This is not the Wick comparison (WA.7) on gauge curvatures etc.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option maxRecDepth 3000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Fock Lattice Finset NormedSpace
open Papyrus Papyrus.Franc
open Lat Fir Ember Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask Paige Vault Scree Spire Peaks
open Py.Rate.LocalLimit.Preparation.Yoke Graph
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {P Q : Op I} {T : Shaft I} {ρ w : ℝ}
variable {N : Side} {j : ℕ} {M : Male} {t v h z E : ℝ}

/-- work around gear before the tilt energy evolution -/
lemma tilt_dressed (q : IsStarProjection Q) (S : Shaft I) (A : FC I) (x : Wave I) (t : ℝ) :
    acts (wholeTilt Q t) (acts (quant S.sell) (acts A x)) =
    acts ((weighted Q t S).glow A) (acts (wholeTilt Q t) (acts (quant S.sell) x)) := by
  let T:= weighted Q t S
  rw [tilt_act q, tilt_act q, (acts (T.glow A)).map_smul_of_tower]; congr 1
  rw [←act_mul,←act_mul]; apply congrArg (fun u : FC I => acts u x)
  change quant T.sell * A = quant T.sell * A * quant T.buy * quant T.sell
  rw [mul_assoc _ (quant T.buy),←quant_mul,T.pay,quant_one,mul_one]

lemma gaugedQ (q : IsStarProjection Q) (U : UNI I) : IsStarProjection (twist U Q) := by
  constructor
  · unfold IsIdempotentElem; rw [←map_mul,q.isIdempotentElem.eq]
  unfold IsSelfAdjoint; rw [←map_star, q.isSelfAdjoint.star_eq]

/-- Tilt price at finite reg with full Yoke comparison and the extra height paid.
May replace any Board with the *actual pointwise tier* inequality needed below. -/
def boardRent (E : ℝ) := 1+shellRent (1+E)+(tiltBound*(45*(1+E)))^2

lemma boardRent_pos (E : ℝ) : 0 < boardRent E := by unfold boardRent shellRent; positivity

variable {m B L:Side}{ho:Odd L.val}{d:ℝ}{Y:Pricing j L ho (Vault.Thread j)}
local notation "ΩZ" => spar j M (1 : Pane N)

def windShaft (hj : 1 ≤ j) (p : IsStarProjection ΩZ) (g : Seat N → SU.E) : Shaft (Single N) :=
  (shear hj p).foldC (unitStem (tradew N g))

lemma wind_sells (hj : 1 ≤ j) (p : IsStarProjection ΩZ) (e : postage j E) (g : Seat N→SU.E) (ht : |t| ≤ 1) :
    let W:= weighted ΩZ t (windShaft hj p g)
    ColumnDeal W.sell (tiltBound*(45*(1+E))) ∧ ColumnDeal (star W.buy) (tiltBound*(45*(1+E))) := by
  intro W
  refine ⟨sells p (craftE _ (exact_columns hj p e).1 g) _ ht,buys p ?_ _ ht⟩
  unfold windShaft Shaft.foldC unitStem; simp only [star_mul,star_star]
  exact craftE _ (exact_columns hj p e).2 g

/-- This norm is on the whole Fock space. We *pay* the tilt on the sea itself,
so this can give an estimate for the beginning vector of (WA.11)'s integration.
The cost forms may use the actual transformed gauge at their choice. -/
lemma posture (w : Grasp Y B d) (R : GramM (mid m B)) (U : Loom (mid m B)) (X : Orbit (mid m B))
    (g : Seat (mid m B) → SU.E) (hj : 1 ≤ j)
    (x : IsStarProjection (spar j R.J.M (1 : Pane (mid m B))))
    (q : IsStarProjection (spar j R.J.M (U X)))
    (u : Sea (spar j R.J.M (U X)) (changeM w (U X) R.J.M))
    (hw : 0 ≤ v) (hv : ∀ k : Single (mid m B), Gall.dialZ (acts (spar j R.J.M (U X)) (basisKet k)) ≤ v)
    (he : 0 ≤ E) (e : postage j E) (hz : (v+1)*(tiltBound*(45*(1+E))) ≤ h)
    (c : tier h (R.board X).val ≤ Real.exp z) (t : ℝ) (ht : |t| ≤ 1) :
    let W:= windShaft hj x g
    ‖acts (wholeTilt (spar j R.J.M (1 : Pane (mid m B))) t) (acts (quant W.sell) (recX w R U X))‖ ≤
      past R X.1 * Real.exp (z + boardRent E * metroStress j R U X g) := by
  intro W
  let P₀ := spar j R.J.M (1 : Pane (mid m B)); let A := mile j R U X; let f:= changeM w (U X) R.J.M
  let T := weighted P₀ t W; let U' := tradew (mid m B) g; let V:= U X; let G:= R.J; let P:= spar j G.M V
  rw [Graph.porch,(acts (quant W.sell)).map_smul_of_tower,(acts (wholeTilt _ t)).map_smul_of_tower,
    norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  change past R X.1 * ‖acts (wholeTilt P₀ t) (acts (quant W.sell) (acts A f))‖ ≤ _
  rw [tilt_dressed x]; simp_rw [W, windShaft, era_fold]
  let y:= acts (quantU U').val f; let P':= twist U' P; let f':= acts (wholeTilt P₀ t) (acts (quant (shear hj x).sell) y)
  obtain ⟨hs,hb⟩ := wind_sells hj x e g ht
  let C:= actF j R U X; let ρ:= tiltBound*(45*(1+E)); let r:= revE C; let u':= revE (P'-P₀)
  have hS: ‖f'‖≤ Real.exp (shellRent (1+E)*u'):= TiltSea (gaugedQ q U') x (shear_flat hj x)
    (by positivity) (exact_columns hj x e).1 y (windLace _ P _ u) t ht
  let L:=Pec.pigment R.J.I V
  have heL: 0 ≤ tiltBound:=tiltBound_pos.le; have hr:0 ≤ ρ:=by unfold ρ; positivity
  have hu:0≤ h:= le_trans (mul_nonneg (by linarith : 0 ≤ v+1) hr) hz
  have hk:‖T.glow (tank P (R.board X))‖ ≤ Real.exp z:= by
    refine le_trans ?_ c
    have he:∀ i:LeanV (Single (mid m B)), ‖T.glow (drawT P i)‖ ≤ h:= fun i=> (T.tag_glow ρ hs hb P v hr hw hv i).trans hz
    simpa using (tank_glow T P h 0 ∅ (R.board X) hu le_rfl (fun i=> by simpa using he i))
  have hδ: ‖T.glow (exp (dg C))‖ ≤ Real.exp (ρ^2*r):=by rw [T.glowExp]; exact (bootC _).trans (Real.exp_monotone (T.dg_glow ρ hs hb C hr))
  change past R X.1 * ‖acts (T.glow A) f'‖ ≤ _
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hη := Complex.norm_exp_le_exp_norm (-L)
  rw [norm_neg] at hη
  have hA: ‖T.glow A‖ ≤ Real.exp (‖L‖ + z + ρ^2*r) := by
    unfold A mile; rw [T.glow_free,T.glow_mult,norm_smul];
    refine (mul_le_mul hη ((norm_mul_le ..).trans (mul_le_mul hk hδ (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_
    rw [← Real.exp_add, ←Real.exp_add, ← add_assoc]
  apply (spentS _ _ _).trans; apply (mul_le_mul hA hS (norm_nonneg _) (Real.exp_pos _).le).trans
  change Real.exp _ * Real.exp _ ≤ Real.exp (z + (1+shellRent (1+E)+ρ^2)*(‖L‖+r+u')); rw [←Real.exp_add]; apply Real.exp_monotone
  have hv: 0≤r:= revE_ge C; have hu: 0≤u':=revE_ge _; have hl:0≤ shellRent (1+E):=by unfold shellRent; positivity
  have h':= norm_nonneg L; have hw:= sq_nonneg ρ
  nlinarith only [h',hu,hv,mul_nonneg hu hw,mul_nonneg h' hw,mul_nonneg h' hl,mul_nonneg hv hl]

-- switch on that pointwise price from an actually enrolled estimate;
-- proof of the budget criterion from the proof of `Graph.market_glow`
lemma posture_ready (R : GramM N) (u : Orbit N) (t : 0 ≤ h) (e : MarketR R h z) :
    tier h (R.board u).val ≤ Real.exp z := by
  obtain ⟨x,y,s,hr,hs,hf,v⟩:=e; let Y:= Graph.actG R u; let F:=fueled R.p R.K u
  change tier h ((exp Y:Dough _).val*F.val)≤ _; apply le_trans _ (Real.exp_monotone v)
  rw [Real.exp_add]; exact (tier_mul t _ F).trans (mul_le_mul ((dust_exp h Y t).trans (Real.exp_le_exp.mpr
    (show tier h Y.val≤x+y from (tier_plus t _ _).trans
      (add_le_add (fixedToeE hr t u.1) (fixedToeE hs t u.1)))))
    (fixedToeF hf t _) (Pastry.pitch t F.val) (Real.exp_pos _).le)

#print axioms posture
end YM.CF.WakeInvestment
