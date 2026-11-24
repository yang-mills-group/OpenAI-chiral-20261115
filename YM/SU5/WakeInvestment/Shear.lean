import YM.SU5.WakeInvestment.Generator
import SatinThinRod

/-!
Pass stock estimates on the finite Saber all the way to an exact shear on
*each actual reg site space*, to permit the occupation-number estimates from F & WA;
also keep its uniform column budget. We give the compiler objects with `p` Prop arguments
(rather than spectral assumptions about all `spar j M` at nonflat V). No measurable dependence
on the link arguments through this choice (depends on j M N, **flat**).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Fock Lattice Finset NormedSpace
open Papyrus Papyrus.Franc
open Lat Fir Ember Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {P Q : Op I}
variable {N : Side} {j : ℕ} {M : Male}
local notation "ΩK" => spar j M (1 : Pane N)

/-- Uniquely take the whole `Comb` limit, to buy the two exact matches with flat WA accounts. -/
lemma comb_converges (hj : 1 ≤ j) (p : IsStarProjection ΩK) :
    ∃ X : Op (Single N), Tendsto (Comb (tickA N) ΩK) atTop (𝓝 X) := by
  let F := Comb (tickA N) ΩK
  have hcol (i : Single N) : CauchySeq (fun k => acts (F k) (basisKet i)) := by
    refine Metric.cauchySeq_iff'.mpr (fun ε hε => ?_)
    obtain ⟨k,hk⟩ := (net_c j hj (ε/2) (half_pos hε)).exists
    exact ⟨k,fun v hv => by
      rw [dist_eq_norm,←act_sub]; exact (hk N M p v hv i).1.trans_lt (half_lt_self hε)⟩
  choose x hx using fun i => cauchySeq_tendsto_of_complete (hcol i)
  refine ⟨Matrix.of (fun i k => (x k).ofLp i),?_⟩
  refine tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr (fun k => ?_))
  exact ((PiLp.continuous_apply 2 (fun _ : Single N => ℂ) i).continuousAt.tendsto.comp (hx k)).congr (fun j => basis_act ..)

section

def spineJet (hj : 1 ≤ j) (p : IsStarProjection ΩK) : Op (Single N) := (comb_converges (N:=N) (M:=M) hj p).choose

lemma pad_jet (hj : 1 ≤ j) (p : IsStarProjection ΩK) : Tendsto (Comb (tickA N) ΩK) atTop (𝓝 (spineJet (N:=N) (M:=M) hj p)) := (comb_converges (N:=N) (M:=M) hj p).choose_spec

/-- The exact shear. Sell is $G_*$ of F over Single at this flat operator. -/
def shear (hj : 1 ≤ j) (p : IsStarProjection ΩK) : Shaft (Single N) where
  sell := 1 + star (spineJet (N:=N) (M:=M) hj p)
  buy := 1 - star (spineJet (N:=N) (M:=M) hj p)
  payment := by
    let f (L : Op (Single N)) := (1+star L)*(1-star L)
    change f (spineJet (N:=N) (M:=M) hj p) = _
    have hf : Continuous f := by unfold f; fun_prop
    apply tendsto_nhds_unique (hf.continuousAt.tendsto.comp (pad_jet (N:=N) (M:=M) hj p))
    exact tendsto_const_nhds.congr fun k => (Saber p (B:=tickA N) k).payment.symm

lemma ship_sell (hj : 1 ≤ j) (p : IsStarProjection ΩK) : Tendsto (fun k => (Saber p (B:=tickA N) k).sell) atTop (𝓝 (shear (N:=N) (M:=M) hj p).sell) :=
  tendsto_const_nhds.add (pad_jet (N:=N) (M:=M) hj p).star
lemma ship_buy (hj : 1 ≤ j) (p : IsStarProjection ΩK) : Tendsto (fun k => (Saber p (B:=tickA N) k).buy) atTop (𝓝 (shear (N:=N) (M:=M) hj p).buy) :=
  tendsto_const_nhds.sub (pad_jet (N:=N) (M:=M) hj p).star
lemma shear_flat (hj : 1 ≤ j) (p : IsStarProjection ΩK) : (shear (N:=N) (M:=M) hj p).sell * ΩK = ΩK :=
  tendsto_nhds_unique ((ship_sell (N:=N) (M:=M) hj p).mul_const ΩK) (tendsto_const_nhds.congr fun _ => (paint_stays p).symm)

variable {E : ℝ}
lemma exact_columns (hj : 1 ≤ j) (p : IsStarProjection ΩK) (e : postage j E) :
    ColumnDeal (shear (N:=N) (M:=M) hj p).sell (1+E) ∧ ColumnDeal (star (shear (N:=N) (M:=M) hj p).buy) (1+E) := by
  have h (i : Single N) : Continuous (fun A : Op (Single N) => acts A (basisKet i)) := acts_cont.clm_apply continuous_const
  refine ⟨⟨fun i=>?_⟩,⟨fun i=>?_⟩⟩
  · apply le_of_tendsto (((h i).continuousAt.tendsto.comp (ship_sell (N:=N) (M:=M) hj p))).norm
    exact Eventually.of_forall fun k => (postal p e k).1.all i
  apply le_of_tendsto (((h i).continuousAt.tendsto.comp (ship_buy (N:=N) (M:=M) hj p).star)).norm
  exact Eventually.of_forall fun k => (postal p e k).2.all i
end
section
open Thera
local notation "D0" => Real.exp (Cascade.angleFin M N j)

/-- `$D_{0,s}$`, independent of phases (and not a claim of an IR bound).
The equality here uses the *same* Male as in the Sea paired against the plus projection.
Variant of Cascade.angle_pay not requiring a Grasp; allow both Seas arbitrary. -/
theorem wake_overlap (hj : 1 ≤ j) (p : IsStarProjection ΩK) (x y : Wave (Single N))
    (hx : Sea (tickA N) x) (hy : Sea ΩK y) : ‖inner ℂ x y‖ = D0 := by
  let A:= tickA N
  have h := Cascade.plus_P N
  have u := (Cascade.rank_z N hj M).symm
  have hK : skyGlow x (1 : Op (Single N)) y=inner ℂ x y := by rw [skyGlow,quant_one,act_one]
  have hh : IsUnit (Cascade.Zoom N (A*ΩK)) :=
    (isUnit_map_iff (love N).symm.toAlgEquiv.toRingEquiv _).1 (Cascade.cut_free M N j hj)
  have hp := prismK p h u 1 y hy x hx
  have hB := orb_snap ΩK A 0 y hy x hx p h u
  rw [add_zero,hK] at hB; rw [show Cascade.angleFin M N j= _ from hB.symm]
  symm; apply Real.exp_log
  apply norm_pos_iff.mpr
  intro z
  apply (Matrix.isUnit_iff_isUnit_det _|>.1 hh).ne_zero; unfold Cascade.Zoom
  simpa only [hK,z,norm_zero,zero_pow (by decide:(2:ℕ)≠0),Complex.ofReal_zero,mul_one] using hp.symm

/-- Saturate the Cauchy--Schwarz inequality: no residual correction for the
$ε N^4$ error which would be recurring every marked invocation in a `Saber` calculation. -/
theorem saturation (hj : 1 ≤ j) (p : IsStarProjection ΩK) (x y : Wave (Single N))
    (hx : Sea (tickA N) x) (hy : Sea ΩK y) :
    let z:=acts (quant (star (shear hj p).buy)) x
    ‖z‖ = D0 ∧ z = star (inner ℂ x y) • y := by
  let T:= shear hj p; intro z
  have hK : acts (quant T.sell) y = y := stays p _ (shear_flat hj p) _ hy
  have hv : inner ℂ z y=inner ℂ x y := by
    change inner ℂ (acts (quant (star T.buy)) x) y= _
    rw [quant_star,act_inner]; conv_lhs=> rw [←hK, ←act_mul,←quant_mul,T.pay,quant_one,act_one]
  have hu := wake_overlap hj p x y hx hy
  have f : ‖z‖ ≤ D0 := by
    let u (a:ℝ) := Real.exp (GaugeFlux.seaPrec j N M + a*N.val^4)
    let V (A:Op (Single N)) := acts (quant (star A)) x
    have he : ∀ a>0, ‖z‖ ≤ u a := by
      intro a ha
      have h : Continuous V := by unfold V; fun_prop
      apply le_of_tendsto ((h.continuousAt (x:=T.buy)).tendsto.comp (ship_buy hj p)).norm
      filter_upwards [purge j hj a ha] with k hk
      let U:=Saber p (B:=tickA N) k
      change ‖acts (quant (star U.buy)) x‖ ≤ u a
      rw [show star U.buy = 1-Comb (tickA N) ΩK k from (by unfold U Saber; simp),purse p (Cascade.plus_P N) k x hx]
      exact Real.exp_monotone (hk N M p)
    have h : Tendsto u (𝓝[>] 0) (𝓝 (u 0)) := ((show Continuous u by unfold u; fun_prop).continuousWithinAt)
    apply le_of_le_of_eq (ge_of_tendsto h ((show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin).mono fun a ha=> he a ha))
    unfold u; simp only [zero_mul,add_zero,GaugeFlux.seaPrec]
  have hl:= norm_inner_le_norm z y (𝕜:=ℂ)
  rw [hv,hu,hy.2,mul_one] at hl
  have g:= le_antisymm f hl
  refine ⟨g, ?_⟩
  have hw : inner ℂ y z = star (inner ℂ x y) := hv ▸ (inner_conj_symm ..).symm
  have hcs : ‖inner ℂ y z‖ = ‖y‖ * ‖z‖ := by rw [hw,norm_star,hu,hy.2,g,one_mul]
  have f0 : y ≠ 0 := norm_pos_iff.mp ((by rw [hy.2]; norm_num : 0<‖y‖))
  have hz : z=(inner ℂ y z/inner ℂ y y) • y := Or.resolve_left (((norm_inner_eq_norm_tfae ℂ y z).out 0 1).mp hcs) f0
  rw [inner_self_eq_norm_sq_to_K,hy.2] at hz; simpa [hw] using hz

/-- eq. WA.2 on **every Fock operator** (in particular with the `1/16` normalized
q columns at this cost). No claim about $E$ until earning the extensive
estimates below. Uses `norm_pos` on the exact overlap. -/
theorem wick_prepayment (hj : 1 ≤ j) (p : IsStarProjection ΩK) (x y : Wave (Single N))
    (hx : Sea (tickA N) x) (hy : Sea ΩK y) (A : FC (Single N)) :
    inner ℂ y (acts ((shear hj p).glow A) y) = inner ℂ x (acts A y)/inner ℂ x y := by
  have h : inner ℂ x y≠0 := norm_pos_iff.mp (show 0 < ‖inner ℂ x y‖ by rw [wake_overlap hj p x y hx hy]; exact Real.exp_pos _)
  rw [(shear hj p).lawn x y, (saturation hj p x y hx hy).2, stays p _ (shear_flat hj p) y hy, inner_smul_left]
  simp [mul_div_cancel_left₀ _ h]
end
#print axioms exact_columns
#print axioms wick_prepayment
end YM.CF.WakeInvestment
