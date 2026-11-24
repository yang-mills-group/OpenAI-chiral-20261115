import Verses.Ocean
import Verses.Policy
import YM.SU5.Fineness.Chalice
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Papyrus.Franc
namespace SatinForce
open Filter Function NormedSpace Fock Finset Lattice Laurent Bloch Lat Cube Rush SU Fir Nacre Ember Scroll Tulip Tenant Cascade
open Papyrus.Granat Thera Dial Verses
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

/-! The flat Slater shear of the construction notes / the construction notes. We take the limit of the polar-angle
    Neumann shears already financed on the flat symbols in the library (not an
    infinite-volume limit). This allows *exact* flat price comparisons in the
    Fock norm & Tilt estimates. All statements here on the supplied SU matter
    hilbert space, no spectral measure rebuilt independently. -/

variable (j : ℕ) (M : Male) (N : Side)

/-- The flat projector on deployment `(j, M, N)`. -/
abbrev FlatPaneP : Op (Single N) := spar j M (1 : Bkg (More N))

local notation "S" => FlatPaneP j M N
local notation "A" => tickA N
local notation "X" => Comb A S

variable (h : 1 ≤ j) (p : IsStarProjection (FlatPaneP j M N))
section
include h p

theorem flat_comb_tendsto_ex : ∃ T : Op (Single N), Tendsto X atTop (𝓝 T) := by
  have cols (i : Single N) : ∃ v : Ket (Single N),
      Tendsto (fun k => acts (X k) (basisKet i)) atTop (𝓝 v) := by
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε e
    obtain ⟨k,hk⟩ := (net_c j h (ε/3) (by positivity)).exists
    have hv (a : ℕ) (w : a ≥ k) :
        dist (acts (X a) (basisKet i)) (acts (X k) (basisKet i)) ≤ ε/3 := by
      rw [dist_eq_norm, ←act_sub]; exact (hk N M p a w i).1
    exact ⟨k, fun m u n t => (dist_triangle_right _ _ (acts (X k) (basisKet i))).trans_lt (by
      linarith only [e,hv m u,hv n t])⟩
  choose V hV using cols
  refine ⟨Matrix.of (fun i l => inner ℂ (basisKet i) (V l)),?_⟩
  apply tendsto_pi_nhds.mpr
  intro i; apply tendsto_pi_nhds.mpr; intro l
  have hi(k:ℕ) : inner ℂ (basisKet i) (acts (X k) (basisKet l)) = X k i l := by rw [basis_inner,basis_act]
  exact (Filter.Tendsto.inner (x:=basisKet i) tendsto_const_nhds (hV l)).congr hi

end

def flatComb : Op (Single N) := (flat_comb_tendsto_ex j M N h p).choose

theorem flatComb_tends : Tendsto X atTop (𝓝 (flatComb j M N h p)) := (flat_comb_tendsto_ex j M N h p).choose_spec

local notation "T" => flatComb j M N h p

theorem flatComb_nil : T * T = 0 := by
  have hh := flatComb_tends j M N h p
  exact tendsto_nhds_unique (hh.mul hh) ((tendsto_const_nhds (x:= (0 : Op (Single N)))).congr fun i => (comb_nil (B:=A) p i).symm)

def exactShear : Shaft (Single N) := ⟨1 + star T, 1 - star T, by
  have hnil : star T * star T = 0 := by rw [← star_mul,flatComb_nil,star_zero]
  rw [add_mul,one_mul,mul_sub,mul_one,hnil,sub_zero]; abel⟩

local notation "U" => exactShear j M N h p
local notation "E" i:max => Saber (B:=A) p i

theorem shear_sell_tends : Tendsto (fun i => (E i).sell) atTop (𝓝 (U).sell) :=
  tendsto_const_nhds.add (flatComb_tends j M N h p).star

theorem shear_buy_tends : Tendsto (fun i => (E i).buy) atTop (𝓝 (U).buy) :=
  tendsto_const_nhds.sub (flatComb_tends j M N h p).star

theorem shear_on_flat : (U).sell * S = S := by
  have hh : Tendsto (fun i => (E i).sell * S) atTop (𝓝 S) := by
    simp_rw [Saber_holds]; exact tendsto_const_nhds
  exact tendsto_nhds_unique ((shear_sell_tends j M N h p).mul_const _) hh

theorem exactShear_fiber {c : ℝ} (hc : postage j c) (q : 0 ≤ c) : fiber U (1+c) := by
  constructor
  · intro i
    have z : Continuous (fun (P : Op (Single N)) => ‖acts P (basisKet i)‖) := by fun_prop
    exact le_of_tendsto ((z.tendsto (U).sell).comp (shear_sell_tends j M N h p))
      (Eventually.of_forall fun k => (Saber_budget p A k q (hc N M k p)).fst i)
  · intro i
    have z : Continuous (fun (P : Op (Single N)) => ‖acts (star P) (basisKet i)‖) := by fun_prop
    exact le_of_tendsto ((z.tendsto (U).buy).comp (shear_buy_tends j M N h p))
      (Eventually.of_forall fun k => (Saber_budget p A k q (hc N M k p)).snd i)

/-- This decouples the phase of the selected finite choice functions: the normalization on
*any* flat Slater ket, and *any* phase on the true bra. Does not assert equality of rays
between this flat sector and any of the non-flat occupied sectors. -/
lemma flat_overlap (v w : Wave (Single N)) (hv : Sea S v) (hw : Sea A w)
    (h : 1 ≤ j) (p : IsStarProjection S) : ‖inner ℂ w v‖ = Real.exp (angleFin M N j) := by
  have τ : Matrix.trace A = Matrix.trace S := (rank_z N h M).symm
  have hh : IsUnit (Zoom N (A * S)) :=
    (isUnit_map_iff (love N).symm.toAlgEquiv.toRingEquiv _).1 (cut_free M N j h)
  have e : skyGlow w 1 v = inner ℂ w v := by rw [skyGlow,quant_one,act_one]
  have ne : inner ℂ w v ≠ 0 := by
    intro he
    have hy := prismK p (plus_P N) τ (1 : Op (Single N)) v hv w hw
    rw [e,he,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Complex.ofReal_zero] at hy
    apply (Matrix.isUnit_iff_isUnit_det _|>.1 hh).ne_zero
    unfold Zoom
    simpa only [mul_one] using hy.symm
  have r := orb_snap S A 0 v hv w hw p (plus_P N) τ
  rw [add_zero, e] at r
  rw [angleFin,←r,Real.exp_log (norm_pos_iff.mpr ne)]

theorem exactShear_vacant {v : Wave (Single N)} (hv : Sea S v) :
    acts (quant (U).sell) v = v := by
  have e : acts (quant S) v = v := by
    nth_rw 1 [←hv.1]; rw [←act_mul,line_quant p,hv.1]
  nth_rw 1 [←e]
  rw [←act_mul, ←quant_mul, shear_on_flat, e]

private lemma shear_bra_le {v : Wave (Single N)} (hv : Sea A v) :
    ‖acts (quant (star (U).buy)) v‖ ≤ Real.exp (angleFin M N j) := by
  let f (P : Op (Single N)) := ‖acts (quant (star P)) v‖
  let q := angleFin M N j
  have z : Continuous f := by unfold f; fun_prop (disch := assumption)
  let n : ℝ := N.val^ (4:ℕ)
  suffices ∀ᶠ ε in 𝓝[>] (0:ℝ), f (U).buy ≤ Real.exp (q + ε*n) by
    have e := (((continuous_const (y:=q)).add (continuous_id.mul_const n)).rexp.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
    simp only [Pi.add_apply,id_eq, zero_mul,add_zero] at e
    exact ge_of_tendsto e this
  filter_upwards [self_mem_nhdsWithin] with ε hε
  refine le_of_tendsto ((z.tendsto _).comp (shear_buy_tends j M N h p)) ?_
  filter_upwards [purge j h ε (show 0<ε from hε)] with k hk
  change ‖acts (quant (star (E k).buy)) v‖ ≤ Real.exp _
  rw [show star (E k).buy=1-X k from by simp only [Saber,star_sub, star_star,star_one]]
  rw [purse p (plus_P N) k v hv]
  exact Real.exp_monotone (by
    change stunt k _ _≤ q+ε*n
    exact hk N M p
  )

/-- Exact alignment with the flat sea *and pricing of the phase multiplier*, not just norm. -/
lemma shear_bra {v w : Wave (Single N)} (hv : Sea S v) (hw : Sea A w) :
    acts (quant (star (U).buy)) w = inner ℂ v w • v := by
  let y := acts (quant (star (U).buy)) w
  let r := inner ℂ v w
  have he : inner ℂ w v = inner ℂ y v := by
    have e := (U).lawn w v 1
    rwa [(U).glow_nil, act_one, act_one, exactShear_vacant j M N h p hv] at e
  have hr : ‖inner ℂ w v‖ = ‖v‖ * ‖y‖ := by
    rw [hv.2,one_mul]
    exact le_antisymm (by rw [he]; simpa [hv.2] using norm_inner_le_norm y v)
      ((shear_bra_le j M N h p hw).trans_eq (flat_overlap j M N v w hv hw h p).symm)
  have hh : y ≠ 0 := norm_pos_iff.mp (by
    rw [flat_overlap j M N v w hv hw h p,hv.2,one_mul] at hr
    rw [←hr]; exact Real.exp_pos _)
  have ht : v ≠ 0 := norm_pos_iff.mp (by rw [hv.2]; norm_num)
  obtain ⟨c,_,e⟩ := (norm_inner_eq_norm_iff (𝕜:=ℂ) ht hh).mp (by
    rw [norm_inner_symm, ← he]; exact hr)
  change y = r • v
  have hc : r = c := by
    rw [e,inner_smul_left,inner_self_eq_norm_sq_to_K,hv.2] at he
    dsimp [r]
    rw [← inner_conj_symm]
    simp [he]
  rwa [hc]

lemma shear_bra_norm {v w : Wave (Single N)} (hv : Sea S v) (hw : Sea A w) :
    ‖acts (quant (star (U).buy)) w‖ = Real.exp (angleFin M N j) := by
  rw [shear_bra j M N h p hv hw,norm_smul,hv.2,mul_one,norm_inner_symm]
  exact flat_overlap j M N v w hv hw h p

/-- WickA (WA.2), signed. -/
lemma flat_price (F : FC (Single N)) {v w : Wave (Single N)} (hv : Sea S v) (hw : Sea A w) :
    inner ℂ w (acts F v)/inner ℂ w v = inner ℂ v (acts ((U).glow F) v) := by
  have hy := (U).lawn w v F
  rw [exactShear_vacant j M N h p hv,shear_bra j M N h p hv hw,inner_smul_left,inner_conj_symm] at hy
  rw [div_eq_iff (norm_pos_iff.mp ((flat_overlap j M N v w hv hw h p).symm ▸ Real.exp_pos _)),hy,mul_comm]


end SatinForce
end YM.CF.Papyrus.Franc
