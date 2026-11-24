import YM.SU5.Reconstruction.UVPrice.Temper
import YM.SU5.Reconstruction.Moat.Sonic
import YM.SU5.Reconstruction.Cashier.Honesty
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Moat
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup ConePrice
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
open Roy Anvil Multiplier
lemma outside_hydro (x:H)(h:∀ u v:ℝ, 0<u → 0 ≤ v → (P).region (band a u v) x=0) : cue S x=x := by
 let A:= (P).region (toe a)ᶜ; let y:= A x
 have X(i:ℕ): ∀ᵐ p∂(P).diagonal x, p∉ band a ((i:ℝ)+1)⁻¹ i:=by apply ae_iff.mpr; simp only [Classical.not_not]; exact ((P).null_pair (bandM ..) x).2 (h _ _ (by positivity) (by positivity))
 have D: ∀ᵐ p∂ (P).diagonal x, p∈ toe a := by
    filter_upwards [S.bright x, ae_all_iff.mpr X] with z p b
    by_contra e; have he:0<z a:= lt_of_le_of_ne p (Ne.symm e)
    obtain ⟨m,hx⟩:=exists_nat_gt ((z a)⁻¹+(z a)); have hz:0<(m:ℝ)+1:=by positivity
    apply b m; refine ⟨?_,?_⟩
    · rw [inv_le_comm₀ hz he]; linarith
    have hm:0 < (z a)⁻¹ := by positivity
    linarith
 have hv:A x=0:= ((P).null_pair toe_meas.compl x).1 (ae_iff.mp D)
 have hA: cue S + A = 1:= by
    apply Registers.single ((toe_pays S).add (Registers.box _ toe_meas.compl)); rw [show (toe a).indicator (1:E4→ℂ)+(toe a)ᶜ.indicator 1=1 from funext fun i=> by by_cases p:i∈toe a<;>simp [p]]; exact Registers.one _
 exact Eq.trans (show cue S x=(cue S + A) x by simp [_root_.add_apply,hv]) (by rw [hA]; rfl)

open Anvil
lemma low_limit {ι : Type*} (l:Filter ι)[l.NeBot]{X:ι→H.Op}{T:H.Op}(h: Anvil.Limited l X T)(Ω:H)(g:∀ u v:ℝ, 0<u→0≤v→Tendsto (fun i=>(P).region (band a u v) (X i Ω)) l (𝓝 0)) : cue S (T Ω)=T Ω:= by
 apply outside_hydro; intro u v p t; let A:= (P).region (band a u v)
 apply ext_inner_left ℂ; intro y; refine tendsto_nhds_unique ?_ (tendsto_const_nhds.inner (g u v p t))
 simp only [←ContinuousLinearMap.adjoint_inner_left ((P).region (band a u v))]; exact h.confirms _ Ω
end YM.Moat
