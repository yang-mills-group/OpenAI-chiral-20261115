import SatinStress.U1.PivotConclusion

/-! Locate both tensors (97) on their **class rows**, with the normalization in (97).
This does not assert their free *charge* normalization correct; that calls for
additional free-field (Wick shell) analysis. Using only the polynomial test meaning of
the tensors here. For `Jg`, polarize with *sum* convention on the GG Wick evaluation;
for `Jf`, use precisely the spin row in (93) and L'=q-p. -/
namespace SatinStress.U1
open Certificate Radix Class Derivative Sequence
open Raw (relation denote)
namespace Line

open Chart
-- GG with μ summed; spin polarizations in z. No antisymmetric typically omitted factors.
def gauge (z : GPol) (i j : Axis) : Expr := four fun a =>
    Chart.F 0 z.1 i a * Chart.F 1 z.2 j a + Chart.F 1 z.2 i a * Chart.F 0 z.1 j a
/-- `4 • Jg` -/
def gauge4 : Raw (TR GPol) := fun z =>
    Expr.conZ 4 * gauge z.1 z.2.val.1 z.2.val.2 - if z.2.val.1=z.2.val.2 then
      four fun a => gauge z.1 a a else 0
/-- `64 • Jf` -/
def spin64 : Raw (TR FPol) := fun z =>
    let a := z.2.val.1
    let b := z.2.val.2
    (-(spin a * d b + spin b * d a))

set_option maxHeartbeats 24000000 in
set_option maxRecDepth 120000 in
theorem gauge_cert : (relation [(gauge4,1),(G.t1,-2),(G.t2,2),(G.t3,-4)]).denote = 0 :=
  Raw.spends G.tRow_all (by decide +kernel)
set_option maxHeartbeats 2400000 in
theorem spin_cert : (relation [(spin64,1),(F.t1,2),(F.t3,1)]).denote = 0 :=
  Raw.spends F.tRow_all (by decide +kernel)

open Submodule
variable (K : Type*) [Field K] [Algebra K ℂ] [CharZero K]

lemma in_gauge : gauge4.denote ∈ gaugeStress K := by
  unfold gaugeStress
  rw [(G.tables K).costT, bake, G.issuers_T,G.mapped_T,G.pick_T]
  exact Raw.kill K _ 1 [(G.t1,-2),(G.t2,2),(G.t3,-4)] (by decide) (by simp) (Raw.of_rel gauge_cert)
lemma in_flavor : spin64.denote ∈ flavorStress K := by
  unfold flavorStress
  rw [(F.tables K).costT, bake,F.issuers_T,F.mapped_T,F.pick_T]
  exact Raw.kill K _ 1 [(F.t1,2),(F.t3,1)] (by decide) (by simp) (Raw.of_rel spin_cert)

lemma shape_g : gauge4.denote = (2:ℤ) • G.t1.denote - (2:ℤ) • G.t2.denote + (4:ℤ) • G.t3.denote := by
  have h := Raw.of_rel gauge_cert
  simp only [Raw.relation_step, Raw.denote_plus, Raw.denote_times, Raw.relation_nil, Raw.denote_zero,one_smul] at h
  rw [h]; abel
lemma shape_f : spin64.denote = (-2:ℤ) • F.t1.denote - F.t3.denote := by
  have h := Raw.of_rel spin_cert
  simp only [Raw.relation_step, Raw.denote_plus, Raw.denote_times, Raw.relation_nil, Raw.denote_zero,one_smul] at h
  rw [h]; abel

omit [CharZero K] in
lemma conservation_g : divT K s gauge4.denote = 0 := by
  have ht := G.D_dep_3
  simp only [Raw.relation_step, Raw.denote_plus, Raw.denote_times, Raw.relation_nil, Raw.denote_zero, G.d1, G.d2,G.d3,G.frequency, luDiv K s] at ht
  rw [shape_g]; simp only [map_add,map_sub,map_zsmul]
  linear_combination (norm := module) (2 : ℤ) • ht
omit [CharZero K] in
lemma conservation_f : divT K s spin64.denote = 0 := by
  have ht := F.D_dep_2
  simp only [Raw.relation_step, Raw.denote_plus, Raw.denote_times, Raw.relation_nil, Raw.denote_zero, F.d1,F.d2,F.frequency, luDiv K s] at ht
  rw [shape_f]; simp only [map_sub,map_zsmul]
  linear_combination (norm := module) -ht

noncomputable def Jg : gaugeStress K := (4:K)⁻¹ • (⟨gauge4.denote, in_gauge K⟩ : gaugeStress K)
noncomputable def Jf : flavorStress K := (64:K)⁻¹ • (⟨spin64.denote, in_flavor K⟩ : flavorStress K)

set_option maxHeartbeats 1000000 in
lemma gauge_cert_ne : gauge4.denote ≠ 0 := by
  intro he
  exact nonzero_of_seen (gauge4 ((0,1),Duo.sym 0 0)) 532482 (by decide +kernel) (congr_fun he _) -- replace n & argument metavars
set_option maxHeartbeats 1000000 in
lemma spin_cert_ne : spin64.denote ≠ 0 := by
  intro he
  exact nonzero_of_seen (spin64 ((),Duo.sym 0 0)) 129 (by decide +kernel) (congr_fun he _)

theorem Jg_ne : Jg K ≠ 0 := by
  apply smul_ne_zero (by norm_num : (4:K)⁻¹ ≠ 0)
  exact fun h => gauge_cert_ne (congr_arg Subtype.val h)
theorem Jf_ne : Jf K ≠ 0 := by
  apply smul_ne_zero (by norm_num : (64:K)⁻¹ ≠ 0)
  exact fun h => spin_cert_ne (congr_arg Subtype.val h)

theorem supplies :
    LinearMap.ker (D K ge4 s) = K ∙ Jg K ∧
    LinearMap.ker (D K ph4 s) = K ∙ Jf K := by
  obtain ⟨-, -, hg, hf⟩ := low_consequences K
  constructor
  · symm; apply Submodule.eq_of_le_of_finrank_le
    · apply (Submodule.span_singleton_le_iff_mem ..).mpr
      rw [LinearMap.mem_ker, Jg,map_smul, show D K ge4 s ⟨gauge4.denote,in_gauge K⟩ = 0 from conservation_g K, smul_zero]
    rw [hg, finrank_span_singleton (Jg_ne K)]
  symm; apply Submodule.eq_of_le_of_finrank_le
  · apply (Submodule.span_singleton_le_iff_mem ..).mpr
    rw [LinearMap.mem_ker, Jf,map_smul, show D K ph4 s ⟨spin64.denote,in_flavor K⟩ = 0 from conservation_f K, smul_zero]
  rw [hf, finrank_span_singleton (Jf_ne K)]
end Line
end SatinStress.U1
