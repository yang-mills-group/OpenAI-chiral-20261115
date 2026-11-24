import YM.SU5.FiniteGaugeData.Tower.Base
set_option autoImplicit false
set_option quotPrecheck false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
open FullBill Marks
namespace Donor
variable {τ ε:ℝ}
local notation "Ds" i:max => (expense C R x τ i + |serviceCost T i|)
-- Bridge.shrinks with extra volume-exponential allowed
lemma shrinksAmplified (i b:ℕ) (he:0 < ε) (A:ℝ) : ∀ᶠ n in atTop, ∀ m:Side,
    cone b n m → Real.exp (A * game m) * divisionBill T C τ i n m ≤ ε := by
  let Vq:= volumePrice T i+1; let t:= thermalCost C R x τ i*postage B R.L i; let v:= Ds i * postage B R.L i
  have p := collapse b (c:=Real.log 2) (Real.log_pos (by norm_num)) (half_pos he) (horizontalPrice T i)
  filter_upwards [p (Vq+t+A),p (Vq+t+A+v)] with n h0 h1 m u
  specialize h0 m u; specialize h1 m u
  let x:= horizontalPrice T i * decay n (Real.log 2); let M:=game m; let V':= Real.exp (Vq*M); let T':= Real.exp (t*M); let C':= Real.exp (v*M); let y:=Real.exp (A*M)
  have hT : x*(V'*T'*y) ≤ ε/2 := by simp only [add_mul,Real.exp_add] at h0; exact h0
  have hC : x*(V'*T'*y*C') ≤ ε/2 := by simp only [add_mul,Real.exp_add] at h1; exact h1
  change y * ((1 + Real.exp ((Ds i) *_)) * (x*V') * Real.exp (thermalCost C R _ τ i * _)) ≤ _; rw [sites_postage,←mul_assoc (thermalCost ..),←mul_assoc (Ds i)]
  change y * ((1 + C') * (x * V') * T') ≤ _
  linarith only [hT,hC]

end Donor
end LocalLimit
end YM.CF.Py.Rate

namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
namespace Assay
variable (s:ℕ) {i k:ℕ}

private lemma billPay (p:Ferry Y s i k) (S:Finset Cover) (f:Family (tent Y H))
    (w:InTest K true S false f) (D:ℝ) (hp:pay f D):
    ‖sharp Y H s i k f-hot Y H s i k f‖ ≤ D* Donor.divisionBill Y.meter Λ.C Y.τ s (Y.ivory k) (Y.ir i):=by
  obtain ⟨hx,V⟩:= through (terrain Y H (Y.ir i) s) ((Y.voyage i).ownership s).paid.bill (w.support (momentm Y i s)).env (hp _)
  unfold hot; rw [dif_pos p.depth]
  exact (p.fire.mark_bound _ _ hx.meas V).2.2
where
 through {i k:Side}{l:Loom k}{f:Mark i}{b:ℝ}(h:i=k) (p:Measurable l) (hx:Envelope f)(w:∀ x,‖f x‖≤ b) :
    let g:Mark k:=h ▸ f; let Q:=g∘drawn l
    Envelope Q ∧ ∀ x,‖Q x‖≤ b:=by subst i; exact ⟨mark_pay p hx,fun x=> w _⟩

/-- At fixed level along all sufficiently advanced ferries, heat & sharp prices of
copy arrays transfer with arbitrarily small per-copy slack, subject only to
occupancy upper bound, eligibility and a (fixed per copy) sup Mark cost. -/
lemma flashFreeze (c d d' A:ℝ) (hc:0<c) (hd:0<d)(he:d<d') : ∀ᶠ k in atTop, ∀ i,
    Ferry Y s i k → ∀ p:ℕ, 0<p → (p:ℝ)≤A*game (Y.ir i) →
    ∀ (S:Finset Cover) (f:Family (tent Y H)), InTest K true S false f → pay f (c^p) →
    (‖sharp Y H s i k f‖≤d^p → ‖hot Y H s i k f‖ ≤ d'^p) ∧
    (‖hot Y H s i k f‖≤d^p → ‖sharp Y H s i k f‖ ≤ d'^p) := by
  let r:= d'/d; have hr:1<r := (lt_div_iff₀ hd).mpr (by simpa only [one_mul])
  filter_upwards [Y.UV.tendsto_atTop.eventually (Donor.shrinksAmplified (T:=Y.meter) (C:=Λ.C) («τ»:=Y.τ) s Λ.b (sub_pos.mpr hr) (c/d*A))] with k g i h p hp t S f u y
  let E:=Real.exp (c/d*A*game (Y.ir i))
  have hE:c^p≤d^p*E := by
    rw [mul_comm]; apply (div_le_iff₀ (pow_pos hd _)).mp
    rw [←div_pow]
    have hh: c/d ≤ Real.exp (c/d) := by linarith only [Real.add_one_le_exp (c/d)]
    refine (pow_le_pow_left₀ (div_pos hc hd).le hh p).trans ?_
    rw [←Real.exp_nat_mul]
    apply Real.exp_monotone
    rw [mul_comm (p:ℝ),mul_assoc]
    exact mul_le_mul_of_nonneg_left t (div_pos hc hd).le
  have q:= billPay Y H s h S f u (d^p*E) (fun _ a=> (y _ a).trans hE)
  rw [mul_assoc] at q
  have hx:= q.trans (mul_le_mul_of_nonneg_left (g _ ((Y.voyage i).domain k h.depth)) (pow_pos hd p).le)
  have hz:d^p+d^p*(r-1)≤d'^p:=calc
    _=d^p*r^1:= by ring
    _≤d^p*r^p:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr.le hp) (pow_pos hd p).le
    _=_:=by rw [←mul_pow,show d*r=d' by unfold r; field_simp]
  let a:=sharp Y H s i k f; let b:=hot Y H s i k f
  have h1:= norm_sub_norm_le a b
  have h2:= norm_sub_norm_le b a
  rw [norm_sub_rev] at h2
  constructor <;> intro w <;> linarith only [w,hx,hz,h1,h2]

end Assay
end YM.CF.Buffered.Afterglow.Tower
