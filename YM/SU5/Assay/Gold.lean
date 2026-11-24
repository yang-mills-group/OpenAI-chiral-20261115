import YM.SU5.Assay.Inlay
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
open Glaze Ballad
local notation "τ"=>P.tock
local notation "ι"=>P.walk j
local notation "β"=>P.rawBase j x
local notation "σ"=>P.rawSlot j x
local notation "γ"=>P.actOne j x
local notation "Δ"=>P.actTwo j x
variable (M:P.Menagerie)(A:ℕ→P.Glaze)(I:Set P.Court){a b c d:ℝ}
local notation "D"=>P.inlay A M I
local notation "η"=>P.badge A M I
local notation "μ"=>P.scrap A M I
local notation "€"=>P.electro M
/-! Accounting the repriced lock even at minimal chronological clearance
 of *advertised* inlay; statement includes old pole's coefficient in
 construction, but NOT an estimate of error to an old pole. The target
 is the owner's pole itself, dressed by these amplitudes. -/

/-- Coefficient if priced on polar legs. -/
def electrum (Z:Lead.Clan)(n:Bool):ℂ:= if n then star (€ Z) else (€ Z)
local notation "Ω'"=>P.electrum M
lemma electrum_active (Z:Lead.Clan)(n:Bool): Ω' Z n ≠0:=by
 cases n <;> simp [electrum,electro_alive]
lemma electrum_norm (Z:Lead.Clan)(n:Bool): ‖Ω' Z n‖=‖€ Z‖:=by cases n <;> simp [electrum]
lemma inlay_glows (n:Bool)(s:ℕ)(Z:Lead.Clan):β (ι n (serial (D Z) s))=Ω' Z n•β (ι n (serial (η Z) s)):=by
 have h:β (serial (D Z) s)= € Z•β (serial (η Z) s):=by funext; exact Glaze.coat_pay ..
 cases n; exact h
 unfold walk electrum
 simp only [↓reduceIte,P.rawBase_kiss,h,P.rawOther_scale]
lemma sampler_smul (t:ℕ)(F:SampleDose)(z:ℂ)(u:Vantage→X):P.sampler j x t F (z•u)=z•P.sampler j x t F u:=by
 unfold sampler
 rw [smul_sum];exact Finset.sum_congr rfl (fun y _=>by rw [Pi.smul_apply,P.charter_smul,smul_comm _ z])
lemma inlay_slot (n:Bool)(F:SampleDose)(s t:ℕ)(a b:ℝ)(Z:Lead.Clan):
 σ t (ι n (serial (D Z) s)) a b F=Ω' Z n • σ t (ι n (serial (η Z) s)) a b F:=by
 unfold rawSlot
 rw [P.inlay_glows,←P.sampler_smul]; rfl
variable {P j x M A I}
namespace Lock
variable {v e:ℝ} {s t u:ℕ}{Z Y₁:Lead.Clan}{F G:SampleDose}
variable (h:P.Lock j x A M I s v e)
include h
local notation "f" Z:max=>serial (D Z) s
local notation "g"=> serial A s
lemma gild (n:Bool)(p:Walled j F a b (τ s (D Z s).w)):
 ‖σ t (ι n (f Z)) a b F-Ω' Z n•σ t (ι n g) a b F‖≤ ‖€ Z‖*(P.gridMass F t*prismGap (μ s)):=by
 rw [P.inlay_slot,←smul_sub,norm_smul,electrum_norm]
 exact mul_le_mul_of_nonneg_left (h.raw_once n p) (norm_nonneg _)
lemma gild_pair (n m:Bool)(p:Walled j F a b (τ s (D Z s).w))(q:Walled j G c d (τ s (D Y₁ s).w)):
 ‖σ t (ι n (f Z)) a b F*σ u (ι m (f Y₁)) c d G-(Ω' Z n*Ω' Y₁ m)•(σ t (ι n g) a b F*σ u (ι m g) c d G)‖≤ ‖€ Z‖*‖€ Y₁‖*(P.gridMass F t*P.gridMass G u*(2*prismGap (μ s))):=by
 rw [P.inlay_slot,P.inlay_slot,smul_mul_assoc,mul_smul_comm,smul_smul,←smul_sub,norm_smul,norm_mul,electrum_norm,electrum_norm]
 exact mul_le_mul_of_nonneg_left (h.raw_joint n m p q) (by positivity)

omit h in
private lemma pearl (g₁ g₂:X)(z:ℂ):
 ‖inner ℂ Vac (g₁ Vac)- z*inner ℂ Vac (g₂ Vac)‖≤‖g₁-z•g₂‖:=by
 rw [←inner_smul_right,←ContinuousLinearMap.smul_apply]
 exact P.vacant_diff ..
lemma spoken (n:Bool)(p:Walled j F a b (τ s (D Z s).w))(k:s≤t):
 ‖γ (D Z s) n F s t-Ω' Z n*γ (A s) n F s t‖≤ ‖€ Z‖*(P.gridMass F t*prismGap (μ s)):=by
 let v:=Walled.grow (badge_width A M I s Z) p
 rw [actOne_price n _ p k,actOne_price n _ v k]
 exact (pearl _ _ _).trans (h.gild n p)
lemma spoken_pair (n m:Bool)(p:Walled j F a b (τ s (D Z s).w))(q:Walled j G b d (τ s (D Y₁ s).w))(k:s≤t):
 ‖Δ (D Z s) n F (D Y₁ s) m G s t-(Ω' Z n*Ω' Y₁ m)*Δ (A s) n F (A s) m G s t‖≤ ‖€ Z‖*‖€ Y₁‖*(P.gridMass F t*P.gridMass G t*(2*prismGap (μ s))):=by
 let f₁:=Walled.grow (badge_width A M I s Z) p
 let f₂:=Walled.grow (badge_width A M I s Y₁) q
 rw [actTwo_price n m _ _ p q k,actTwo_price n m _ _ f₁ f₂ k]
 exact (pearl _ _ _).trans (h.gild_pair n m p q)
end Lock
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
