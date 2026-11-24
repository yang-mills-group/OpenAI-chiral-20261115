import YM.SU5.May.Stamped
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine

open Aria Germ Alliance SelectionAnalysis Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "C" => P.room
local notation "Y" => P.run
local notation "L" => P.large
local notation "P₁" => P.par
local notation "V" => P.law
local notation "G" => P.projection
local notation "H" => P.history
local notation "H₁" => P.projection.clipped
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J
open Selected (doorstep indoor fort ride peninsula vocation displacement compass_origin placement atEstate vocate)
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget
local notation "ℳ" => marks (timeMesh P.par)
local notation "Q" => Follows Y L V G j (C j) χ
local notation "K" => P.calibration
local notation "D'" => Domain Y L G
local notation "X'" => Sky K
local notation "Hr" => Selected.ride Y L V H H₁ j false (C j) χ
local notation "R" => peninsula Y L V H H₁ j false (C j) χ
local notation "Pₓ" => P.maySaunters x j
local notation "P₀" => (Pₓ).orthogonalProjectionOnto
local notation "M" => P.mayFort x j
local notation "Ω'" => vocation Y L V H H₁ j false (C j) χ
local notation "ι" => OSvector Y L V G j (C j) χ
local notation "Ψ" => osValue Y L V G j (C j) χ
local notation "α" => P.glasshouseCharacter 3 x
local notation "Z" => P.mayCarries x j
local notation "mv" => FirstWindows.move K
local notation "ej" => Chambers.eject j
local notation "tk" t:max => FirstWindows.ticket Y L G t
variable (F U: SampleDose)(D : P.MayBooth F reviewEarlierBox)(E : P.MayBooth U reviewLaterBox)
open MacroGrid SatinNucleus SatinJets DoseTravel
variable (A:ℕ → P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)
-- named marks. They are literally the markings of `exists_disclosed_satin_native_contrast`.
local notation "W" => P.soldTrumpet A c r n w
local notation "Φ" a:max i:max t:max => P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F
local notation "Λ" a:max i:max t:max => P.prepared t ((P.soldTrumpet A c r n w) a i) U
variable (v : ∀ j:Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
variable (g h:ℕ)(T:P.HandleWith x c r A n)
local notation "Δ" => P.mayGap j F U D E
local notation "dℝ" => Real.toNNReal ((P.mayGap j F U D E):ℝ)
variable (a b:Lead.Clan)(i t:ℕ)

-- fort purchase on compass projection of individual *kets*, then the pair. This matters for
-- testing ACTUAL membership in weak WOT ket Criterion. In particular `mayFortKetPair` is true
-- *before* having BoostBacking! and the kets themselves computed from the actual matrix.
local notation "a₀" a:max i:max t:max => P.mayHead x j F D A c r n w a i t
local notation "a₁" a:max i:max t:max => P.mayToe x j U E A c r n w a i t
local notation "h₀" j:max=> Real.toNNReal (-(D.high j:ℝ))
local notation "h₁" j:max=> Real.toNNReal (E.low j:ℝ)
-- exact costs of the given probes at consultation t after accounting for width, ejection origin at (time) 0.
def preLeft := (Hr).E (h₀ j) (star (a₀ a i t) Ω)
def preRight := (Hr).E (h₁ j) ((a₁ a i t) Ω)
def preLeftS := (R).E (h₀ j) ((star (Z (a₀ a i t))) Ω')
def preRightS := (R).E (h₁ j) ((Z (a₁ a i t)) Ω')
-- general reflection & heat
lemma mayStarCarry (B:(I₀).Op) : star (Z B)= Z (star B) := by
  ext1 z; apply ext_inner_left ℂ; intro y
  rw [show star (Z B) = ContinuousLinearMap.adjoint (Z B) from rfl, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (P₀ (B y.val)) (show M from z) = inner ℂ y (show M from P₀ ((star B) z.val))
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right («K»:=Pₓ) _ _).trans
    ((ContinuousLinearMap.adjoint_inner_right B _ _).symm.trans
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=Pₓ) _ _).symm)
lemma mayProject_heat (B:I₀) (s:ℝ≥0) : P₀ ((Hr).E s B) = (R).E s (P₀ B) := by
  apply ext_inner_left ℂ; intro x'
  -- type instances via calc
  calc
    inner ℂ x' _ = inner ℂ (x'.val:I₀) ((Hr).E s B) := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=Pₓ) x' _
    _ = inner ℂ (((R).E s x').val:I₀) B := ((Hr).swing s (x'.val:I₀) B).symm
    _ = inner ℂ ((R).E s x') (show M from P₀ B) := (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=Pₓ) ((R).E s x') B).symm
    _ = _ := (R).swing s _ _
lemma mayLeft_project : P₀ (P.preLeft x j F D A c r n w a i t) = P.preLeftS x j F D A c r n w a i t := by
  unfold preLeft preLeftS; rw [mayProject_heat,mayStarCarry,mayProjectionVac]
lemma mayRight_project : P₀ (P.preRight x j U E A c r n w a i t) = P.preRightS x j U E A c r n w a i t := by
  unfold preRight preRightS; rw [mayProject_heat,mayProjectionVac]
lemma mayGap_split : dℝ=h₀ j + h₁ j:= by
  ext1
  have h : 0 ≤ -(D.high j:ℝ) := P.mayEarly_negative j F D; have v : 0 ≤ (E.low j:ℝ) := P.mayLate_positive j U E
  rw [NNReal.coe_add]; simp_rw [Real.coe_toNNReal (P.mayGap j F U D E:ℝ) ((show 0≤(2:ℝ) from by norm_num).trans (P.mayTotal_positive j F U D E).le), Real.coe_toNNReal _ h, Real.coe_toNNReal _ v]; change (E.low j:ℝ)-(D.high j:ℝ)=_; ring
lemma mayFortKetPair : inner ℂ (P.preLeftS x j F D A c r n w a i t) (P.preRightS x j U E A c r n w b i t)= P.fortPrism x j F U D E A c r n w i t a b:=by
  unfold preLeftS preRightS
  rw [(R).swing, ←ContinuousLinearMap.comp_apply ((R).E _) ((R).E _), ←(R).time, ←mayGap_split, show star (Z (a₀ a i t))= ContinuousLinearMap.adjoint (Z (a₀ a i t)) from rfl, ContinuousLinearMap.adjoint_inner_left]; rfl

-- now fix orientation of readings themselves (j0=3) for limits.
local notation "B₀" a:max i:max t:max => P.mayHead x 3 F D A c r n w a i t
local notation "B₁" a:max i:max t:max => P.mayToe x 3 U E A c r n w a i t
local notation "gℓ" => P.preLeft x 3 F D A c r n w
local notation "gΩ" => P.preRight x 3 U E A c r n w
local notation "S₀" => P.preLeftS x 3 F D A c r n w
local notation "S₁" => P.preRightS x 3 U E A c r n w
local notation "birth" a:max i:max=> P.sold_birth x A c r n w a i T
local notation "w[" t "]"=> P.thinGridKet x t
local notation "k[u]"=> P.mayIntertwine x 3
local notation "k[S]"=> P.mayIntertwineS x 3
local notation "Uℓ" a:max i:max t:max=> (k[u]) ((w[t]) (W a i) (birth a i) (flipDose F 3))
local notation "UΩ" a:max i:max t:max=> (k[u]) ((w[t]) (W a i) (birth a i) U)
local notation "Iℓ" a:max i:max=> k[S] (P.thinKet x (W a i) (birth a i) (flipDose F 3))
local notation "IΩ" a:max i:max=> k[S] (P.thinKet x (W a i) (birth a i) U)
local notation "ιz" z:max=> OSvector Y L V G 3 (C 3) (P.mayChar x 3) z
variable {K':P.Register} {μ:ℝ}{s k:ℕ}
variable (Z':P.FullPrismLab x A c r n w v g h T μ F U reviewEarlierBox reviewLaterBox s k K')
local notation "t!" i:max=> c (n i)
local notation "α'"=> P.advocate 3 x 3
local notation "H'"=> P.mayHil x 3
local notation "P'"=> P.mayFort x 3
abbrev mayThinLeft (μ:ℝ) : P.mayFort x 3 := (k[S]) (DoseTravel.beam (P.ManyF 3 α') F (P.earlierProfile x v w μ a))
abbrev mayThinRight (μ:ℝ) : P.mayFort x 3 := (k[S]) (DoseTravel.beam (P.ManyF 3 α') U (P.laterProfile x v w μ a))
include Z'
lemma mayEver_warm : ∀ᶠ i in atTop,∀ t:ℕ,t! i ≤ t→ ∀ a:Lead.Clan, gℓ a i t = Uℓ a i t ∧ gΩ a i t = UΩ a i t:= by
  filter_upwards [Z'.then_read.epoch, P.mayEver_stamped x F U D E A c r n w v g h T Z'] with i ep q t p a
  obtain ⟨d,hv,u,r⟩:= (ep a a).earlier t p; obtain ⟨u',r'⟩:= (ep a a).laterK t p; obtain ⟨f,f'⟩:= q t p 3 a
  let L' := Domain Y L G false (flank 3 0)
  let b := (⟨(tk t) d,ticket_mem Y L G (P.mayInside_loose 3 t d u)⟩ : L'); let d':= Λ a i t; let c':=(⟨(tk t) d', ticket_mem Y L G (P.mayInside_loose 3 t d' u')⟩ : L')
  constructor
  · have he: flipMark 3 K ((tk t) (Φ a i t))= b.val:= by
      erw [flipMark_ticket]; rw [←hv]; change (tk t) (aureole _ _ 0 (aureole _ _ 0 d))=(tk t) d; rw [aureoleTwice]
    refine (P.mayEarlyKet x 3 F D f.pays b he.symm).symm.trans ?_
    change ιz b=(k[u]) _; rw [←r]; exact (P.mayPrice x 3 t d u).symm
  refine (P.mayLateKet x 3 U E f'.pays c' rfl).symm.trans ?_; change ιz c'=(k[u]) _; rw [←r']; exact (P.mayPrice x 3 t d' u').symm

lemma mayMesh_limit : ∀ᶠ i:ℕ in atTop,∀ a:Lead.Clan, Tendsto (fun t=> gℓ a i t) atTop (𝓝 ((Iℓ a i).val:H')) ∧
    Tendsto (fun t=> gΩ a i t) atTop (𝓝 ((IΩ a i).val:H')) := by
  filter_upwards [Z'.then_read.epoch,P.mayEver_warm x F U D E A c r n w v g h T Z'] with i q u a; let s:= q a a
  refine ⟨((k[u]).continuous.continuousAt.tendsto.comp s.gridEarly).congr' ?_, ((k[u]).continuous.continuousAt.tendsto.comp s.gridLate).congr' ?_⟩
  · exact (eventually_ge_atTop (t! i)).mono fun t h=> (u t h a).1.symm
  exact (eventually_ge_atTop (t! i)).mono fun t h=> (u t h a).2.symm

lemma mayThin_limit (a:Lead.Clan) : Tendsto (fun i=> Iℓ a i) atTop (𝓝 (P.mayThinLeft x F w v a μ)) ∧
    Tendsto (fun i=> IΩ a i) atTop (𝓝 (P.mayThinRight x U w v a μ)) :=
   ⟨(k[S]).continuous.continuousAt.tendsto.comp (Z'.then_read.leftM a), (k[S]).continuous.continuousAt.tendsto.comp (Z'.then_read.rightM a)⟩
omit Z' in
lemma mayThin_matrix (μ:ℝ):P.readPrism x v w μ F U a b=inner ℂ (P.mayThinLeft x F w v a μ) (P.mayThinRight x U w v b μ):=
  ((k[S]).inner_map_map _ _).symm
lemma mayIndoor_strongLimit {t:ℕ→ℕ}(b:∀ᶠ i in atTop,t! i ≤ t i)(a:Lead.Clan):
    Tendsto (fun i=>gℓ a i (t i)) atTop (𝓝 ((P.mayThinLeft x F w v a μ).val:H')) ∧
    Tendsto (fun i=>gΩ a i (t i)) atTop (𝓝 ((P.mayThinRight x U w v a μ).val:H')):= by
  have he:= (P.mayEver_warm x F U D E A c r n w v g h T Z').and b; let Y':= Z'.then_read.bothM a t b
  exact ⟨((k[u]).continuous.continuousAt.tendsto.comp (Y'.1)).congr' (he.mono fun i h=> (h.1 (t i) h.2 a).1.symm), ((k[u]).continuous.continuousAt.tendsto.comp (Y'.2)).congr' (he.mono fun i h=> (h.1 (t i) h.2 a).2.symm)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
