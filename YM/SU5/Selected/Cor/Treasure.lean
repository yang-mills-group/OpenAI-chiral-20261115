import YM.SU5.Selected.Cor.Amber
import YM.SU5.Selected.Cor.Guild
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
local notation "m" χ:max => marked Y H V Q Qc (3:Axis) false (C 3) χ
open CF.Pannier.Chancel Tapestry Papal SatinVerification
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
open Crest.Airy (Coast Wq)
open Mileage
attribute [local instance] opCStarAlgebra
namespace Fern
local notation "B0"=> 3
local notation "O"=> (3:Axis)
local notation "R"=> Aurora Y H V Q (O) false (C 3)
local notation "U" s:max=> liftCap Y H V Q Qc O false (C 3) s
local notation "Ω"=> seat0 Y H V Q O false (C 3)
variable (Ψ:Horizon Y H V Q Qc 3 false (C 3)) (hΨ:Law Y H V Q Qc 3 false (C 3) Ψ)
local notation "L" v:max => emigrant Y H V Q Qc O false (C 3) Ψ v (C v)
local notation "T" i:max => Ψ.character i
variable {X: Rack Λ l} {Z₀:Clay Λ l} (eX: Exhibition Y H i k I E X Z₀)
  {A:Mezz} {b' v' w':ℕ} {C₁ δ ε Γ:ℝ}{G F:Coast→ Wq A.marks}
   (Δ:Delay Y H b' v' δ Γ C₁ ε A w' G F)
local notation "Δ₀" => Δ.stationed Y H
include Δ
-- marks across all rung. Harvard variation.
local notation "π₀"=> phaseRead Y H V Q Qc O (C 3)
local notation "p"=> A.Broad
variable (s:ℕ)
def screen {W:Window.Family}(F':Sermon A (tent Y H) W) : Test:= gentle Y H (Commission.blush (F'.solitude A (K) Δ₀)).widen
local notation "ϱ"=> screen Y H Δ
local notation "r" v:max=> (Sermon.solitude A K Δ₀ v).val
local notation "θ" X:max=> Tower.mirror (K) O 0 X*X
include V Q Qc C Ψ hΨ
lemma star_budget {W:Window.Family}(x:Sermon A (tent Y H) W) {D':ℝ}(u:‖E s (θ (r x))‖ ≤ D') : ‖E s (r x)‖^2 ≤ D' ∧ (∫ i, ‖(m (T i)) s (ϱ x)‖^2 ∂Ψ.μ) ≤ D' :=by
 let f:=r x; let g:= ϱ x; let z:= asField Y H O false s g (Commission.blush (x.solitude A K Δ₀)).widen (by rw [area0]; exact A.broad_hour K (Δ.raised Y H))
 let X':= actor Y H s Q.circuit O 0 false (C 3) z; let y:=cap Y H V s Q Qc (O) false (C 3) g Ω
 have hp:inner ℂ X' X'=E s (θ f):= by unfold X'; rw [stems Y H V,area0]; rfl
 have hu: ‖y‖^2 ≤ D' :=by
    have hx: ‖X'‖ ^2 ≤ D':= (@inner_self_eq_norm_sq ℂ _ _ _ _ X').symm.trans_le ((congrArg Complex.re hp).trans_le ((Complex.re_le_norm _).trans u)) -- maybe lemma args
    have hN : ‖y‖≤ ‖X'‖:=by unfold y; rw [show g=toTest Y H O false s z from Subtype.ext rfl,cap_prepares]; exact (R).norm_orthogonalProjectionOnto_apply_le X'
    exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans hx
 constructor
 · apply le_trans _ hu; apply pow_le_pow_left₀ (norm_nonneg _); change ‖E s g.val‖≤_; rw [←inspected Y H V s Q Qc O false (C 3)]; exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans_eq (by rw [ground_normalized,one_mul]) -- signature
 change (∫ i, ‖(T i) ((U s) g)‖^2∂Ψ.μ)≤ D'; rw [Localization.Canton.sees_star_sq (X:=basisRoom Y H V Q O false (C 3)) Ω Ψ hΨ]; exact hu
omit V Q Qc C Ψ hΨ Δ
-- combine |Slot|45+6. enough 51 /200. add Pack originals. use arbitrary P predicates. param. 
private lemma limits (v:ℝ)(h:10000≤v): 3*Real.exp (1-v)≤ 3/10000:=by
 -- avoid ~lin errors
 have hp: Real.exp (1-v) ≤1/10000:=by
    rw [show (1-v)= -(v-1) from by ring,Real.exp_neg,← one_div]; apply one_div_le_one_div_of_le (by norm_num); linarith [Real.add_one_le_exp (v-1)]
 linarith only [hp]
lemma sip {u : ℝ} (h:0≤u)(t: u^ (2:ℕ) ≤ 3*Real.exp (1-Γ))(hP:10000≤Γ):u<1/2:= (sq_lt_sq₀ h (by norm_num)).1 (lt_of_le_of_lt t ((limits Γ hP).trans_lt (by norm_num))) -- lem order
-- single union certificate.
private abbrev LX:= SU.Slot ⊕ Window.Family
private lemma lit {X:Type}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]
   {F:X→Prop}(u:∀ᵐ x∂μ,F x) (L1: SU.Slot ⊕ Window.Family→X→ℝ)
   (v:10000 ≤ Γ) (a:∀ k:LX, Integrable (fun x=> L1 k x^(2:ℕ)) μ)
   (pL:∀ k,(∫ x, L1 k x ^ (2:ℕ)∂μ) ≤3* Real.exp (1-Γ))
   (g:∀ i x,0≤L1 i x) : ∃ x:X,F x∧ ∀ i,L1 i x < 1/2:=by
 classical
 let z(x:X) := ∑ i,L1 i x^2
 let f(k:LX)(x:X):= L1 k x^2
 have hu:(∫ x,z x ∂μ) < (1/2:ℝ)^2:=by
    unfold z; rw [integral_finsetSum _ (fun i _=> a i)]; refine (sum_le_sum (s:= (univ:Finset (LX))) (fun i _=> (pL i).trans (limits Γ v))).trans_lt ?_; rw [sum_const,card_univ,Fintype.card_sum,SU.slots,show Fintype.card Window.Family=6 from (by decide)]; norm_num
 have hA:∃ᵐ x∂μ,z x < (1/2:ℝ)^2:=by
    by_contra! p'; have hv:∀ᵐ x ∂ μ, (1/2:ℝ)^2 ≤ z x:= (not_frequently.mp (by simpa using p')).mono fun i v=> le_of_not_gt v
    exact hu.not_ge (by simpa [z] using integral_mono_ae (integrable_const ((1/2:ℝ)^2)) (integrable_finsetSum _ (fun i _=> a i)) hv)
 obtain ⟨x,h,z'⟩:= (hA.and_eventually u).exists; exact ⟨x,z',fun i=> (sq_lt_sq₀ (g i x) (by norm_num)).1 (lt_of_le_of_lt (single_le_sum (f:=fun i=> L1 i x ^2) (fun _ _=> sq_nonneg _) (mem_univ i)) h)⟩ -- name clash z
-- cp3 repeat Section from Cast.assigns, now same s poss both. χ primary=3. Variation Uniform or Born before deadline.
include V Q Qc Ψ hΨ Δ
variable {q d w:ℕ}{C₀ T₀:ℝ} (P : Council.Choir Y H q d w C₀ T₀ Γ) (hp:10000 ≤ Γ)
open Council Survival OS.Ground
local notation "B"=> payout d q w
local notation "bM"=> Survival.camp B
local notation "S"=> Sen (Survival.camp B) B
include C P hp eX
local notation "Y₀" v:max=> escort Y H V Q Qc O false (C 3) v (C v)
local notation "ξ" v:max=> phaseRead Y H V Q Qc v (C v)
-- combined choices. prove B' before. Main type heavy. all v includes esteem vs primary? primary extreme and `∀a, ∃ Birthplace...`. need χ3 actual LoneVac for retinue? no, but matching with χ primary for `consensus_ex`. need exposure matching C3 birth escorts in particular χ=escort 3 at a=3. show escort primary eq via groundIso p. can pick arbitrary `V'` for primary and get LoneVac if needed via equality; cheaper use escorted at 3 transported price. 
theorem survey (u : ℕ) (V' : ∀ v i, Birthplace Y H V Q Qc v false (C v) ((L v).character i)) :
    ∃ (F' : SU.Slot→Family K) (F₁:∀ W:Window.Family,Sermon A K W) (s c c' : ℕ) (x : Ψ.X), u ≤ s ∧
      extremeJoint Y H Q false (m (T x)) ∧ printedHere Λ l s A.Broad (cabin c') ∧
      ∀ v : Axis, LoneVac Y H V Q Qc v false (C v) (V' v x) ∧
        Law Y H V Q Qc v false (C v) (L v) ∧
        marked Y H V Q Qc v false (C v) ((L v).character x)=m (T x) ∧
        (∀ z: SU.Slot, Witness Y H V Q Qc v (C v) ((Y₀ v) (T x)) (F' z) z s S (booty bM d q) (cabin c) (1/2)) ∧
        (∀ z:Window.Family, ‖E s (θ (r (F₁ z)))‖≤ 3*Real.exp (1-Γ) ∧ ‖E s (r (F₁ z))‖<1/2 ∧ ‖(ξ v) ((Y₀ v) (T x)) s (r (F₁ z))‖ <1/2) := by
 obtain ⟨s,⟨h,hS⟩,Xc⟩:= (((glimpses Y H C₀ T₀ Γ P V O).and (eventually_ge_atTop u)).and (Δ.tallyD Y H V)).exists
 choose F' pF e t0 v using h; choose F₁ cS using Xc
 obtain ⟨c,u⟩:= (fundCabin Λ l s S).exists; obtain ⟨c',dP⟩:= (fundCabin Λ l s (p)).exists
 have H'(z): PhysicalTexture Y H (F' z) z s S (booty bM d q) (cabin c) (2/precisionAt Λ s) :=by have h:= positiveScale Λ s; exact ⟨P.corn.cents bM, stake_centers Y H bM d q w, by positivity, fun i h a=> endpoints_far Λ s (h a), e z,pF z,u⟩
 let i' (z:SU.Slot) (i : Ψ.X):= (m (T i)) s ((H' z).enter Y H false); let k' (z:Window.Family)(i:Ψ.X):= (m (T i)) s (ϱ (F₁ z))
 have hk z:= variance_light Y H V Q Qc O C P Ψ hΨ s (show 0 ≤ 3*Real.exp (1-Γ) by positivity) ((H' z).enter Y H false) (FilTest (pF z)).widen (v z)
 have he z:= star_budget Y H V Q Qc C Ψ hΨ Δ s (F₁ z) (cS z)
 have hW(z):Continuous (k' z):= (many_accept Y H V Q Qc O false (C 3) Ψ hΨ s (ϱ (F₁ z))).1
 haveI:= hΨ.normalized; let P1 (i : Ψ.X):= ∀ v:Axis,LoneVac Y H V Q Qc v false (C v) (V' v i)
 let X0: LX → Ψ.X → ℝ := Sum.elim (fun z i=> ‖1+i' z i‖) (fun z i=> ‖k' z i‖)
 -- cut costs lemma. UB Ɵ. Lane.
 have hz(t:LX): Continuous (X0 t):=by cases t with|inl z=> exact ((continuous_const (y:=(1:ℂ))|>.add (hk z).1).norm)|inr z=> exact (hW z).norm
 obtain ⟨x,f,lx⟩:= lit (F:=P1) (typical Y H V Q Qc O C Ψ hΨ V' eX) X0 hp (fun t=> ((hz t).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun t=> by cases t with|inl z=> exact (hk z).2|inr z=> exact (he z).2) (fun t=> by cases t<;> exact fun _=> norm_nonneg _)
 have β (v:Axis): marked Y H V Q Qc v false (C v) ((L v).character x)=m (T x) := funext fun i => funext fun y=> unchanged Y H V Q Qc O false (C 3) v (C v) (Ψ.character x) i y
 refine ⟨F',F₁,s,c,c',x,hS,(β O ▸ owner Y H V Q Qc O false (C 3) (V' O x) (f 3)),dP,fun y=> ⟨f y,Selection.brought Y H V Q Qc O false (C 3) Ψ hΨ y (C y),β y,fun z=>?_,fun z=>?_⟩⟩
 · let read:= phaseRead Y H V Q Qc y (C y) ((L y).character x)
   have e1:read s (F' z)= i' z x:= (phase_read Y H V Q Qc y (C y) s _ ((H' z).enter Y H false)).trans (congrFun (congrFun (β y) s) _)
   have h2: ‖1+ read s (F' z)‖ < 1/2:= e1 ▸ lx (.inl z)
   apply witnesses Y H V Q Qc y (C y) (by norm_num) (H' z) (t0 z); have h:= norm_sub_norm_le (1:ℂ) (-(read s (F' z))); rw [norm_one,norm_neg,sub_neg_eq_add] at h; change 1/2< ‖read s (F' z)‖; linarith only [h2,h] -- maybe too cost unfolding
 have he₀:=phase_read Y H V Q Qc y (C y) s ((Y₀ y) (T x)) (ϱ (F₁ z)); exact ⟨cS z, sip (norm_nonneg _) (he z).1 hp, (show (ξ y) ((Y₀ y) (T x)) s (r (F₁ z))= k' z x from he₀.trans (congrFun (congrFun (β y) s) _)) ▸ lx (.inr z)⟩
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern
#print axioms survey
#print axioms star_budget
