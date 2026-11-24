import YM.SU5.Selected.Cairn.Season
import YM.SU5.Selected.Twirl.Celeste
import YM.SU5.Selected.Twirl.Swan
import YM.SU5.Selected.Cor.Treasure
import YM.SU5.Selected.Cor.Battery
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
variable {F':Coast→ Wq A.marks}(V₀:Effigy Y H Γ b' v' δ C₁ ε A w' G F' F)  -- HERE clarify F is old symbol ??? printed below
variable (s:ℕ)
local notation "p"=> A.Broad
local notation "ϱ"=> screen Y H V₀.first_
local notation "r" f:max=> (Mezz.Sermon.solitude A K (V₀.first_.stationed Y H) f).val
local notation "θ" X:max=> Tower.mirror (K) O 0 X*X
open Tender (stint rapids)

private lemma limits_more (v:ℝ)(h:10000≤v): 3*Real.exp (1-v)≤ 3/10000:=by
 -- avoid ~lin errors
 have hp: Real.exp (1-v) ≤1/10000:=by
    rw [show (1-v)= -(v-1) from by ring,Real.exp_neg,← one_div]; apply one_div_le_one_div_of_le (by norm_num); linarith [Real.add_one_le_exp (v-1)]
 linarith only [hp]

open Papal.Convent (crew PriceE TipC guardFee enter pass_key stellar)
open CF.Pannier.Chancel.Attic.Cairn CF.Pannier.Chancel.Attic.Cairn.Giant
variable {M:Giant} {β:M.Notes → Crest.Rail.basisRule}{Cβ γ:ℝ}(pβ:PriceE TipC Γ (crew Y H) M β Cβ γ)(vβ:guardFee M ≤ Λ.h)(uβ:Λ.d≤Convent.enter)(sc:Scooped Λ)
local notation "rM" x:max => (SpireBook.bouquet M K x).val
local notation "ρ·"=> 3*Real.exp (1-Γ)
def petite {W:Window.Family}(x:SpireBook M K W) : Test:= gentle Y H (Commission.blush (x.bouquet M K)).widen
local notation "ϱM"=> petite Y H
include V Q Qc C Ψ hΨ pβ
lemma starC {W:Window.Family}(x:SpireBook M (tent Y H) W) {D':ℝ}(u:‖E s (θ (rM x))‖ ≤ D') : ‖E s (rM x)‖^2 ≤ D' ∧ (∫ i, ‖(m (T i)) s (ϱM x)‖^2 ∂Ψ.μ) ≤ D' :=by
 let f:=rM x; let g:= ϱM x; let z:= asField Y H O false s g (Commission.blush (x.bouquet M K)).widen (by rw [area0]; exact M.broad_region K (by rw [show M.timeGap=(crew Y H).timeGap from (pass_key Y H pβ).1]; exact Nat.le_add_right _ _))
 let X':= actor Y H s Q.circuit O 0 false (C 3) z; let y:=cap Y H V s Q Qc (O) false (C 3) g Ω
 have hp:inner ℂ X' X'=E s (θ f):= by unfold X'; rw [stems Y H V,area0]; rfl
 have hu: ‖y‖^2 ≤ D' :=by
    have hx: ‖X'‖ ^2 ≤ D':= (@inner_self_eq_norm_sq ℂ _ _ _ _ X').symm.trans_le ((congrArg Complex.re hp).trans_le ((Complex.re_le_norm _).trans u)) -- maybe lemma args
    have hN : ‖y‖≤ ‖X'‖:=by unfold y; rw [show g=toTest Y H O false s z from Subtype.ext rfl,cap_prepares]; exact (R).norm_orthogonalProjectionOnto_apply_le X'
    exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans hx
 constructor
 · apply le_trans _ hu; apply pow_le_pow_left₀ (norm_nonneg _); change ‖E s g.val‖≤_; rw [←inspected Y H V s Q Qc O false (C 3)]; exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans_eq (by rw [ground_normalized,one_mul]) -- signature
 change (∫ i, ‖(T i) ((U s) g)‖^2∂Ψ.μ)≤ D'; rw [Localization.Canton.sees_star_sq (X:=basisRoom Y H V Q O false (C 3)) Ω Ψ hΨ]; exact hu

omit V Q Qc C Ψ hΨ pβ
private abbrev Triple:=
 SU.Slot ⊕ ((Window.Family × Bool) ⊕ (Window.Family × Bool))
/-private abbrev BothSlots:= SU.Slot ⊕ (Window.Family × Bool) -/
private lemma litM {X:Type}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]
   {F:X→Prop}(u:∀ᵐ x∂μ,F x) (L1: (Triple)→X→ℝ)
   (v:10000 ≤ Γ) (a:∀ k:Triple, Integrable (fun x=> L1 k x^(2:ℕ)) μ)
   (pL:∀ k,(∫ x, L1 k x ^ (2:ℕ)∂μ) ≤3* Real.exp (1-Γ))
   (g:∀ i x,0≤L1 i x) : ∃ x:X,F x∧ ∀ i,L1 i x < 1/2:=by
 classical
 let z(x:X) := ∑ i,L1 i x^2
 let f(k:Triple)(x:X):= L1 k x^2
 have hu:(∫ x,z x ∂μ) < (1/2:ℝ)^2:=by
    unfold z; rw [integral_finsetSum _ (fun i _=> a i)]; refine (sum_le_sum (s:= (univ:Finset (Triple))) (fun i _=> (pL i).trans (limits_more Γ v))).trans_lt ?_; rw [sum_const,card_univ,Fintype.card_sum,Fintype.card_sum,SU.slots,Fintype.card_prod,Fintype.card_bool,show Fintype.card Window.Family=6 from (by decide)]; norm_num
 have hA:∃ᵐ x∂μ,z x < (1/2:ℝ)^2:=by
    by_contra! p'; have hv:∀ᵐ x ∂ μ, (1/2:ℝ)^2 ≤ z x:= (not_frequently.mp (by simpa using p')).mono fun i v=> le_of_not_gt v
    exact hu.not_ge (by simpa [z] using integral_mono_ae (integrable_const ((1/2:ℝ)^2)) (integrable_finsetSum _ (fun i _=> a i)) hv)
 obtain ⟨x,h,z'⟩:= (hA.and_eventually u).exists; exact ⟨x,z',fun i=> (sq_lt_sq₀ (g i x) (by norm_num)).1 (lt_of_le_of_lt (single_le_sum (f:=fun i=> L1 i x ^2) (fun _ _=> sq_nonneg _) (mem_univ i)) h)⟩ -- name clash z
-- cp3 repeat Section from Cast.assigns, now same s poss both. χ primary=3. Variation Uniform or Born before deadline.
include V Q Qc Ψ hΨ V₀
variable {q d w:ℕ}{C₀ T₀:ℝ} (P : Council.Choir Y H q d w C₀ T₀ Γ) (hp:10000 ≤ Γ)
open Council Survival OS.Ground
local notation "B"=> payout d q w
local notation "bM"=> Survival.camp B
local notation "S"=> Sen (Survival.camp B) B
include C P hp eX
local notation "Y₀" v:max=> escort Y H V Q Qc O false (C 3) v (C v)
local notation "ξ" v:max=> phaseRead Y H V Q Qc v (C v)
-- combined choices. prove B' before. Main type heavy. all v includes esteem vs primary? primary extreme and `∀a, ∃ Birthplace...`. need χ3 actual LoneVac for retinue? no, but matching with χ primary for `consensus_ex`. need exposure matching C3 birth escorts in particular χ=escort 3 at a=3. show escort primary eq via groundIso p. can pick arbitrary `V'` for primary and get LoneVac if needed via equality; cheaper use escorted at 3 transported price. 
include pβ vβ uβ sc
theorem antilles (u : ℕ) (V' : ∀ v i, Birthplace Y H V Q Qc v false (C v) ((L v).character i)) :
    ∃ (F' : SU.Slot→Family K) (F₁:∀ W:Window.Family,Bool→ Sermon A K W) (Xβ:∀ W:Window.Family,Bool→SpireBook M K W) (s c c' cm : ℕ) (x : Ψ.X), u ≤ s ∧
      extremeJoint Y H Q false (m (T x)) ∧ printedHere Λ l s A.Broad (cabin c') ∧ (∀ W:Window.Family, Mezz.Duet K A (stint Λ.block A.marks) (F₁ W false) (F₁ W true)) ∧
      printedHere Λ l s M.Broad (cabin cm) ∧ (∀ W:Window.Family, Equatorial M K W (Xβ W false) (Xβ W true)) ∧
      ∀ v : Axis, LoneVac Y H V Q Qc v false (C v) (V' v x) ∧
        Law Y H V Q Qc v false (C v) (L v) ∧
        marked Y H V Q Qc v false (C v) ((L v).character x)=m (T x) ∧
        (∀ z: SU.Slot, Witness Y H V Q Qc v (C v) ((Y₀ v) (T x)) (F' z) z s S (booty bM d q) (cabin c) (1/2)) ∧
        (∀ z:Window.Family× Bool, ‖E s (θ (r (F₁ z.1 z.2)))‖≤ 3*Real.exp (1-Γ) ∧ ‖E s (r (F₁ z.1 z.2))‖<1/2 ∧ ‖(ξ v) ((Y₀ v) (T x)) s (r (F₁ z.1 z.2))‖ <1/2) ∧
        (∀ z:Window.Family× Bool, ‖E s (θ (rM (Xβ z.1 z.2)))‖≤ ρ· ∧ ‖E s (rM (Xβ z.1 z.2))‖<1/2 ∧ ‖(ξ v) ((Y₀ v) (T x)) s (rM (Xβ z.1 z.2))‖ <1/2) := by
 obtain ⟨s,⟨h,hS⟩,Xc,Xm⟩:= (((glimpses Y H C₀ T₀ Γ P V O).and (eventually_ge_atTop u)).and ((V₀.paired_choice Y H V).and (stellar Y H pβ vβ uβ sc V (by linarith only [hp])))).exists
 choose F' pF e t0 v using h; choose P₁ P₂ s₁ s₂ pF₁ using Xc
 let F₁ (i:Window.Family)(j:Bool):= if j then P₂ i else P₁ i; have cS(i:Window.Family × Bool) : ‖E s (θ (r (F₁ i.1 i.2)))‖≤3*Real.exp (1-Γ):=by unfold F₁; split_ifs; exact s₂ _; exact s₁ _
 choose XF YF pX qX lX using Xm
 let Xβ (i:Window.Family)(j:Bool):= if j then YF i else XF i; have mS(i:Window.Family × Bool) : ‖E s (θ (rM (Xβ i.1 i.2)))‖≤3*Real.exp (1-Γ):=by unfold Xβ; split_ifs; exact qX _; exact pX _
 obtain ⟨cm,dpM⟩:= (fundCabin Λ l s M.Broad).exists
 obtain ⟨c,u⟩:= (fundCabin Λ l s S).exists; obtain ⟨c',dP⟩:= (fundCabin Λ l s (p)).exists
 have H'(z): PhysicalTexture Y H (F' z) z s S (booty bM d q) (cabin c) (2/precisionAt Λ s) :=by have h:= positiveScale Λ s; exact ⟨P.corn.cents bM, stake_centers Y H bM d q w, by positivity, fun i h a=> endpoints_far Λ s (h a), e z,pF z,u⟩
 let i' (z:SU.Slot) (i : Ψ.X):= (m (T i)) s ((H' z).enter Y H false); let k' (z:Window.Family× Bool)(i:Ψ.X):= (m (T i)) s (ϱ (F₁ z.1 z.2))
 have hk z:= variance_light Y H V Q Qc O C P Ψ hΨ s (show 0 ≤ 3*Real.exp (1-Γ) by positivity) ((H' z).enter Y H false) (FilTest (pF z)).widen (v z)
 have he(z:Window.Family × Bool):= star_budget Y H V Q Qc C Ψ hΨ V₀.first_ s (F₁ z.1 z.2) (cS z)
 have hW(z):Continuous (k' z):= (many_accept Y H V Q Qc O false (C 3) Ψ hΨ s (ϱ (F₁ z.1 z.2))).1
 let m' (z:Window.Family× Bool)(i:Ψ.X):= (m (T i)) s (ϱM (Xβ z.1 z.2))
 have hβ(z:Window.Family × Bool):= starC Y H V Q Qc C Ψ hΨ s pβ (Xβ z.1 z.2) (mS z)
 have hmW(z):Continuous (m' z):= (many_accept Y H V Q Qc O false (C 3) Ψ hΨ s (ϱM (Xβ z.1 z.2))).1
 haveI:= hΨ.normalized; let P1 (i : Ψ.X):= ∀ v:Axis,LoneVac Y H V Q Qc v false (C v) (V' v i)
 let X0: Triple → Ψ.X → ℝ := Sum.elim (fun z i=> ‖1+i' z i‖) (Sum.elim (fun z i=> ‖k' z i‖) (fun z i=> ‖m' z i‖))
 -- cut costs lemma. UB Ɵ. Lane.
 have hz(t:Triple): Continuous (X0 t):=by cases t with|inl z=> exact ((continuous_const (y:=(1:ℂ))|>.add (hk z).1).norm)|inr z=> cases z with| inl z=> exact (hW z).norm|inr z=> exact (hmW z).norm
 obtain ⟨x,f,lx⟩:= litM (F:=P1) (typical Y H V Q Qc O C Ψ hΨ V' eX) X0 hp (fun t=> ((hz t).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun t=> by cases t with|inl z=> exact (hk z).2|inr z=> cases z with|inl z=> exact (he z).2|inr z=> exact (hβ z).2) (fun t=> by cases t with|inl z=> exact fun _=>norm_nonneg _|inr z=> cases z<;> exact fun _=>norm_nonneg _)
 have β (v:Axis): marked Y H V Q Qc v false (C v) ((L v).character x)=m (T x) := funext fun i => funext fun y=> unchanged Y H V Q Qc O false (C 3) v (C v) (Ψ.character x) i y
 refine ⟨F',F₁,Xβ,s,c,c',cm,x,hS,(β O ▸ owner Y H V Q Qc O false (C 3) (V' O x) (f 3)),dP,(fun w=> (by dsimp only [F₁]; rw [if_neg (by decide : ¬false=true), if_pos rfl]; exact pF₁ w)), dpM,(fun W=> (by dsimp only [Xβ]; rw [if_neg (by decide : ¬false=true), if_pos rfl]; exact lX W)),fun y=> ⟨f y,Selection.brought Y H V Q Qc O false (C 3) Ψ hΨ y (C y),β y,fun z=>?_,fun z=>?_,fun z=>?_⟩⟩
 · let read:= phaseRead Y H V Q Qc y (C y) ((L y).character x)
   have e1:read s (F' z)= i' z x:= (phase_read Y H V Q Qc y (C y) s _ ((H' z).enter Y H false)).trans (congrFun (congrFun (β y) s) _)
   have h2: ‖1+ read s (F' z)‖ < 1/2:= e1 ▸ lx (.inl z)
   apply witnesses Y H V Q Qc y (C y) (by norm_num) (H' z) (t0 z); have h:= norm_sub_norm_le (1:ℂ) (-(read s (F' z))); rw [norm_one,norm_neg,sub_neg_eq_add] at h; change 1/2< ‖read s (F' z)‖; linarith only [h2,h] -- maybe too cost unfolding
 · have he₀:=phase_read Y H V Q Qc y (C y) s ((Y₀ y) (T x)) (ϱ (F₁ z.1 z.2)); exact ⟨cS z, sip (norm_nonneg _) (he z).1 hp, (show (ξ y) ((Y₀ y) (T x)) s (r (F₁ z.1 z.2))= k' z x from he₀.trans (congrFun (congrFun (β y) s) _)) ▸ lx (.inr (.inl z))⟩


 have he₀:=phase_read Y H V Q Qc y (C y) s ((Y₀ y) (T x)) (ϱM (Xβ z.1 z.2)); exact ⟨mS z, sip (norm_nonneg _) (hβ z).1 hp, (show (ξ y) ((Y₀ y) (T x)) s (rM (Xβ z.1 z.2))= m' z x from he₀.trans (congrFun (congrFun (β y) s) _)) ▸ lx (.inr (.inr z))⟩


end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern
#print axioms starC
#print axioms antilles
#check @antilles
