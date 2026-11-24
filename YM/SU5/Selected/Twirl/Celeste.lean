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

private abbrev BothSlots:= SU.Slot ⊕ (Window.Family × Bool)
private lemma lit_more {X:Type}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]
   {F:X→Prop}(u:∀ᵐ x∂μ,F x) (L1: SU.Slot ⊕ (Window.Family × Bool)→X→ℝ)
   (v:10000 ≤ Γ) (a:∀ k:BothSlots, Integrable (fun x=> L1 k x^(2:ℕ)) μ)
   (pL:∀ k,(∫ x, L1 k x ^ (2:ℕ)∂μ) ≤3* Real.exp (1-Γ))
   (g:∀ i x,0≤L1 i x) : ∃ x:X,F x∧ ∀ i,L1 i x < 1/2:=by
 classical
 let z(x:X) := ∑ i,L1 i x^2
 let f(k:BothSlots)(x:X):= L1 k x^2
 have hu:(∫ x,z x ∂μ) < (1/2:ℝ)^2:=by
    unfold z; rw [integral_finsetSum _ (fun i _=> a i)]; refine (sum_le_sum (s:= (univ:Finset (BothSlots))) (fun i _=> (pL i).trans (limits_more Γ v))).trans_lt ?_; rw [sum_const,card_univ,Fintype.card_sum,SU.slots,Fintype.card_prod,Fintype.card_bool,show Fintype.card Window.Family=6 from (by decide)]; norm_num
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
theorem surveyH (u : ℕ) (V' : ∀ v i, Birthplace Y H V Q Qc v false (C v) ((L v).character i)) :
    ∃ (F' : SU.Slot→Family K) (F₁:∀ W:Window.Family,Bool→ Sermon A K W) (s c c' : ℕ) (x : Ψ.X), u ≤ s ∧
      extremeJoint Y H Q false (m (T x)) ∧ printedHere Λ l s A.Broad (cabin c') ∧ (∀ W:Window.Family, Mezz.Duet K A (stint Λ.block A.marks) (F₁ W false) (F₁ W true)) ∧
      ∀ v : Axis, LoneVac Y H V Q Qc v false (C v) (V' v x) ∧
        Law Y H V Q Qc v false (C v) (L v) ∧
        marked Y H V Q Qc v false (C v) ((L v).character x)=m (T x) ∧
        (∀ z: SU.Slot, Witness Y H V Q Qc v (C v) ((Y₀ v) (T x)) (F' z) z s S (booty bM d q) (cabin c) (1/2)) ∧
        (∀ z:Window.Family× Bool, ‖E s (θ (r (F₁ z.1 z.2)))‖≤ 3*Real.exp (1-Γ) ∧ ‖E s (r (F₁ z.1 z.2))‖<1/2 ∧ ‖(ξ v) ((Y₀ v) (T x)) s (r (F₁ z.1 z.2))‖ <1/2) := by
 obtain ⟨s,⟨h,hS⟩,Xc⟩:= (((glimpses Y H C₀ T₀ Γ P V O).and (eventually_ge_atTop u)).and (V₀.paired_choice Y H V)).exists
 choose F' pF e t0 v using h; choose P₁ P₂ s₁ s₂ pF₁ using Xc
 let F₁ (i:Window.Family)(j:Bool):= if j then P₂ i else P₁ i; have cS(i:Window.Family × Bool) : ‖E s (θ (r (F₁ i.1 i.2)))‖≤3*Real.exp (1-Γ):=by unfold F₁; split_ifs; exact s₂ _; exact s₁ _
 obtain ⟨c,u⟩:= (fundCabin Λ l s S).exists; obtain ⟨c',dP⟩:= (fundCabin Λ l s (p)).exists
 have H'(z): PhysicalTexture Y H (F' z) z s S (booty bM d q) (cabin c) (2/precisionAt Λ s) :=by have h:= positiveScale Λ s; exact ⟨P.corn.cents bM, stake_centers Y H bM d q w, by positivity, fun i h a=> endpoints_far Λ s (h a), e z,pF z,u⟩
 let i' (z:SU.Slot) (i : Ψ.X):= (m (T i)) s ((H' z).enter Y H false); let k' (z:Window.Family× Bool)(i:Ψ.X):= (m (T i)) s (ϱ (F₁ z.1 z.2))
 have hk z:= variance_light Y H V Q Qc O C P Ψ hΨ s (show 0 ≤ 3*Real.exp (1-Γ) by positivity) ((H' z).enter Y H false) (FilTest (pF z)).widen (v z)
 have he(z:Window.Family × Bool):= star_budget Y H V Q Qc C Ψ hΨ V₀.first_ s (F₁ z.1 z.2) (cS z)
 have hW(z):Continuous (k' z):= (many_accept Y H V Q Qc O false (C 3) Ψ hΨ s (ϱ (F₁ z.1 z.2))).1
 haveI:= hΨ.normalized; let P1 (i : Ψ.X):= ∀ v:Axis,LoneVac Y H V Q Qc v false (C v) (V' v i)
 let X0: BothSlots → Ψ.X → ℝ := Sum.elim (fun z i=> ‖1+i' z i‖) (fun z i=> ‖k' z i‖)
 -- cut costs lemma. UB Ɵ. Lane.
 have hz(t:BothSlots): Continuous (X0 t):=by cases t with|inl z=> exact ((continuous_const (y:=(1:ℂ))|>.add (hk z).1).norm)|inr z=> exact (hW z).norm
 obtain ⟨x,f,lx⟩:= lit_more (F:=P1) (typical Y H V Q Qc O C Ψ hΨ V' eX) X0 hp (fun t=> ((hz t).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun t=> by cases t with|inl z=> exact (hk z).2|inr z=> exact (he z).2) (fun t=> by cases t<;> exact fun _=> norm_nonneg _)
 have β (v:Axis): marked Y H V Q Qc v false (C v) ((L v).character x)=m (T x) := funext fun i => funext fun y=> unchanged Y H V Q Qc O false (C 3) v (C v) (Ψ.character x) i y
 refine ⟨F',F₁,s,c,c',x,hS,(β O ▸ owner Y H V Q Qc O false (C 3) (V' O x) (f 3)),dP,(fun w=> (by dsimp only [F₁]; rw [if_neg (by decide : ¬false=true), if_pos rfl]; exact pF₁ w)),fun y=> ⟨f y,Selection.brought Y H V Q Qc O false (C 3) Ψ hΨ y (C y),β y,fun z=>?_,fun z=>?_⟩⟩
 · let read:= phaseRead Y H V Q Qc y (C y) ((L y).character x)
   have e1:read s (F' z)= i' z x:= (phase_read Y H V Q Qc y (C y) s _ ((H' z).enter Y H false)).trans (congrFun (congrFun (β y) s) _)
   have h2: ‖1+ read s (F' z)‖ < 1/2:= e1 ▸ lx (.inl z)
   apply witnesses Y H V Q Qc y (C y) (by norm_num) (H' z) (t0 z); have h:= norm_sub_norm_le (1:ℂ) (-(read s (F' z))); rw [norm_one,norm_neg,sub_neg_eq_add] at h; change 1/2< ‖read s (F' z)‖; linarith only [h2,h] -- maybe too cost unfolding
 have he₀:=phase_read Y H V Q Qc y (C y) s ((Y₀ y) (T x)) (ϱ (F₁ z.1 z.2)); exact ⟨cS z, sip (norm_nonneg _) (he z).1 hp, (show (ξ y) ((Y₀ y) (T x)) s (r (F₁ z.1 z.2))= k' z x from he₀.trans (congrFun (congrFun (β y) s) _)) ▸ lx (.inr z)⟩

-- supply Christmas platform. choose χ once, keep CP5 Luminous on both displays. lift Market = TRUE. Dawn/late Duet. partner retacts. in V0.F X'=late higher.
-- omit V Q Qc C hp P eX Ψ hΨ V₀
structure Display (s n n' : ℕ)(F:∀ W:Window.Family,Bool→Sermon A (tent Y H) W)(q d w:ℕ)(W₁: SU.Slot → Family (tent Y H))(x:Ψ.X): Prop where
 card (i:Bool):Fern.Luminous Y H V Q Qc C Ψ eX V₀.first_ s n n' (fun W=> F W i) q d w W₁ x
 porch (W:Window.Family): Mezz.Duet (tent Y H) A (stint Λ.block A.marks) (F W false) (F W true)
 esteem (v:Axis)(z:Window.Family × Bool): ‖E s (r (F z.1 z.2))‖<1/2 ∧ ‖(ξ v) ((Y₀ v) (T x)) s (r (F z.1 z.2))‖ <1/2  -- `¬E.conv` vs `.Fulfill_`: keep BOTH price small for telescope, not ded from Lip.price(F').
#print Display.mk
open Season
omit Ψ hΨ
include C eX hp V₀ P V Q Qc
lemma appointments (u:ℕ) : ∃ (Ψ':Horizon Y H V Q Qc 3 false (C 3))(x:Ψ'.X) (s n n':ℕ)(F:∀ W:Window.Family,Bool→Sermon A K W)(Z:SU.Slot→Family K),u≤ s∧ Display Y H V Q Qc C Ψ' eX V₀ s n n' F q d w Z x:=by
 obtain ⟨Ψ',t⟩:= vision Y H V Q Qc 3 (C 3) eX
 let g(s:Axis)(x: Ψ'.X):= (Y₀ s) (Ψ'.character x); let V' (s:Axis) (i: Ψ'.X) := Classical.choice (realizeRoom Y H V Q Qc s false (C s) (g s i))
 obtain ⟨F',Z,s,n,n',x,h,a,v,du,y⟩:= surveyH Y H V Q Qc C Ψ' t eX V₀ P hp u V'; refine ⟨Ψ',x,s,n,n',Z,F',h,fun i=> ?_,du,fun i z=> ((y i).2.2.2.2 z).2⟩
 refine ⟨t,a,v,fun W=> (((y 3).2.2.2.2 (W,i)).1),fun W=> ?_,fun i=> ?_⟩
 · exact Guild.alongCost Y H V Q Qc C s (Ψ'.character x) (V₀.first_.stationed Y H) (Z W i) (V₀.first_.slope.ge) v (((y 3).2.2.2.2 (W,i)).2.1) (fun v=> ((y v).2.2.2.2 (W,i)).2.2)
 exact ⟨_, seated Y H V Q Qc i C eX (g i x) (V' i x) (y i).1,axisBill Y H V Q Qc 3 C eX _ (Ψ'.character x),(y i).2.2.2.1⟩
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern
#print axioms surveyH
#print axioms appointments
#print axioms Display.card
