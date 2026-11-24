import YM.CF.Paxos.Luz
import YM.CF.Bloom.Kale
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
structure Heron (P:ℝ)(R0 E C D:ℝ→ℝ)(z:ℝ):Prop where
 step (x:ℝ)(u:z≤x){N P':Side}(S:StepData (Domain N B) (Domain P' B))(G:Ratio (mid N B) (mid P' B)) :∃ Δt:ℝ,0<Δt∧∀ (T: Tube SU.group S)(A0:Scree.Loom (mid N B))(B_:Scree.Loom (mid P' B))(X:GramM (mid N B))(Y: GramM (mid P' B))(pA:Roof _ J.k J.roomX J.n A0)(pB: Roof _ J.k J.roomX J.n B_) (wB:∀ F' U' V', JointB G (seine G F' q J.d U' (A0 V'), A0 V') J.roomX)(H: Girt.BaseL U G Y A0 B_ q J.d) {Z' γ:ℝ} (b:StatV V G T U W X Y Z' γ a x p i) (g:N0*radiusB x ≤ (Domain N B).val)(c:60< (Domain N B).val),∀ (I:Type)[TopologicalSpace I][FirstCountableTopology I][Nonempty I](bu:I→ℝ)(F0 F1:I→ RegBudget (mid P' B))(F2:I→ForceBudget (mid P' B))(Jk:I→ℂ)(ij:I→ Haro.ΘS (R0 x)), let X'(c):=Oise.color_b X (bu c+(Z'+γ)) 0 0 0 0; let Vu(c):=Oise.color_b Y (bu c) (F0 c) (F1 c) (F2 c) (Jk c); Continuous bu→ Oise.Tone_u F0 Y.p → Oise.Tone_u F1 Y.p → Oise.Tone_v F2 Y.p→ Continuous ij → (∀ c,Girt.BaseL U G (Vu c) A0 B_ q J.d) → (∀ c,StatV V G T U W (X' c) (Vu c) Z' γ a x p i) → (∀ c,Arc_r (Vu c) h (dleaf R.L x) (dleaf R.L x) (dleaf R.L x)) →(∀ c,∃ Ω,Tact G S (Vu c) h (dleaf R.L x) Ω)→ (∀ c,BeaconP K.j (Vu c) S)→ (∀ c,Pant_W (N:=P') (Vu c))→ ∃ (W1:I→Haro.ΘS (R0 x))(R1:I→RegBudget (mid N B))(Z1:I→ForceBudget (mid N B))(Q:I→ℂ)(Δ:I→ℝ), Continuous W1 ∧ Continuous Δ ∧ Beau.LampF R1 ∧ (∀ j:Force (mid N B),∀ v,Continuous fun z=> Z1 z j v) ∧ ∀ c,LuxM V (X' c) (Vu c) (R1 c) (Z1 c) U (Q c) A0 B_ G S q J.d h (P/(R.L.val:ℝ)*dleaf R.L x+E x) (C x) (D x) (Δ c) (Haro.riseV (ij c)) R.L.val Δt (ij c=W1 c)
 hex(x:ℝ)(u:z ≤ x):0 < R0 x
 wean(x:ℝ)(u:z≤x):|D x|≤ Vale.billX R.L/4

 hu:z≥1
 pay(x:ℝ)(u:z≤x):P/(R.L.val:ℝ)*dleaf R.L x+E x ≤ dleaf R.L x∧ C x ≤ dleaf R.L x
 me (x:ℝ)(u:z ≤ x):0< dleaf R.L x∧ ∀ y:ℝ,x≤ y→ dleaf R.L y ≤ dleaf R.L x∧ plow x≤plow y
 rise(x:ℝ)(u:z ≤ x): |D x| ≤ rendK k₀ x
 buying : 8*W.z≤ z
lemma form_T(P:ℝ)(w:P/R.L.val ≤ 1/4)(F:Coffer (p:=p) (k:=i) V U W q a J.d J.n P N0 J.k J.roomX h) (K0:ℕ): ∃ R0 E C D:ℝ→ℝ,sizeK R.L 2 R0∧ Litt R 2 E ∧Litt R 2 C∧ Chill_v D∧∃ z:ℝ,Heron V a p i N0 K0 J q h P R0 E C D z:=by
 obtain ⟨s,t⟩:=dev_R R; obtain ⟨R0,E,C,D,u,v,a,b,hQ⟩:= F.wrap _ _ _ _ s s s s t
 obtain ⟨x,hX⟩:=eventually_atTop.mp hQ; obtain ⟨y,h,d⟩:= glimp_T (R:=R); obtain ⟨z,hz⟩:= eventually_atTop.mp ((stand_v R P w E C v a).and (fuel_s D b K0)); have hzQ:0 < Vale.billX R.L:=mul_pos (Gauge.slopeConstant_pos yet_one) (Real.log_pos (by exact_mod_cast (show 1<R.L.val from (by have h:= V.tallX; omega))))
 obtain ⟨s,bh⟩:= eventually_atTop.mp (b.spine_a.abs.eventually (ge_mem_nhds (show |(0:ℝ)|< Vale.billX R.L/4 from by simpa using (div_pos hzQ (by norm_num : (0:ℝ)<4) : (0:ℝ)<_))))
 let Bx:=max (max (max x y) z) (8*W.z); have hx:x≤Bx:= le_trans (le_max_left x y) (le_trans (le_max_left ..) (le_max_left ..)); have hu:y≤Bx:=(le_max_right ..).trans (le_trans (le_max_left ..) (le_max_left ..)); have hp:z ≤Bx:=le_trans (le_max_right ..) (le_max_left ..)
 exact ⟨R0,E,C,D,u,v,a,b,max Bx s,⟨fun x e {N M} S G => (hX x (hx.trans ((le_max_left ..).trans e))).2 S G,fun x v=> (hX x (hx.trans ((le_max_left ..).trans v))).1, fun i w=>bh i ((le_max_right ..).trans w), (h.trans hu).trans (le_max_left ..),fun i p=>(hz i (hp.trans ((le_max_left ..).trans p))).1,fun i p=> let t:=d i (hu.trans ((le_max_left ..).trans p)); ⟨t.1,t.2.2⟩,fun i p=> (hz i (hp.trans ((le_max_left ..).trans p))).2,(le_max_right ..).trans (le_max_left ..)⟩⟩ -- tune shadow x and Imp
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Heron V a p i N0 k₀ J q h wα R0 E C δ y)
variable (hy:y≤x)
-- common tips transfer across ℓ
private theorem stepΘ(j k:ℕ): V.L.op k (kint M B R.L j)= V.L.op 0 (kint M B R.L j):=by
 have hp(i:ℕ): V.L.op i (kint M B R.L j)=⟨R,K.bind,kint M B R.L j⟩:=by
    cases h: V.L.op i (kint M B R.L j) with|mk Y Z t=> have ht:Y=R:=Eq.trans (congrArg StepData.patch h.symm) (V.L.lent i); have hv: Z=K.bind:=Eq.trans (congrArg StepData.kernel h.symm) rfl; congr
 exact (hp _).trans (hp 0).symm
def Zps (j l:ℕ):= Classical.choose (D'.step (hat R.L x j) (hy.trans (crown ..)) (V.L.op l (kint M B R.L j)) (apt M B R.L j))
abbrev Hertz(j):= Zps V a p i N0 M k₀ J q h R0 E C δ y D' hy j 0
lemma warm_hrt(j:ℕ): 0 < Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy j:= (Classical.choose_spec (D'.step (hat R.L x j) (hy.trans (crown ..)) (V.L.op 0 (kint M B R.L j)) (apt M B R.L j))).1
lemma swap_hrt(j l:ℕ): Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy j= Zps V a p i N0 M k₀ J q h R0 E C δ y D' hy j l:=by let f(S:StepData (Domain (mesh M R.L j) B) (Domain (mesh M R.L (j+1)) B)):=Classical.choose (D'.step (hat R.L x j) (hy.trans (crown ..)) S (apt M B R.L j)); exact congrArg f (stepΘ V _ j l|>.symm)
include D D'
lemma bond_C (hy:y ≤ x)(Y:ℕ)(hp:Y≤ l0)(q:ℝ) (h: |q-B0 Y| ≤ (Y:ℝ) *(Vale.billX R.L/4)):matchedX (hat R.L x Y) q:=by
 let t:=hat R.L x Y
 have hx:0<x:=zero_lt_one.trans_le (D'.hu.trans hy); have ht0:x≤t:=crown ..
 obtain ⟨u,v⟩:= narrow_β V a p i N0 T M ht l0 B0 D Y hx (D'.buying.trans hy) hp
 rw [abs_le] at h; obtain ⟨g,v'⟩:=h; have ht:B0 Y≤3/2*(hat R.L x Y):=v; unfold matchedX; unfold hat at *; constructor<;> linarith
end YM.CF.Py
