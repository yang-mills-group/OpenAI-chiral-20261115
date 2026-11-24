import YM.SU5.WakeInvestment.Pure
import YM.SU5.FiniteGaugeData.Tower.TowerLaw

/-!
Uniform indexing in the physical P-law. Explicit extent license. Coin currency
astute to $p_X^I$ (coin at (0,I,0)). All degree & power expenses after height.
Not paying support Registration under the fibre Mark price: requires proof on those
actual layout suits at exhibition. The argument here doesn't need Ferry for the added
motions at different heights. Always use course's `hat` and `uv`, `ir`. `P.E`
on coherent *joint* path including these Mark roots, can transfer any purchased
limit or finite-torus comparator using the uniform maturity. 
-/
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 24000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

open Lamour.Bridge Celeste Clock Hookah
open Cliplet
open BProof (coin scaleY)
abbrev sPow (P:Preparation)(s:ℕ)(e:ℝ):=coin (hat P.R.L P.x s) 0 e 0
lemma grow_e (A B:ℝ)(k:0<A)(P:Preparation) : ∀ᶠ s:ℕ in atTop, B ≤ sPow P s A:=by
  filter_upwards [(turnover P).eventually (BProof.coin_budget (b:=0) (e:=A) (c:=0) (a:=0) (d:=0) (f:=0) (Or.inr (Or.inl ⟨rfl,k⟩)) B 1 zero_lt_one)] with s g; exact le_of_lt (by simpa only [one_mul,BProof.coin_zero,mul_one] using g)
lemma pose_roomy {H:Real.exp 1≤ P.x}(A:ℝ)(k:0<A) : ∀ᶠ s:ℕ in atTop,∀ B:ℕ,(B:ℝ)≤ sPow P s A→ leafRoom s B Y H:=by
 let U:= addgap (tent Y H); let f:= fun x=> coin x 0 A 0
 have h0: Worth.Pays 0 A 0 (fun x=> 4*(f x+(U:ℝ))):=Pays.scale 4 (Pays.plus (whole ..) (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,k⟩))))
 filter_upwards [(turnover P).eventually (Pays.leap (p:=0) (q:=0) (w:= -(205:ℝ)/400000) (Pays.times (Pays.scale 12 (Pays.whole Worth.r_meter 0 0)) (Pays.pot h0 4)) (Or.inl (by norm_num [Worth.r_meter])))] with s g B e
 let x:= shx s; unfold leafRoom; apply le_trans _ g; change _ ≤ 12*Worth.meterC x*(4*(f x+U))^4; have h:0≤Worth.meterC x:= (BProof.coin_pos ..).le
 gcongr
lemma pose_rent (E A:ℝ)(M:ℕ)(t:1≤flatTicket E)(p:0<A) (P:Preparation) : ∀ᶠ s:ℕ in atTop,∀ (r:ℕ), (r:ℝ)≤ sPow P s A→ ∀ C:ℝ,0≤C→ C≤ sPow P s A →
    optPrice (P:=P) E s M r C * sizeRent M r ≤ chip (hat P.R.L P.x s) (-199) ∧ optPrice (P:=P) E s M r C ≤1:= by -- shx depends P need explicit earlier? macro hygienic
 let g:ℝ:=Fintype.card (SpinIdx × SU.Slot);-- SpinIdx not Tulip?
 let W:=flatTicket E^M; let S(x:ℝ):=coin x 0 A 0; let R(x:ℝ):=(S x*g+1)^M; let F(x:ℝ):=chip x (-200)*(S x+(S x* R x)* W); let a:=A*(M:ℝ)
 have hs:Worth.Pays 0 A 0 S:= whole 0 A 0
 have hr:Worth.Pays 0 a 0 R:= by
    let f:Pays 0 A 0 (fun x=> S x*g+1):=Pays.plus (Pays.right g hs) (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,p⟩)))
    simpa only [zero_mul] using (Pays.pot f M)
 have he: Worth.Pays 0 (A+a+1) 0 S:= Worth.Pays.merit hs (Or.inr (Or.inl ⟨rfl,by have h0:0 ≤ a:=mul_nonneg p.le (Nat.cast_nonneg _); linarith⟩))
 have hx': Worth.Pays (-(200:ℝ)/400000) (A+a+1) 0 F:= by
    have hp: Worth.Pays 0 (A+a+1) 0 (fun x=> S x*R x*W):= by
      apply Worth.Pays.merit (Pays.right W (Pays.times hs hr)); apply Or.inr; left; exact ⟨by norm_num,by linarith⟩
    simpa only [zero_add,add_zero] using Pays.times (Pays.whole (-(200:ℝ)/400000) 0 0) (Pays.plus he hp)
 filter_upwards [(turnover P).eventually (Pays.leap (w:= -(199:ℝ)/400000) (p:=0) (q:=0) (Pays.times hx' hr) (Or.inl (by norm_num))), (turnover P).eventually (Pays.leap (w:=0) (p:=0) (q:=0) hx' (Or.inl (by norm_num)))] with s tz f r hr C c b
 let x:= hat P.R.L P.x s; have hs:= (chip_pos x (-200)); have hr:sizeRent M r ≤ R x:=by unfold R sizeRent modeCap; push_cast; unfold g; gcongr
 have hW:0 ≤ flatTicket E^M:=pow_nonneg (zero_le_one.trans t) _; have hS:0≤S x:=(BProof.coin_pos ..).le; have hz:0≤R x:=by unfold R g; positivity
 have hQ: optPrice (P:=P) E s M r C ≤ F x:=by unfold optPrice F; apply mul_le_mul_of_nonneg_left (add_le_add b _) hs.le; gcongr
 have ha:0≤ sizeRent M r:=by unfold sizeRent; positivity
 refine ⟨(mul_le_mul hQ hr ha ?_).trans tz, hQ.trans ((BProof.coin_zero _).le.trans' f) ⟩; unfold F; unfold W at *; positivity

-- Chancellor. Move on any eligible Coherent; applications use projection on same enrollment.
open Buffered.Afterglow.Tower
variable {E A v:ℝ} {φ μ π κ:ℕ→ℕ}
-- can always apply even on further thinnings
lemma bone_pose (u:1≤ P.K.j) (s:ℕ): ∀ᶠ i in atTop, evenPose Y s i:=by
 filter_upwards [(Papal.count_la Y s).eventually (ownsHalo u)] with i hp; exact hp (Vale.val_e ..)
structure ViewTickets (H:Real.exp 1≤ P.x) (M:ℕ)(A:ℝ) : Prop where
 poses (B:ℕ)(t:(B:ℝ)≤ sPow P s A): Defog (H:=H) Y s i k E M B 1
 grant (F:Hookah (side Y i s))(B r:ℕ)(C:ℝ)(pE :(B:ℝ) ≤ sPow P s A)(pR:(r:ℝ)≤ sPow P s A)(pC:C≤ sPow P s A) (f: SpinLeaf F M C r) (u:∀ j,cows j (Lattice.halo 0 F.S) B) : ‖Journey.compass Y i k s F.x-noble Y s i k (F.x (1,1))‖ ≤ chip (shx s) (-3)

-- along physical path with its law. Uniformity of tickets at s, across all such B.
variable {H:Real.exp 1≤ P.x} {E' : ℕ→ Buffered.Family (tent Y H) →ℂ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
variable {D₀:ℕ→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
variable (V:Universal Y H φ μ I E') (Q:Coherent (i:=φ) (k:=μ) (E:=E') Y H D₀ π κ)
local notation "iA" => φ ∘ π
local notation "kA" => μ ∘ κ
include V Q
lemma alongView (W:Investment P E v)(J':Dispatchers P)(w:Meritorious P)(M:ℕ)(p:0<A) :
   ∀ᶠ s:ℕ in atTop, ∀ᶠ r:ℕ in atTop, ViewTickets (E:=E) Y s (iA r) (kA r) H M A:=by
 let a:= V.pick.grow_i.comp Q.growsA; let k:= V.pick.grow_k.comp Q.growsB
 filter_upwards [call_hold (H:=H) Y W J' w M, pose_roomy (H:=H) Y A p, pose_rent E A M (flatT_pos W) p P] with s q t u
 let U:= Finset.range (Nat.ceil (sPow P s A)+1); have hu(B:ℕ)(v: (B:ℝ) ≤ sPow P s A): B∈U:=Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.cast_le.mp (v.trans (Nat.le_ceil _))))
 have f:∀ B∈ U,∀ᶠ r:ℕ in atTop,(B:ℝ)≤ sPow P s A → Defog (H:=H) Y s (iA r) (kA r) E M B 1:=by
    intro B _; by_cases b:(B:ℝ)≤ sPow P s A
    · obtain ⟨n,l,h⟩:= q 1 B zero_le_one (t _ b) -- b need t _ b
      filter_upwards [a.tendsto_atTop.eventually_ge_atTop n,k.tendsto_atTop.eventually_ge_atTop l,Q.finance s] with i q p h' _; exact h _ _ q p h'
    exact Filter.Eventually.of_forall fun _ q=> (b q).elim
 filter_upwards [a.tendsto_atTop.eventually (bone_pose Y (nontrivial_spin P) s), (eventually_all_finset U).mpr f] with r p h
 let L0(B:ℕ)(t:(B:ℝ)≤ sPow P s A):=h B (hu B t) t; refine ⟨fun B u=> L0 B u,fun A' B r C pB pr pv F f=>?_⟩
 let q:=L0 B pB; obtain ⟨a,h⟩:=u r pr C ((norm_nonneg _).trans F.degree.price) pv; exact q.test (pure_fit Y s _ _ F q p a h f)

-- fixed footprint including Weyl probes: separate family limit passage.
set_option linter.unusedSectionVars false in
lemma sharp_on_track (s:ℕ){F:Buffered.Family (tent Y H)} (h:TestFamily (tent Y H) true F) : Tendsto (fun r=> Journey.sharp Y H s (iA r) (kA r) F) atTop (𝓝 (E' s F)):=by
 obtain ⟨S,t⟩:=h.paid; obtain ⟨u,p⟩:= valuation Y H t; have hz:0 ≤ u:=pay_nonneg (F:=F) p; obtain ⟨C,z,q⟩:= Q.implements s S
 apply Metric.tendsto_nhds.mpr; intro ε e; let d:=ε/(u+1); have hu:0 < d:=div_pos e (by positivity)
 filter_upwards [q d hu] with i hp
 obtain ⟨_,_,_,_,hx,k⟩:=hp F t u p; rw [dist_eq_norm]; refine lt_of_le_of_lt hx (?_); have hf:d*(u+1)=ε:=div_mul_cancel₀ _ (by positivity); linarith
abbrev expSrc (H:Real.exp 1≤P.x) (f:Buffered.Family (tent Y H)) := Journey.send Y H i s (f (momentm Y i s))
theorem grantLimit (s:ℕ)(A E:ℝ)(M:ℕ){F:Buffered.Family (tent Y H)} {y:ℂ} (z:Tendsto (fun i=> noble Y s (iA i) (kA i) (expSrc Y s (iA i) H F (1,1))) atTop (𝓝 y))
    (x:∀ᶠ r:ℕ in atTop, ViewTickets (E:=E) Y s (iA r) (kA r) H M A)
    {B r:ℕ}{C:ℝ}(pE:(B:ℝ) ≤ sPow P s A)(pR:(r:ℝ)≤ sPow P s A)(pC:C≤ sPow P s A)
    (p: TestFamily (tent Y H) true F)(u:∀ᶠ l in atTop,∃ S: Hookah (side Y (iA l) s), S.x=expSrc Y s (iA l) H F ∧ SpinLeaf S M C r ∧ ∀ j,cows j (Lattice.halo 0 S.S) B) :
    ‖E' s F-y‖ ≤ chip (shx s) (-3):=by
 apply le_of_tendsto (((sharp_on_track Y V Q s p).sub z).norm); filter_upwards [u,x] with i hp g; obtain ⟨S,t,f,h⟩:=hp; let T:=expSrc Y s (iA i) H F; change ‖Journey.compass _ _ _ _ T-noble Y _ _ _ (T (1,1))‖≤ _; rw [←(show S.x=T from t)]; exact g.grant S B r C pE pR pC f h
#print axioms grantLimit
#print axioms alongView
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
