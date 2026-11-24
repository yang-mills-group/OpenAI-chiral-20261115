import YM.SU5.WakeInvestment.CurrentClan
import YM.SU5.WakeInvestment.Escalator

/-! Extensive estimates along an actual joint s-path, finite period even if the
free stencil s chosen first (and error on large p estimate only after degree and
sleeve horizon). Uses the flat spin comparison along that path from
Twah.aroma (not needing to identify the exact M->∞ comparator as this lattice
step). Unscaled gauge-mesh positions have their h_s factor; the (R:ℕ)
here is in *matter-cover* units. -/
set_option maxHeartbeats 400000
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
open Window Buffered.Afterglow.Tower Ballad SitSpin
open Signal.Interval (separationCost)
variable {H:Real.exp 1≤ P.x} {χ d d':ℝ}
variable {I:Type*} [Fintype I] (u:I→Lead.Clan) (G:List I)(x:I→ Cover)(w:I→Twah.DirSpin)(R:ℕ)

variable {E A v:ℝ} {φ μ π κ:ℕ→ℕ} {E' : ℕ→ Buffered.Family (tent Y H) →ℂ}{X:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
variable {D₀:ℕ→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
variable (V:Universal Y H φ μ X E') (Q:Coherent (i:=φ) (k:=μ) (E:=E') Y H D₀ π κ)
local notation "iA" => φ ∘ π
local notation "kA" => μ ∘ κ

abbrev wakeOf (u:I→Lead.Clan)(a:I→ Cover)(b:I→Twah.DirSpin)(R:ℕ)(G:List I) := Twah.witness u G (Twah.nearPoints R (SitSpin.rest a b)) b
local notation "y_" => SitSpin.reader u x w R G
lemma lift_book (H:Real.exp 1≤P.x) (F:Papal.Weaver) : expSrc Y s i H (Papal.household (tent Y H) F)= F (side Y i s):= castF _ _ _
where castF (m n:Side)(h:m=n): (h ▸ F m)=F n:=by subst n; rfl
lemma breadth_cap (Z: Finset Cover) (o:Cover) :∀ᶠ n:Side in atTop,∀ j,cows j (Lattice.halo 0 (dBook n Z)) (2*Celeste.breadth o Z):=by
 filter_upwards [breadthMoney o Z] with n p j; obtain ⟨z,v⟩:=blocks_rest (wrap (More n) o) (Celeste.breadth o Z) j; exact ⟨z,fun i h=> v _ (Lamour.Bridge.fit (r:= _) (w:=0) p h)⟩
set_option linter.unusedSectionVars false in
lemma price_card (x:I→ Cover)(G:List I): (dBook n (lay x G)).card ≤ G.length:=by refine le_trans (card_image_le) ?_; unfold lay; apply le_trans (List.toFinset_card_le _) ?_; simp

lemma clarity_upper (F: Papal.Weaver) (z:ℂ)(R:Clarity (Papal.meanF F z) P.K.j χ) :
    ∀ᶠ i:ℕ in atTop,∀ k:ℕ, ‖noble Y s i k (F (side Y i s) (1,1))-z‖ ≤ χ:= by
 filter_upwards [(Papal.count_la Y s).eventually R] with i ht k; let q:= ht (Vale.val_e ..) ((RootBook Y i k s).J.M) _ (preparedFlat Y s i k); rw [noble_linear]; let Z:=Lamour.alleyR (mateK (side Y i s)) (flatSea Y s i k)
 change ‖Z (_-z • 1)‖ ≤ _ at q; rw [map_sub,map_smul,smul_eq_mul,show Z 1=1 from (noble_linear ..|>.symm).trans (noble_unit Y s i k),mul_one] at q; exact q

variable {s}
include V Q
-- The comparison hypothesis is not E: it is a `Clarity` on finite flat Wake.
lemma aroma_le
   (D':∀ᶠ l in atTop, ViewTickets (E:=E) Y s (iA l) (kA l) H (2*G.length) A)
   (h:(G.length:ℝ)≤ sPow P s A) (v: ∃ o: Cover, 2 * (Celeste.breadth o (lay x G):ℝ) ≤ sPow P s A) (p: (SitSpin.factor R)^G.length ≤ sPow P s A) {t:ℂ}
   (e: Clarity (Papal.meanF y_ t) P.K.j χ) : ‖E' s (Papal.household (tent Y H) y_) - t‖≤ chip (shx s) (-3)+χ := by
 obtain ⟨o,q⟩:=v; let f:= Papal.household (tent Y H) y_; let g:= lay x G; let b:=Celeste.breadth o g; have h':= V.pick.grow_i.comp Q.growsA
 let W(k):= (Papal.count Y s k); let a:=SitSpin.reader_voice u x w R G
 apply le_of_tendsto (((sharp_on_track Y V Q s (F:=f) (aux_test ((a.1.narrow _).widen))).sub (tendsto_const_nhds (x:=t))).norm)
 filter_upwards [D',h'.tendsto_atTop.eventually (clarity_upper Y s _ _ e), ((Papal.count_la Y s).comp h'.tendsto_atTop).eventually (breadth_cap g o)] with l k ht hu
 let i:=iA l; let s':=kA l; let N':=side Y i s; let X0:= y_ N'; let X :Hookah N':=⟨X0,dBook N' g,wrap (More N') o⟩
 have hw:= k.grant X (2*b) G.length _ (by exact_mod_cast q) h p (show SpinLeaf X (2*G.length) _ _ from ⟨a.1.bounded N',price_card x G,a.2 N',fun x'=> reader_link u x w R G N' x' _, reader_price u x w R G N' _⟩) hu
 change ‖Journey.compass Y i s' s (expSrc Y s i H f) - t‖≤ _; unfold f; rw [lift_book]; exact (norm_sub_le_norm_sub_add_norm_sub (Journey.compass Y i s' s X.x) _ t).trans (add_le_add hw (ht s'))
lemma spin_wake (Z:Investment P E v)(L_:Dispatchers P)(K:Meritorious P) (J:0<A) (f:0<χ) (q:0<d) :
   ∃ n:ℕ, ∀ᶠ s:ℕ in atTop, ∀ R:ℕ,n≤ R→ ∀ (x:I→ Cover), (G.length:ℝ)≤ sPow P s A →
      (∃ o: Cover, 2 * (Celeste.breadth o (lay x G):ℝ) ≤ sPow P s A) → -- prefer Eventually strength atTop R independent of s: separate
      (SitSpin.factor R)^G.length ≤ sPow P s A → Twah.Spill (SitSpin.rest x w) d' d R →
      ‖E' s (Papal.household (tent Y H) (SitSpin.reader u x w R G)) - wakeOf u x w R G‖≤ χ := by
 obtain ⟨n,p⟩:= eventually_atTop.mp (Twah.aroma P.K.j u G w (nontrivial_spin P) (χ/2) q d' (by positivity))
 refine ⟨n,?_⟩; filter_upwards [alongView Y V Q Z L_ K (2*G.length) J,(turnover P).eventually (chip_spend (-3) 0 1 (χ/2) (by norm_num) (by positivity))] with s z h R g x hL t a u'
 have hp: chip (shx s) (-3) ≤ χ/2:= by simpa only [WakeInvestment.chip,zero_div,BProof.coin_zero,one_mul,mul_one] using h.le
 apply (aroma_le Y u G x w R V Q z hL t a (p R g _ u' rfl)).trans; linarith only [hp]
#print axioms spin_wake
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
