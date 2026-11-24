import SatinThinInhale
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
-- requirements above read-account (uniform across δ-tested enquiries).
structure Dispatchers (P:Preparation) : Prop where
 offers: ∃ R a δ:ℝ,0 ≤ R ∧ 0<a∧ P.d≤δ ∧ ∃ n:ℕ,∀ N:Side,n ≤ N.val→ Colts P.K.j N a R δ
lemma dispatch_commission {RΘ:Preparation→Prop}(T_: CommissionVector RΘ): CommissionVector (fun P=> RΘ P ∧ Dispatchers P):= by
 constructor; intro e' ε he Q
 obtain ⟨R,a,δ,v,hv,u,N0,p⟩:= colts_thrive 4 (by omega)
 obtain ⟨P,ℓ,Z,Y,p',u',t',r,c,A,w,X',L',G',B',J⟩:= T_.purchased (min e' δ) ε (lt_min he u) Q
 refine ⟨P,ℓ,Z,Y,p',u',t'.trans (min_le_left ..),r,c,A,⟨w,?_⟩,X',L',G',B',J⟩
 exact ⟨R,a,δ,v.le,hv,t'.trans (min_le_right ..),N0,fun n v=> by rw [P.kJ]; exact p n v⟩ -- struct has field binder `⟨⟨...⟩⟩`?

local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s
open Damask Pannier.Damask
abbrev atFrame (s i:ℕ)(U:Orbit (side Y i s)) := Rous.metroFrame (terrace (shx s)) ((ℂk s i) U) -- tune
lemma map_meters (H:Dispatchers P) (c:ℝ)(w:0 ≤ c) : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s≤ Y.uv k→∀ U:Orbit (side Y i s),
    c*metroStress D (Gξ s i k) (ℂk s i) U (atFrame Y s i U) ≤ meterC (shx s) * sites (side Y i s) + gateC (shx s) * flakes (vℓ s) U.1:=by
 obtain ⟨R,g,δ,z,z',h',n,p⟩:= H.offers; let C:= cashU P.W.C; let a:=levelQ P.W.C; let q:=P.J.n; have hp:Tendsto (hat L P.x) atTop atTop:= turnover P; have ht:= P.J.ht
 have hx: Tendsto shieldC atTop (𝓝 0):= BProof.coin_purchases (Or.inl (by norm_num [r_shield]: r_shield<0))
 filter_upwards [hp.eventually (clamp_bill C R a g δ c (level_p _) z' q),hp.eventually (hx.eventually (ge_mem_nhds ht))] with s h hT
 let u:=shx s; let m:=radiusB u; let r:= terrace u
 filter_upwards [(Papal.count_grows Y s).eventually_ge_atTop (n+r.val+m)] with i hN k v U
 let V:= ℂk s i; let F:=Gξ s i k; let y:=vℓ s; let N:=side Y i s; let K:=sites N; let ρ:=flakes y U.1; have hsc:= Papal.roofage Y i s; have hv:0 ≤ y:= (BProof.coin_pos ..).le; change n+r.val+m≤ N.val at hN
 have hu:=P.U.broadness N (P.J.gran.trans ((Y.voyage i).ownership s).size) F.J.M; let hf:=p N (by omega); have ha:N.val≤(More N).val:=Nat.le_mul_of_pos_right N.val two_pos
 have hh:=mile_attenuation hf z h' F (Papal.prices_plot Y s i k v).2.2.2.2 (cash_v P.W.C) U hsc (hu.projection _ (hsc.paid _)) (show y≤ _ from hT) (level_p P.W.C).le hv (show m≤ (More N).val by omega) (atmosphere a u) le_rfl
 have hh':=frame_attenuation hf z (P.dpos.trans_le h') r F.J.M hv hsc (show y≤ _ from hT) U m h' hu (by omega)
 let X':=baseDaily a C R (atmosphere a u); let Y':= debtDaily q m C R; let W:=townDaily r y R g δ m; let T:=townDues r R 1 q
 have hA:townDues r R (townS U y) q=T*ρ:=by unfold T ρ townDues frame_h townS; ring
 have hX: c*(X'+W) ≤ meterC u ∧ c*(Y'+T) ≤ gateC u:=h
 let H':= metroStress P.K.j F V U (atFrame Y s i U)
 apply (mul_le_mul_of_nonneg_left (show H'≤ X'*K+Y'*ρ +(W*K+T*ρ) from ?_) w).trans; swap
 · rw [←hA]; exact add_le_add hh hh'
 have hv:0 ≤ K:=zero_le_one.trans (sites_pos _); have hρ:0 ≤ ρ:= Nat.cast_nonneg _; change _ ≤ meterC u*K+gateC u*ρ; nlinarith only [mul_le_mul_of_nonneg_right hX.1 hv, mul_le_mul_of_nonneg_right hX.2 hρ]
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.map_meters
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.dispatch_commission
