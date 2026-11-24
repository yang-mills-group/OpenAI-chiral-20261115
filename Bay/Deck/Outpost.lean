/- Compatibility lift, near-exact baseline YM/SU5/Thin/Cascade/Outpost.lean with narrower imports omitting Vellum. No proof changes. -/
import Bay.Deck.Tinsel
set_option autoImplicit false
set_option maxHeartbeats 320000
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open clocks
variable {L':Side}
namespace Papal
open CF.Rapids CF.Pannier.Damask CF.Pannier.Damask.VelvetC CF.Pannier.Chancel
open Graph Pannier
local notation "Ψ"=> P.R.L

open clocks Sleigh Paddled
variable (s i k:ℕ)
local notation "M"=> count Y s i
local notation "θA"=>levelQ P.W.C
local notation "θB"=>cashU P.W.C
local notation "X"=>hat Ψ P.x
local notation "Z"=>uniformDebit
local notation "μ" x:max=> radiusB x

variable {ε a C D:ℝ}{v b:ℕ}(W:Convent P ε a C D v b)
-- weight kept for further flags for obvious interactions? half of both budgets
abbrev rink (U:Pane (count Y s i)):ℝ:= let x:=hat Ψ P.x s; let R:=gram Y s i k; stipd (clocks.grain x) (ledge x) (meek R.p U) (outerMark x) U
include W
lemma cappuccini : ∀ᶠ s:ℕ in atTop,∀ i, Fashion Y ε a C D v b s i:=by
 filter_upwards [winters_port P, ((tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/200)).comp (stage_slope P.V P.x)).eventually_ge_atTop ( ((2*(v+b):ℕ):ℝ))] with s h e i
 let d:= count Y s i; obtain ⟨m,r,w⟩:= h (Y.ir i); let Xo:=averge (hat Ψ P.x s); have hp:(2*(v+b):ℕ) ≤ r.count.val:= Nat.cast_le.mp (le_trans (α:=ℝ) e w.span.1)
 have hv:r.count.val<d.val*2:= lt_of_le_of_lt (by omega) w.ample; have hs:d.val=(Vale.mesh (Y.ir i) Ψ s).val*2*P.block.val:=rfl; refine ⟨W,⟨?_,?_⟩,?_⟩; change v≤d.val; omega; change b≤d.val; omega; change Even d.val; rw [hs]; exact Even.mul_right (Even.mul_left even_two _) _
-- pointwise normalized amplitude billed even in all projected-flag states.
def HillSeal (Y:Course P (VolumeCape.Dream.Nimbus l))(s i k:ℕ)(R:GramM (count Y s i))(E:ℝ):Prop:= let A:= gram Y s i k; R.beta=A.beta ∧ R.p=A.p∧ R.funds=A.funds ∧ R.path=A.path ∧ R.J=A.J ∧ Graph.Ledger P.h E E (levelQ P.W.C) (cashU P.W.C) R
abbrev sealMark (R:GramM (count Y s i))(U:Orbit (count Y s i)):ℂ:= Complex.exp (-R.v)* Scree.beamZ (count Y s i) (denZ R P.U (room Y s i) U)
lemma seal_budget : ∀ᶠ s:ℕ in atTop,∀ i k, s≤Y.uv k→∀ (R:GramM (count Y s i))(E:ℝ), HillSeal Y s i k R E →∀ U:Orbit (count Y s i),
    Real.exp (rink Y s i k U.1 / 2) * ‖sealMark Y s i R U‖ ≤ winterBill Y s i k U.1 * Real.exp (angleFin (gram Y s i k).J.M (count Y s i) P.K.j + (3*E+oar (X s))*sites (count Y s i)):=by
 let F:= (1+D)^2+1
 let h:F/2≥0:=div_nonneg (by unfold F; positivity) (by norm_num)
 let u:= W.health; have he:0<P.J.k:= P.J.ht
 let g:= stage_slope P.V P.x
 filter_upwards [ cappuccini Y W, charge_fit Y _ _ u.credit.le W.size, g.eventually (coreShot u.rate ε C (F/2) u.credit.le h Ψ P.J.n),winters_port P, g.eventually (neckElection), g.eventually (((park (-(45/100:ℝ))).lim (by norm_num)).eventually (ge_mem_nhds he)), g.eventually (suitBlast Ψ), g.eventually_gt_atTop 0] with s w H l' x p h' q₀ z i k q R E R₀ U
 let n:= count Y s i; let x₀:=hat Ψ P.x s; let ℓ:= clocks.height x₀; let G:=gram Y s i k; obtain ⟨B,C',Y',Y₀,W',Ms⟩:= (show R.beta=G.beta∧R.p=G.p∧R.funds=G.funds ∧ R.path=G.path ∧ R.J=G.J ∧ Graph.Ledger P.h E E (levelQ P.W.C) (cashU P.W.C) R from R₀)
 obtain ⟨m,r,o⟩:= x (Y.ir i); obtain ⟨T⟩:=Tree.select r o.odd; let t:=outerMark x₀; have ht: 0<t:= (shinyH x₀ z).2.1; let U':=U.1; let e:=frilly T U; let Y₁:= Lattice.gauge e ((room Y s i) U); let K:= spar P.K.j R.J.M Y₁; let V:= crimp ε a C x₀ P.J.n r U'; specialize w i; obtain ⟨hh,hr⟩:= l' r o.span o.odd
 have hL: ℓ ≤ (More n).val:=by have he:ℓ+P.J.n+1≤ r.count.val/2:=hh; have Ht:2*(r.count.val+1)<(More n).val:=o.ample; omega
 have hx:= poetry T u (roofage Y i s) o.odd W.applicable w.within.1 ht.le P.dpos.le hh h' o.ample U (q₀ r.count.val r.count.property o.span) R.J.M
 let x₁:= temp x₀/2; have hz:0<x₁:= half_pos (Work.E09.temp_pos z); let F':= fit_fare Y U x₁ (uniformDebit θA x₀) C D ℓ
 let y:= issuesPa Y w U R E E Ms hz.le ((half_le_self (Work.E09.temp_pos z).le).trans (le_trans p h')) (Z θA x₀) le_rfl hL e (show DriveL1 (K-spar P.K.j R.J.M (1:Pane n))≤ V from hx)
 let L:=G.path.inChannels G.funds G.p G.beta U'; let b_f:= (F/2)*V; let Ψ':=oar x₀; let Γ:= rink Y s i k U'; let a:=angleFin G.J.M n P.K.j; let S:=sites n
 have ht₀:‖sealMark Y s i R U‖≤ Real.exp (a-L + (3*E*S + F' + b_f)):=by
    unfold b_f a L; -- geometry rewrites in y? G.p may occur in the explicit B1 syntactic placeholder around V: have y membership
    rw [W',Y₀,Y',C',B] at y; unfold F' S; change _ ≤ Real.exp _ at y; exact (le_trans y (Real.exp_monotone (by unfold F; apply le_of_eq; ring))) -- maybe `unfold F` but y F' use
 have hw:=H i U; have hY:=hr U'; obtain ⟨hp,g,h,hb,-⟩:=prices_plot Y s i k q; have hf:winterBill Y s i k U'=Real.exp (- L+ Γ):=by
    unfold winterBill Γ rink L; change G.path=P.V.L.path _ at g; change G.funds=P.K.top.clip at h; rw [g,h]
 let t₃:=flakes x₁ U'; let t₄:ℝ:=(misdemean t U').card; have hΓ: Γ= clocks.grain x₀*t₃+ ledge x₀*t₄:=by
    have hG:G.p.threshold=temp x₀:= (congrArg BudgetPoint.threshold hp).trans (Y.meter.boot s).1; change stipd _ _ (meek G.p U') t U' = _; unfold stipd meek; rw [hG]; -- `roughness` vs `misdemean`, Decidable equality issue
    rfl
 rw [hf]; refine (mul_le_mul_of_nonneg_left ht₀ (Real.exp_pos _).le).trans ?_; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; rw [sites_as_price] at hY -- alias fhs `N=` binder defeq
 change F'≤ (Ψ'/2)*S+(clocks.grain x₀/2)*t₃ at hw; change b_f≤ (Ψ'/2)*S+(ledge x₀/2)*t₄ at hY; change Γ/2+_ ≤ -L+Γ+(a+(3*E+Ψ')*S); rw [hΓ]; linarith only [hw,hY]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
