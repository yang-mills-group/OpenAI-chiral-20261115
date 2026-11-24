/- Compatibility lift, near-exact baseline YM/SU5/Thin/Cascade/Flight.lean with narrower imports omitting Vellum. No proof changes. -/
import YM.SU5.Thin.Cascade.Poetry
import YM.SU5.Thin.Cascade.Marks
import YM.SU5.Thin.Cascade.Swing
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
abbrev ΥU(s:ℕ)(Λ:Preparation):=hat Λ.R.L Λ.x s
-- simple weight budget, explicitly PathPose enrolled before s.
structure Convent (Λ:Preparation) (ε a C D:ℝ)(z bb:ℕ): Prop where
 health : Finisher ε a C Λ.K.j z
 size : 0≤D
 lifts (N:Side) : Even N.val → bb≤ N.val → LiftMark D Λ.K.j N
 applicable : Λ.d ≤ ε
 price : (C+1)*(45*(D+1)) ≤ Λ.h
variable {ε a C D:ℝ}{v b s i k ℓ:ℕ}
local notation "mL" => mesh (Y.ir i) P.R.L s
local notation "M"=> count Y s i
local notation "ρ"=> P.K.j
local notation "X"=> room Y s i
abbrev flareUp (U:ℝ):=45*(U+1)
structure Fashion (Y:Course P (VolumeCape.Dream.Nimbus l))(ε a C D:ℝ)(v b s i:ℕ) : Prop where
 auth : Convent P ε a C D v b
 within : v≤(count Y s i).val ∧ b≤ (count Y s i).val
 width : Even (count Y s i).val
-- weights abstract B1/B2 independent symbol transport, no limit claims
abbrev fit_fare (U:Orbit (count Y s i))(γ γ' C D:ℝ)(l':ℕ):ℝ := let w:= P.J.n;  let u:=cashU P.W.C; (((1+C)^2 * (180^2 * (storm U γ γ' w l' u 1+storm U γ γ' w l' u 2)))*(flareUp D)^2)+paintE (r:=w) l' U γ γ' u
-- avoid using implicit Y on fee measures explicit. set Axis normative alloc D.
variable (p:Fashion Y ε a C D v b s i)
variable {t t₁ t₂ θ ζ B₁ B₂ a':ℝ}
local notation "θA"=>levelQ P.W.C
local notation "θB"=>cashU P.W.C
include p in
lemma opticScope (U:Orbit (count Y s i))(R:GramM (count Y s i))(z:Seat (count Y s i) → SU.E) : let Z₁:= Lattice.gauge z ((room Y s i) U); let W:=spar P.K.j R.J.M Z₁; let W':=spar P.K.j R.J.M (1:Pane (count Y s i)); Gall.Yep (flareUp D) (mateK (count Y s i)) (changeM P.U ((room Y s i) U) R.J.M) (Real.exp (angleFin R.J.M (count Y s i) P.K.j + ((1+D)^2+1)* DriveL1 (W-W')/2)):=by
 intro Z₁ W W'; let h:1≤P.K.j:=by rw [P.kJ]; decide; --scope
 let xQ:= p.auth.lifts _ p.width p.within.2; obtain ⟨z',H,J⟩:= xQ R.J.M; let u:=P.U; let M':=R.J.M; let A:=count Y s i
 have hp:u.roundZ ≤ A.val:=P.J.gran.trans ((Y.voyage i).ownership s).size
 have h0: Guard (1:Bkg (More A)) P.d:= Tulip.guard0 P.dpos.le; have hv: Guard Z₁ P.d := ((roofage Y i s).paid U).cov z;
 obtain ⟨u,H',_⟩:= angle_pay R.J.M ρ P.U (Vale.mesh (Y.ir i) P.R.L s) h hp P.dpos; rw [H', Real.exp_add, Real.exp_log (norm_pos_iff.mpr u)]; have hz:IsStarProjection W:=(P.U.broadness _ hp M').projection _ hv; let habs:= payment H J _ (sea_g (P:=P.U) hp Z₁ hv M') _ (sea_g (P:=P.U) hp 1 h0 M') _ (tickB A) hz
 exact (Gall.rose P.W.pearl P.V.note hp h R.J.M _ z hv (add_nonneg p.auth.size zero_le_one) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) habs).2
include p
-- compressed field as pointwise bound
lemma issuesPa (U:Orbit (count Y s i))(R:GramM (count Y s i))(t₁ t₂:ℝ)(Z:Graph.Ledger P.h t₁ t₂ (levelQ P.W.C) (cashU P.W.C) R)(wl:0≤θ)(V₀:θ ≤ P.J.k)(t:ℝ)(ht:θ+2*Real.exp (-((levelQ P.W.C)*ℓ)) ≤ t)(hl:ℓ≤ (More (count Y s i)).val)(F:Seat (count Y s i)→SU.E)
   (hc:DriveL1 (spar P.K.j R.J.M (Lattice.gauge F ((room Y s i) U))-spar P.K.j R.J.M (1:Pane (count Y s i)))≤ B₁):
    ‖Complex.exp (-R.v)* beamZ (count Y s i) (denZ R P.U (room Y s i) U)‖ ≤ Real.exp (angleFin R.J.M (count Y s i) P.K.j - R.path.inChannels R.funds R.p R.beta U.1 + ((t₁+t₁+t₂)*sites (count Y s i) + fit_fare Y U θ t C D ℓ + ((1+D)^2+1)*B₁/2)):=by
 let A:= room Y s i; let P':= spar P.K.j R.J.M (A U); let s':= (More M).val; let w:= (((1+C)^2 * (180^2 * (storm U θ t P.J.n ℓ θB 1+storm U θ t P.J.n ℓ θB 2)))*(flareUp D)^2); let m:=P.K.j; let C':=p.auth.health; let t':= angleFin R.J.M M m; let Q:= (t₁+t₁+t₂)*sites M; let Y':= mile m R A U; let Mo:= changeM P.U (A U) R.J.M
 let Η:= Lattice.gauge F (A U); have hW:=roofage Y i s; let T:= hW.paid U; have he: IsStarProjection P':=(P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) R.J.M).projection (A U) T; have hQ : Filed P' C:= p.auth.health.column M p.within.1 _ (T.shrink p.auth.applicable) R.J.M
 have hx:0 ≤ flareUp D:=by unfold flareUp; have hh:=p.auth.size; positivity
 let L := paintE (r:=P.J.n) ℓ U θ t θB; have hp: Gall.Pays (flareUp D) Y' (Real.exp (Q+(fit_fare Y U θ t C D ℓ))):=by
    let k:= Gall.Pays.mul (show Gall.Pays (flareUp D) _ (Real.exp Q) from shipsBoard R P' U he Z hQ hx (zero_le_one.trans P.height) p.auth.price) (gifts (show Gall.Pays (flareUp D) (dg (actF m R A U)) w from preparesG R Z hx U hW V₀ (level_p _).le wl hl (cash_v _) t ht he hQ p.auth.health.credit.le)); let F:= Pec.pigment R.J.I (A U); refine (k.linear (Complex.exp (-F))).weigh ?_ hx; apply le_trans (mul_le_mul_of_nonneg_right ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_monotone (?_ : ‖-F‖≤L))) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (le_of_eq ?_) -- b annotation likely invalid
    · rw [norm_neg]; exact aur_pin _ _ Z.field.2 U rfl hW V₀ (level_p _).le wl hl (cash_v _) _ ht
    rw [←Real.exp_add,←Real.exp_add]; change Real.exp _= Real.exp (Q+(w+L)); congr 1; ring
 let α:= Lattice.gauge F (A U); let H:= DriveL1 (spar m R.J.M α-spar m R.J.M (1:Pane M)); let x₀:=t'+((1+D)^2+1)*B₁/2; have hg:H≤ B₁:=hc; let q:= opticScope Y p U R F; have hk: Gall.Yep (flareUp D) (mateK M) Mo (Real.exp x₀):=q.weigh (Real.exp_monotone (show t'+((1+D)^2+1)*H/2 ≤ _ from (by unfold x₀; gcongr))) hx
 have hv:= (hp.2 (mateK M) Mo (Real.exp x₀) (Real.exp_pos _).le hk).low
 rw [mote,Scree.beamZ, inner_smul_right, ←mul_assoc,←Complex.exp_add,norm_mul,Complex.norm_exp, GramM.H0] -- tune complex `H0=v-action` uses simp
 apply (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans_eq; simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re, Complex.neg_re]; rw [←Real.exp_add,←Real.exp_add]; unfold x₀ Q t'; congr 1; ring -- adjust
end Papal
end LocalLimit
end Rate
end YM.CF.Py
