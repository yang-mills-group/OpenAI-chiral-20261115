import YM.SatinExist.Glacis
import YM.SatinExist.Crust
import SatinThinRoman
import SatinThinTrees
import SatinThinCrystal
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
open Regis.Head.Etch
variable (i k:ℕ){f r v d:ℕ}{a c:ℝ}
local notation "L"=> P.R.L
local notation "Δ"=> P.block
local notation "Ω" j:max=> side Y i j
local notation "Gξ" j:max=> Vale.apt (Y.ir i) P.block P.R.L j
open Again Buffered.Afterglow.Tower.SlabMark
variable {A b z U u:ℝ} {m j:ℕ} (p:f ≤ r)(x:r ≤ v)(l:List (Site (side Y i f)))
lemma genuine_ticket (V:Credentials Y i k A f v)(t:Consulate Y i k (p:=V.scope) A b)(X:ShelterCost c Y f i k) {l:List (Site (side Y i f))}(w:outdoor (rural (RootBook Y i k f).p.B) l):
    ‖Journey.compass Y i k v (l.map (Yoke.principal Y i k V.scope b)).prod‖ ≤ steamRent P A f (side Y i f) (2*l.length) l.length:=by
 obtain ⟨s,Q⟩:= t.emit
 let J:=List.finRange l.length
 obtain ⟨E,F,z,v',a⟩:= Q (Fin l.length) l.get (solid_call Y i k l w)
 have ht: J.Nodup:= List.nodup_finRange _
 obtain ⟨q,q',r⟩:= a.sky J ht
 let N:= side Y i f; let G:= artwork Y i k E F (J.map Prin)
 have hv: Integrable (fun x:Orbit N=> beamZ _ (G x)) (city _) := ((Env.integrableX (Girt.pole_w q (beamZ N) (beamL _).continuous r) (city _))).congr (q'.symm.mono fun y w=>congrArg (beamZ N) w)
 have hp:= warp_receipt Y X E F v' l.get z (J.map Prin) hv
 let Z:=(l.map (Yoke.principal Y i k V.scope b)).prod
 have hu : markedRead 1 ((Y.voyage i).CapeT f) G = mark_cost Y i k v Z:=by
    have e := a.grant J ht 1 (AtSupport.oneM _)
    apply e.trans; congr 1
    rw [convoy_one,one_mul,← List.map_map,List.map_get_finRange]
    exact V.pays
    exact V.caps
 change ‖mark_cost Y i k v Z/coined Y i k v‖≤ _
 rw [← hu,markvac,← minted_steps Y i k V.caps V.scope]; apply hp.trans_eq; congr 1
 · simp [QuadClock.Article,mul_comm] -- name
 simp [J]
lemma truthful (V:Credentials Y i k A f v)(H:Real.exp 1≤P.x)(g:Ferry Y v i k)(e:ℕ)(b:ℝ): GraceA Δ (repeatD P ℓ e) (rural e) (Yoke.principal Y i k V.scope b) (solder Y i k g.depth v) (highTurn P f v) (reserve P ℓ):=by
 let p:=V.scope; let M:=graceful_clock Y i k p (Nat.le_refl v) (b:=1) (z:=1) H g e
 constructor
 · exact M.gap
 · intro j s x h
   exact band_true Y i k j _ _ (Nat.le_add_right _ _) (moving_band Y i _ _ _ p h) b
 · intro i s x; unfold Yoke.principal; rw [heel_swing,route_swing]
 exact M.heat
lemma true_oval {p:f≤v}(l:List (Site (side Y i f))) (b:ℝ): Envelope (l.map (Yoke.principal Y i k p b)).prod:= (receipt_word (F:=fun x=>Yoke.principal Y i k p b x) (fun x=>route_owns Y i k v b (upRoot Y i p x)) l (S:=univ) fun _ _=>subset_univ _).env
-- cost unscaled with no sigma purchase left. exact.Read.
lemma white_ticket (V:Credentials Y i k A f v)(X:ShelterCost c Y f i k) {l:List (Site (side Y i f))}(w:outdoor (rural (RootBook Y i k f).p.B) l):
    ‖Journey.compass Y i k v (l.map (Yoke.principal Y i k V.scope 1)).prod‖ ≤ (fareMin L (v-f))^l.length * steamRent P A f (side Y i f) (2*l.length) l.length:=by
 obtain ⟨b,B⟩:= purchased_theta Y i k V.scope V
 let p:=V.scope; let q:=((b⁻¹:ℝ):ℂ)
 have hy(z:Site (Ω f)): Yoke.principal Y i k p 1 z=q • Yoke.principal Y i k p b z:=by
    unfold Yoke.principal routeTip; rw [smul_smul, show q * (b:ℂ)=1 by unfold q; rw [←Complex.ofReal_mul, inv_mul_cancel₀ B.aims.nz, Complex.ofReal_one],Complex.ofReal_one]
 have ht(l:List (Site (Ω f))): (l.map (Yoke.principal Y i k p 1)).prod=q^l.length • (l.map (Yoke.principal Y i k V.scope b)).prod:=by
    induction l with | nil=> simp | cons i l ih=> rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,hy,ih,List.length_cons,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,pow_succ]
 have hk:0 ≤ fareMin L (v-f):= (abs_nonneg _).trans B.aims.small
 have he:‖q^l.length‖ ≤ (fareMin L (v-f))^l.length:=by rw [norm_pow]; apply pow_le_pow_left₀ (norm_nonneg _); unfold q; simpa only [Complex.norm_real,Real.norm_eq_abs] using B.aims.small
 rw [ht]; unfold Journey.compass; rw [mark_smul,mul_div_assoc] -- lemma
 rw [norm_mul]; exact mul_le_mul he (genuine_ticket Y i k V B X w) (norm_nonneg _) (pow_nonneg hk _)
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
