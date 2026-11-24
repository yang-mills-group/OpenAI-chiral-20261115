import ZecaCrew
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

variable {A b z t': ℝ} (hp:f≤r)(hz:r≤v)(l:List (Site (side Y i f)))
local notation "e"=> (RootBook Y i k f).p.B
lemma zecaPrinTicket (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A hp hz b z t')(h:outdoor (rural e) l):
 ‖Journey.compass Y i k v (l.map (fun o=> (t':ℂ) • principal Y i k (hp.trans hz) b o)).prod‖≤ steamRent P A f (side Y i f) (2*l.length) l.length:=by
 let α:=Fin l.length; let Z:= List.finRange l.length; let V:= Z.map Prin; have ht:CasePage V:=by
    unfold V CasePage; rw [List.map_map,show (QuadClock.host ∘ Prin) = _root_.id (α:=α) from rfl,List.map_id]; exact List.nodup_finRange _ -- tune
 have he:= layout_receipt Y X hp hz u' l.get (solid_call Y i k l h) V ht; have hv: V.map (menuClock Y i k l.get b z t' hp hz)= l.map (fun o=> (t':ℂ) • principal Y i k (hp.trans hz) b o):=by
    unfold V; rw [List.map_map,show menuClock Y i k l.get b z t' hp hz ∘ Prin= (fun o=> (t':ℂ) • principal Y i k (hp.trans hz) b o) ∘ l.get from funext fun _=> menu0 ..,←List.map_map,List.map_get_finRange l]; -- Z reducible?
 rw [hv] at he; apply he.trans_eq; congr 1
 · simp [Article,mul_comm] -- Lex card
 simp [V,Z]


abbrev violet (P:Preparation)(f:ℕ)(A:ℝ):= (slotFee P f)*Real.exp (8*A+1)
local notation "ε"=> meterC (hat L P.x f)
variable (X:ShelterCost c Y f i k)
 (D:ℕ)(α:14*Worth.meterC (hat P.R.L P.x f)*(D:ℝ)^4≤1)
 (N: (More (side Y i f)).val^4 ≤ l.length * D^4)
include X in
lemma violet_pos: 0<violet P f A:=by
 obtain ⟨_,_,p',_,_⟩:= X.load.health; exact mul_pos p' (Real.exp_pos _)
include X α N
lemma violet_fit: steamRent P A f (side Y i f) (2*l.length) l.length
      ≤ (violet P f A)^l.length:=by
 obtain ⟨_,_,vp,m',_⟩:=X.load.health;
 let aε:= ε; have ha:0≤aε:=vp.le.trans m'; let n:= side Y i f
 have hy: sites n ≤ (l.length:ℝ)*(D:ℝ)^4:=by unfold sites; exact_mod_cast N
 unfold steamRent violet; rw [mul_pow,← Real.exp_nat_mul]
 apply mul_le_mul_of_nonneg_left _ (pow_nonneg vp.le _)
 push_cast; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left hy ha,mul_le_mul_of_nonneg_left α (Nat.cast_nonneg (α:=ℝ) l.length)]
lemma violet_gap
 (u':ReadDensity Y i k A hp hz b z t')(h:outdoor (rural (RootBook Y i k f).p.B) l):
 ‖Journey.compass Y i k v (l.map (gapMark Y i k b z hp hz)).prod‖
    ≤ (violet P f A)^l.length:=
 (gap_ticket Y i k hp hz l X u' h).trans (violet_fit Y i k l X D α N)
omit X α N
-- Mark has SMulCommClass? tactic induct prod.
lemma pulls_principal (b t:ℝ)(h:t*b ≠ 0) : let g:= principal Y i k hp;
 (l.map (g 1)).prod=(↑((t*b)⁻¹):ℂ)^l.length •
    (l.map (fun x=>(t:ℂ) • g b x)).prod
 :=by 
 intro g
 have hu (x:Site (Ω f)):g 1 x=(↑((t*b)⁻¹):ℂ) • ((t:ℂ) • g b x):=by
    dsimp only [g,principal,routeTip]
    rw [smul_smul,smul_smul,mul_assoc,←Complex.ofReal_mul,←Complex.ofReal_mul,inv_mul_cancel₀ h]
 induction l with
 | nil=> simp
 | cons z l ih=>
     simp only [List.length_cons,pow_succ',List.map_cons,List.prod_cons]
     rw [ih,hu z,mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm]

include X α N
lemma violet_principal (G:PaysTilt Y i k f r r A) (h:outdoor (rural (RootBook Y i k f).p.B) l):
 ‖Journey.compass Y i k r (l.map (principal Y i k hp 1)).prod‖
  ≤ ((fareMin L (r-f)) * violet P f A)^l.length:=by
 obtain ⟨b',z',t,_,w,x,w',_⟩:= G.reading
 have u:=mul_ne_zero x.breath.nz w.aims.nz
 have v:|b'⁻¹|≤1:=w.aims.small.trans_eq (by simp [fareMin])
 have v':‖(↑((t*b')⁻¹):ℂ)‖≤ fareMin L (r-f):=by
    rw [Complex.norm_real, Real.norm_eq_abs, mul_inv_rev,abs_mul]
    exact (mul_le_mul v x.breath.small (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
 have q:=
   (zecaPrinTicket Y i k hp le_rfl l X w' h).trans (violet_fit Y i k l X D α N)
 have h' :0≤fareMin L (r-f):= (norm_nonneg _).trans v'
 rw [show (l.map (principal Y i k hp 1)).prod = _ from pulls_principal Y i k hp l b' t u]
 unfold Journey.compass at *;
 rw [mark_smul,mul_div_assoc,norm_mul,norm_pow,mul_pow]
 exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) v' _) q (norm_nonneg _) (pow_nonneg h' _)
omit X α N

abbrev starGrace (size price:ℕ)(W:Site (side Y i f)→Buffered.Mark (side Y i v)) (hm: (Y.voyage i).kick ≤ k): Prop:=
  Cardigan.Grace P.block node
   (fun j s=> (plane j s).mills (Journey.side Y i f))
   size price W (solder Y i k hm v)
    (fun x=> (((P.R.L.val^(v-f)):ℕ):ℤ) * x) (reserve P ℓ)
lemma shrubGrace {κ:ℕ} (H:Real.exp 1≤ P.x)(g:Ferry Y v i k):
 starGrace Y i k (repeatD P ℓ κ) (rural κ) (gapMark Y i k b z hp hz) g.depth:=by
 unfold starGrace; rw [show (fun (x:ℤ)=> (((P.R.L.val^(v-f)):ℕ):ℤ)*x)= highTurn P f v from funext (fun x=>by unfold highTurn; push_cast; rfl)]
 let Z:=graceful_clock (b:=b) (z:=z) Y i k hp hz H g κ
 exact ⟨fun a q y=> Shape.nodex _ _,fun x=>((message_support Y i k b z hp hz x g.depth g.enters).2).mono (subset_univ _),Z.gap,Z.price,Z.spin,Z.heat⟩
lemma violetGrace {κ:ℕ} (H:Real.exp 1≤ P.x)(g:Ferry Y r i k):
 starGrace Y i k (repeatD P ℓ κ) (rural κ) (principal Y i k hp 1) g.depth:= by
 unfold starGrace
 rw [show (fun (x:ℤ)=> (((P.R.L.val^(r-f)):ℕ):ℤ)*x)= highTurn P f r from funext (fun x=>by unfold highTurn; push_cast; rfl)]
 unfold principal
 let Z:=graceful_clock (b:=1) (z:=1) Y i k hp le_rfl H g κ
 refine ⟨fun a q y=> Shape.nodex _ _, fun x=> (route_owns ..).mono (subset_univ _), Z.gap,?_,?_,Z.heat⟩
 · intro a q x p
   exact band_true Y i k a _ _
     (Nat.le_add_right _ _) (moving_band Y i a q x hp p) _
 intro a q x
 rw [heel_swing,route_swing]

include hp in
lemma odessaScale : (Journey.side Y i r).val= P.R.L.val^(r-f) * (Journey.side Y i f).val :=by
 induction hp with
 | refl=>simp
 | @step u s ih=>
   have h:=(Vale.apt (Y.ir i) P.block P.R.L u).exact_size
   rw [Nat.succ_sub s,pow_succ',mul_assoc,←ih,mul_comm]
   exact h
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
