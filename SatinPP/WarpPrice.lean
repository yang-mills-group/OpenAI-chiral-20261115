import SatinThinRoman
import SatinPP.Renew
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
local notation "w" => reserve P ℓ
variable (a':Axis)(s:ℤ)
variable {b z A t':ℝ}(hp:f≤r)(hz:r≤v)
lemma graceful_prin (a:ℝ) (H:Real.exp 1≤ P.x)(g:Ferry Y v i k)(e:ℕ):
 Again.GraceA Δ (repeatD P ℓ e) (rural e) (principal Y i k (hp.trans hz) a) (solder Y i k g.depth v) (highTurn P f v) (reserve P ℓ):=by
 refine ⟨by unfold repeatD; omega, fun i' s x u=> band_true Y i k i' _ _ (show w+12 ≤ repeatD P ℓ e from Nat.le_add_right _ _) (moving_band Y i i' s _ (hp.trans hz) u) a, fun i' s x=> by unfold principal; rw [heel_swing,route_swing],?_⟩
 intro a t f' B YQ; let z:= Heat.gaugeShift Δ t; let v':= (highTurn P f v t); have hp:highTurn P f v z= Heat.gaugeShift Δ v':=by unfold v' z highTurn Heat.gaugeShift; ring
 have hx: AtSupport false (band (Ω v) a (Heat.gaugeShift Δ v') w) f':= hp ▸ YQ; rw [show B= _ from hp]; exact tenderD Y H v i k g a v' f' hx -- B deflet; hp rw z
open Again
variable (l:List (Site (side Y i f)))
local notation "e"=> (RootBook Y i k f).p.B
lemma prin_ticket (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A hp hz b z t')(h:outdoor (rural e) l):
 ‖Journey.compass Y i k v (l.map ((fun y=> ((t':ℝ):ℂ) • principal Y i k (hp.trans hz) b y))).prod‖≤ steamRent P A f (side Y i f) (2*l.length) l.length:=by
 let α:=Fin l.length; let Z:= List.finRange l.length; let V:= Z.map Prin; have ht:CasePage V:=by
    unfold V CasePage; rw [List.map_map,show (QuadClock.host ∘ Prin) = _root_.id (α:=α) from rfl,List.map_id]; exact List.nodup_finRange _ -- tune
 have he:= layout_receipt Y X hp hz u' l.get (solid_call Y i k l h) V ht; have hv: V.map (menuClock Y i k l.get b z t' hp hz)= l.map ((fun y=> ((t':ℝ):ℂ) • principal Y i k (hp.trans hz) b y)):=by
    unfold V; rw [List.map_map,show menuClock Y i k l.get b z t' hp hz ∘ Prin= ((fun y=> ((t':ℝ):ℂ) • principal Y i k (hp.trans hz) b y)) ∘ l.get from funext fun _=> menu0 ..,←List.map_map,List.map_get_finRange l]; -- Z reducible?
 rw [hv] at he; apply he.trans_eq; congr 1
 · simp [Article,mul_comm] -- Lex card
 simp [V,Z]
variable {θ:ℝ}
local notation "θa"=> Real.exp (-(8*A+1002))
lemma prin_cap (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A hp hz b z t')
    (h:outdoor (rural e) l)
    (ht:|θ| ≤ Real.exp (-(8*A+1002)) * |t'*b|):
    ‖Journey.compass Y i k v (l.map (principal Y i k (hp.trans hz) θ)).prod‖ ≤
      θa^l.length * steamRent P A f (side Y i f) (2*l.length) l.length:=by
 let G:= t'*b; let q:= θ/G
 have h₀: q*(t'*b)= θ ∧ |q| ≤ θa := by
   by_cases z:G=0
   · change |θ| ≤ _ * |G| at ht
     unfold q; simp only [z,abs_zero,mul_zero,div_zero,zero_mul] at *
     exact ⟨((abs_nonpos_iff.mp ht).symm), (Real.exp_pos _).le⟩
   exact ⟨div_mul_cancel₀ _ z,(abs_div ..).trans_le ((div_le_iff₀ (abs_pos.mpr z)).2 ht)⟩
 let T (x:Site (side Y i f)):= (t':ℂ) • principal Y i k (hp.trans hz) b x
 have he(l:List (Site (side Y i f))):
       (l.map (principal Y i k (hp.trans hz) θ)).prod=
       ((q:ℂ)^l.length) • (l.map T).prod:=by
   induction l with
   | nil => simp
   | cons o s ih=>
     rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,ih,List.length_cons,pow_succ']
     have t: principal Y i k (hp.trans hz) θ o=(q:ℂ) • T o:=by
        unfold T principal routeTip
        rw [show (θ:ℂ)=q*(t'*b) from by exact_mod_cast h₀.1.symm,mul_smul,mul_smul]
     rw [t,mul_smul,mul_smul_comm,smul_mul_assoc,smul_comm]
 rw [he]; unfold Journey.compass; rw [mark_smul,mul_div_assoc,norm_mul,norm_pow,Complex.norm_real, Real.norm_eq_abs]
 exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h₀.2 _) (prin_ticket Y i k hp hz l X u' h) (norm_nonneg _) (by positivity)
local notation "gξ"=> repeatD P ℓ (RootBook Y i k f).p.B
local notation "Kξ"=> plusAgain P.block (gξ)
lemma prin_full (t2:14*meterC (hat P.R.L P.x f)*(((4*(d+Kξ):ℕ):ℝ))^4 ≤ 1)
    (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A hp hz b z t')
    (h:outdoor (rural e) l)
    (ht:|θ| ≤ Real.exp (-(8*A+1002)) * |t'*b|)
    (hw:(More (side Y i f)).val^4≤l.length*(4*(d+Kξ))^4):
    ‖Journey.compass Y i k v (l.map (principal Y i k (hp.trans hz) θ)).prod‖ ≤
      Real.exp (-1001)^l.length:=by
 obtain ⟨_,_,p',m',_⟩:=X.load.health
 apply le_trans (prin_cap Y i k hp hz l X u' h ht)
 let fee:= slotFee P f; let M:= meterC (hat P.R.L P.x f)
 have hM:0≤M:=p'.le.trans m'
 let R:=d+Kξ
 have hR:1 ≤ (4*R:ℕ):= by have H:= @plusAgain_pos P.block gξ; omega
 have hv: fee≤1:=by
   apply m'.trans
   have h: (1:ℝ)≤(((4*R:ℕ):ℝ))^4:=one_le_pow₀ (by exact_mod_cast hR)
   change 14*M*(((4*R:ℕ):ℝ))^4≤ 1 at t2
   change M≤1
   nlinarith only [t2,h,hM]
 let J:=l.length; let n:=side Y i f
 have hs: sites n ≤ (J:ℝ)*(((4*R:ℕ):ℝ))^4:=by unfold sites; exact_mod_cast hw
 have aM:14*M*sites n ≤ J:=by
   change 14*M*(((4*R:ℕ):ℝ))^4≤ 1 at t2
   nlinarith only [mul_le_mul_of_nonneg_left hs hM,mul_le_mul_of_nonneg_left t2 (Nat.cast_nonneg (α:=ℝ) J)]
 change θa^J*(fee^J*Real.exp (4*A*(↑(2*J):ℝ)+14*M*sites n)) ≤ Real.exp (-1001)^J
 refine le_trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (Real.exp_pos _|>.le) (pow_le_one₀ p'.le hv)) (by positivity)) ?_
 rw [←Real.exp_nat_mul, ←Real.exp_nat_mul, ←Real.exp_add]
 push_cast
 exact Real.exp_monotone (by linarith only [aM])

open Buffered.Afterglow.Tower.SlabMark

set_option maxHeartbeats 500000
/-- Purchase the sharp price of long outdoor arrays. Equality to a
specific (tape) banner not needed yet. Length *low* clock ticks
controls density; high-clock copies needn't be dense at all. -/
lemma compass_long
   (t1:d+plusAgain P.block (repeatD P ℓ (RootBook Y i k f).p.B)≤(side Y i f).val)
    (t2:14*meterC (hat P.R.L P.x f)*(((4*(d+Kξ):ℕ):ℝ))^4 ≤ 1)
     (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A hp hz b z t')
    (h:outdoor (rural e) l)
    (ht:|θ| ≤ Real.exp (-(8*A+1002)) * |t'*b|)
    (j:Axis)
    (lower:(side Y i f).val ≤ l.length*d)
    (upper:l.length ≤ 2*(side Y i f).val)
    (trans:∀ a,a≠j → cows a (upperRoll l) d)
    (H:Real.exp 1≤ P.x)(g:Ferry Y v i k)(a:IcePlot Y v i k)
    (U:ℝ)(u₀:0≤U)
    (pay:∀ x:Fields (side Y i v), ‖(l.map (principal Y i k (hp.trans hz) θ)).prod x‖≤ U^l.length)
    (t0: U*(16/Real.exp (-1001)) ≤ (side Y i v).val):
    ‖Journey.compass Y i k v (l.map (principal Y i k (hp.trans hz) θ)).prod‖ ≤
      3*(Real.exp (-1001))^l.length:=by
 let B:=side Y i v; let n:= side Y i f
 let Z:=solder Y i k g.depth v
 let T':=Journey.compass Y i k v; let E:=principal Y i k (hp.trans hz) θ
 let W L':=(List.map E L').prod; let D':=Real.exp (-1001)
 have t':0<D':= Real.exp_pos _
 have he:∀ {L':List (Site n)}, L'.length≤(More B).val^4→
      (∀ t:Fields B,‖(W L') t‖≤ U^L'.length)→ ‖T' (W L')-Z (W L')‖≤ D'^L'.length:= by
    intro L' t v'
    have env: Envelope (W L'):= (receipt_word (fun i': Site n=>
      show AtSupport false _ (E i') from route_owns Y i k v θ _) L'
      (S:=univ) fun _ _=> subset_univ _).env
    exact (a _ (W L') _ env v').trans (hailW Y i t' u₀ t0 t)
 obtain ⟨y,J,hG,hJ,cn,ym,a',pv,hℕ⟩:=renewed_transverse
      (p:=E) (graceful_prin Y i k hp hz θ H g e) l j h trans t1 lower upper pay
 have ht0:(More n).val ≤ (More B).val:= Nat.mul_le_mul_right 2 (growingM Y i (hp.trans hz))
 have pv':= pv.trans (pow_le_pow_left' ht0 _)
 have h₀: ‖T' (W y)‖≤ D'^y.length:=
   prin_full Y i k hp hz y t2 X u' hG ht hℕ
 have htp: ‖Z (W l)‖ ≤ 2*D'^l.length:=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (n:=J) a'.ne').mp
    apply ym.trans
    refine ((norm_le_norm_sub_add (Z (W y)) (T' (W y))).trans (add_le_add ((norm_sub_rev ..).trans_le (he pv' cn)) h₀)).trans ?_
    rw [←two_mul,mul_pow,hJ,Nat.mul_comm,pow_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (show (2:ℝ)=2^1 from pow_one _|>.symm).trans_le (pow_le_pow_right₀ (by norm_num) a')
 have hc:= he ((Nat.le_mul_of_pos_left l.length a').trans (le_trans (le_of_eq hJ.symm) pv')) pay
 exact ((norm_le_norm_sub_add (T' (W l)) (Z (W l))).trans (add_le_add hc htp)).trans_eq (by ring)

end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
