import YM.SU5.WakeInvestment.TractLeaf
import YM.SU5.WakeInvestment.DyeRates
set_option maxHeartbeats 300000
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
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

open WakeInvestment Gleam.Wake
open Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
variable (s i k : ℕ)
local notation "X" s:max => hat P.R.L P.x s
local notation "χ" s:max c:max => WakeInvestment.chip (hat P.R.L P.x s) c
local notation "Θ" T:max=> tollR T
local notation "Υ" T:max=> tabμ T
local notation "wax" s:max=> (Υ (θ s))
local notation "ℓop" s:max i:max k:max t:max=> (WakeInvestment.weighted (spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))) t (flatShear Y s i k))

/-! # Sample point at finite Gauge: boarding polynomial leads

 `F` is the scalar function of a finite list of face components taking spin-Wick first.
 Outcome XQ = $w_s(P_F)$ on unit stamen (all covariance still at this n,M).
 Unlike WA.7 asks for equivariant/scalar transport version Φ with budgets,
 purchases it when checking real *material*. LightBar is then payable also for
 rear-rates of any such voter. -/
open Regis.Wake (Paint drip mute_mix muting mute_shrink mute_ceiling mute_same mute_smooth lipClay assay)
open ProbabilityTheory
variable {I:Type*} [Fintype I] {d m:ℕ}
local notation "qθ" => P.K.top.clip
local notation "ωs" s:max k:max => Y.uv k - s
local notation "Bθ" s:max k:max => P.V.L.mood (Y.uv k - s)
local notation "Pθ" s:max k:max => P.V.L.tied (Y.uv k - s)
local notation "qP" s:max i:max k:max => RootBook Y i k s
local notation "stageR" s:max i:max k:max => stamen (Bθ s k) (Pθ s k) (More (side Y i s))
variable {A α Rc:ℝ}
variable {F:(I→ℝ)→ℂ}{S:Support (More (side Y i s))}
variable (V:Gleam.Wake.Vessel SU.group (More (side Y i s)) I)

abbrev hug (z c:ℂ) (Φ:Pane n→ℂ) (U:Pane n):ℝ:= (z*(Φ U - c)).re
abbrev bornQ (P:Preparation)(s:ℕ):ℝ:= Real.sqrt (hat P.R.L P.x s)
abbrev reachCost (ρ:ℝ):= ρ*Next.SectorChange.coupling (RootBook Y i k s).beta

def seatT (G:(I→ℝ)→ℂ)(ρ:ℝ):ℂ:= let F:=Y.uv k - s; let H:=stamen (P.V.L.mood F) (P.V.L.tied F) (More (side Y i s)); ∫ x:H,V.basin (reachCost Y s i k ρ) G P.K.top.clip x.val ∂stdGaussian H
abbrev WellDrawn (α:ℝ) (S:Support (More (N s i)))(U:Pane (N s i)) : Prop := Tiny S U (skyline (hat P.R.L P.x s)) ∧ ordinary (possession (n:=side Y i s) S) (α*(RootBook Y i k s).p.threshold) U
structure Batch (F:(I→ℝ)→ℂ)(A α ρ:ℝ)(m:ℕ)(S:Support (More (N s i)))(Φ:Pane (N s i)→ℂ):Prop where
 ship: V.Ship S (radiusB (hat P.R.L P.x s))
 cost: Paint F m (sPow P s A)
 cards: (↑(Fintype.card I):ℝ) ≤ sPow P s A
 near: α≤1
 mantle: |ρ| ≤2*bornQ P s
 env: RG.Envelope Φ
 gauge: GaugeInvariant Φ
 range: ∀ U, ‖Φ U‖≤ sPow P s A
 scene: ∀ U:Pane _, WellDrawn Y s i k α S U → ‖Φ U-F (V.material ρ U)‖ ≤ scratch (X s)
variable {Φ:Pane (side Y i s)→ℂ} (U:Batch Y s i k V F A α Rc m S Φ)
variable (p: DyeLease P s A m d)(paid:s≤ Y.uv k)
open Gleam.Wake.Vessel
local notation "H'" s:max => sPow P s A
local notation "Cap" q:max=> Gleam.Wake.Vessel.cap q 4
include U p paid
lemma Batch.frameFunds :
   Cap qθ ≥ Gleam.Wake.Vessel.cap qθ (reachCost Y s i k Rc) :=by
 obtain ⟨_,_,_,u,-⟩:= Papal.prices_plot Y s i k paid; let R:=RootBook Y i k s; have h0:= p.day; have hbpos:0 < R.beta:= (half_pos h0).trans_le u.1
 have hh:= Regis.Head.Etch.railB u.1 u.2 h0; let b:= coupling R.beta; have he:= coupling_pos hbpos
 have hx:|reachCost Y s i k Rc| ≤ 4:= by rw [reachCost,abs_mul,abs_of_pos he]; apply (mul_le_mul_of_nonneg_right U.mantle he.le).trans; rw [mul_assoc]; exact le_trans (mul_le_mul_of_nonneg_left hh.2 (by norm_num)) (le_of_eq (by norm_num))
 change |reachCost Y s i k Rc| * _ ≤ |(4:ℝ)| * _; rw [abs_of_pos (by norm_num : (0:ℝ)<4)]; gcongr
omit p paid U in
private lemma assay_mono (a b v:ℝ) (m:ℕ)(h:a≤b) : assay m v a≤ assay m v b:=by unfold assay; gcongr
lemma Batch.seatCost : ‖seatT Y s i k V F Rc‖ ≤ sPow P s (upperPay A):= by
 let T:= stageR s i k; let L':= reachCost Y s i k Rc; let f i:= (V.siphon L' 1 0 qθ i).comp T.subtypeL; have hc(i): ‖f i‖≤ Cap qθ:= (V.siphons_clamp L' _ _ _ _ _).trans (U.frameFunds Y s _ k V p paid); have hx:= Paint.soak f U.cost (Cap qθ) hc; have ha:0≤H' s:=(BProof.coin_pos ..).le
 apply hx.2.trans (p.assayE.trans' _); exact mul_le_mul_of_nonneg_left (assay_mono _ _ _ _ U.cards) ha
-- support licenses.
variable (t:Signed)(b:Skye.Seat (side Y i s)) {c:Side}{r: Ratio c (More (side Y i s))}
local notation "miℓ" s:max=> radiusB (X s)
local notation "μθ" s:max i:max k:max => stdGaussian (stageR s i k)
local notation "ρ$" s:max i:max k:max => reachCost Y s i k Rc
local notation "soilG" s:max i:max k:max => seatT Y s i k V F Rc

omit paid p U
lemma drawnT {t':ℝ}{L:Ratio c (More n)} {V:Pane n}{α:Support c}{X₀:Finset (Lattice.Face (Per (More n)))}{w:ℕ}{S:Support (More n)} (hx:X₀=misdemean t' V)(hp:∀ z∈ S, withinCore L α (face_anchors X₀) w z) : ordinary (possession (n:=n) S) t' V :=by
 subst X₀
 intro h g; have hv:=hp h.1 ((mem_filter.mp g).2 (Work.E01.base_touched h)); by_contra! hX; exact hv.2 (halo_spec.mpr ⟨_,mem_image_of_mem Prod.fst (mem_filter.mpr ⟨mem_univ _,hX⟩), show separation h.1 h.1 ≤ w from by simp⟩)
lemma calmT {v:ℝ}{w:ℕ}{S:Support (More n)}{r:Ratio c (More n)}{f:Pane n}{A:Support c}{B:Support (More n)}{D: Exterior.fieldDir SU.group (More n) 1} (p:1 ≤ w)(u: TrustLogs D f r A v)(b:∀ i∈ S,withinCore r A B w i): Tiny S f v:=fun i h _=>(u _ ⟨(b i.1 h).1.1,safeIn (b i.1 h).1 p⟩).2

include p U paid
lemma Batch.starch (z:ℂ)(h:‖z‖≤ leafCost (P:=P) s) : LeadVision Y s i k α c r S (hug z (seatT Y s i k V F Rc) Φ):=by
 let H:=RootBook Y i k s; let Xc:=θ s; let C:= Θ Xc; let n:=side Y i s; let ζ:= H' s; let η:=seatT Y s i k V F Rc; let R:= reachCost Y s i k Rc; let M:= stageR s i k; let J:=Cap qθ; let T:= H.p.threshold; let D:= dwarf m Xc; let V':=scratch Xc; let Δ:= tabμ Xc
 have he:= U.seatCost Y s _ k V p paid; have hE:= U.frameFunds Y s _ k V p paid; have hn:0≤ ζ:=(BProof.coin_pos ..).le; have hn':0 ≤ J:=by unfold J Gleam.Wake.Vessel.cap; positivity
 have hd:1≤D:= p.gift; have hd':0<D:= zero_lt_one.trans_le hd; have hz(f:ℂ)(hf:‖f‖≤ (ζ*(2*D)^m)): |(z*(f-η)).re| ≤ C:=by
    apply (Complex.abs_re_le_norm _).trans; rw [norm_mul]; exact (mul_le_mul h ((norm_sub_le ..).trans (add_le_add hf he)) (norm_nonneg _) ((norm_nonneg _).trans h)).trans p.wax
 let hx(U':Pane n):=hz _ ((U.range U').trans (le_mul_of_one_le_right hn (one_le_pow₀ (by linarith only [hd] : 1≤2*D)))); have hg: Measurable Φ:= U.env.meas
 refine ⟨⟨by unfold hug; fun_prop,C,fun x=>hx x⟩,hx,fun g x=>by rw [hug,hug,U.gauge g],?_⟩
 intro t b S₀; let μ:= stdGaussian M; let f:= V.siphon R t b qθ; let f0 i:= (f i).comp M.subtypeL; have hl (i:I): ‖f0 i‖ ≤ J:= (V.siphons_clamp R _ _ _ _ _).trans hE
 let x:= fun p:Altar SU.group (More n)=> muting D (drip f p); let Φ'(y:Altar SU.group (More n)):= F (x y); let Aφ(y):=(z*(Φ' y - η)).re
 have hv:ContDiff ℝ 1 Φ':= U.cost.bright.comp ((mute_smooth (I:=I) D).comp (contDiff_pi.mpr (fun i=>(f i).contDiff)))
 have hw(i j:ℂ): |(z*(i-η)).re - (z*(j-η)).re| ≤ ‖z‖* ‖i-j‖:= by rw [←Complex.sub_re,←mul_sub,sub_sub_sub_cancel_right,←norm_mul]; exact Complex.abs_re_le_norm _
 refine ⟨Aφ,(Complex.reCLM.contDiff.comp (contDiff_const.mul (hv.sub contDiff_const))), fun i=>hz _ (Paint.fade_cost U.cost hd (drip f i)),fun x y=>?_,?_,?_⟩
 · let y':=vase SU.group (More n) S₀ (x-y); apply (hw _ _).trans; unfold Φ'; let k:= lipClay; apply (mul_le_mul_of_nonneg_left (Paint.fade_lip U.cost hd (drip f x) (drip f y)) (norm_nonneg _)).trans
   have ht:‖drip f x-drip f y‖ ≤ J*‖y'‖:= by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hn' (norm_nonneg _))).mpr; intro i; change ‖(f i) x-(f i) y‖ ≤ _; rw [←map_sub,←show f i y'=_ from V.sight R t b qθ i U.ship (x-y)]; exact (V.siphon_price R t b qθ i y').trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
   let k:=ζ*(2*D)^m*(lipClay:ℝ); have hk:0≤k:=by unfold k; positivity
   change ‖z‖*(k*_) ≤ C*‖y'‖; refine (mul_le_mul h (mul_le_mul_of_nonneg_left ht hk) (mul_nonneg hk (norm_nonneg _)) ((norm_nonneg _).trans h)).trans ?_; let h':=mul_le_mul_of_nonneg_right p.wave (norm_nonneg y'); change leafCost (P:=P) s*(k*J)*‖y'‖ ≤ _ at h'; linarith only [h'] -- h: k difference assoc linarith unfold?
 · let m₀:= P.V.L; let R1:=Y.uv k-s; let P':=m₀.roof R1; let V1:= m₀.H R1; let Yθ:Bid.Sworn V1 (More n) SU.group:=P'.2.2 (More n)
   have ht: η=∫ u:M,F (drip f u.val) ∂stdGaussian M:= V.turn_basin (Bθ s k) (Pθ s k) (P'.2.1 (More n)) R t b Yθ F U.cost.bright.continuous
   have hF: Integrable (fun i:M=> Φ' i.val) (μ):= U.cost.faded_int (f0) hd; let u₀(i:M):= z*(Φ' i.val - η); have hF': Integrable u₀ μ:= (hF.sub (integrable_const _)).const_mul z; let w:= ∫ x:M, Φ' x.val∂μ
   unfold Head.clouds; rw [show ∫ i:M,Aφ i.val ∂stdGaussian M=(z*(w-η)).re from ?_]
   swap; · unfold w; rw [show ∫ i:M,Aφ i.val ∂stdGaussian M = (∫ i:M, u₀ i ∂stdGaussian M).re from integral_re hF']; unfold u₀; rw [integral_const_mul,integral_sub hF (integrable_const _), integral_const, probReal_univ,one_smul]
   have hf: ‖w-η‖≤ scratch Xc:= by
      rw [norm_sub_rev,ht]; let A':= U.cost.receipts f0 hd (m+1) J hl; have he: assay (m+(m+1)) J (Fintype.card I)≤ assay (m+(m+1)) J ζ:=assay_mono _ _ _ _ U.cards
      exact (A').trans ((mul_le_mul_of_nonneg_left he (show 0≤2*ζ/D^(m+1) from by positivity)).trans p.rescue)
   apply (Complex.abs_re_le_norm _).trans; rw [norm_mul]; refine (mul_le_mul h ?_ (norm_nonneg _) ((norm_nonneg _).trans h)).trans p.wax0; exact hf.trans (le_mul_of_one_le_left ((norm_nonneg _).trans hf) one_le_two)
 intro T0 Y0 V₀ D' L _ y0 _ vt vv; let y:= starFeed (Bθ s k) (Pθ s k) r T0 (face_anchors Y0) (radiusB (X s)) L H.beta D'
 let xp:= drip f y; let pp:= pull t b V₀; let mp:= V.material Rc pp
 have hp := p.tiny; have hv: Tiny S₀ V₀ (skyline Xc):=(calmT (w:=hallBill (radiusB Xc)) (by unfold hallBill Sequest; omega) vt vv).raise (Subset.refl _) hp
 have ht:WellDrawn Y s i k α S pp:= ⟨tugTiny V₀ t b hv,tugSmall V₀ t b (drawnT y0 vv)⟩
 let G:= gradientRent Xc; have hg0:0≤ G:=(chip_pos ..).le; have hρ : 0 < H.beta:= ((half_pos p.day).trans_le (Papal.prices_plot Y s i k paid).2.2.2.1.1)
 have hT(i:I) : SU.group.chord (faceValue pp (V.ua i)) ≤ H.p.threshold:= (ht.2 _ (mem_filter.mpr ⟨mem_univ _,U.ship.lives i⟩)).trans (mul_le_of_le_one_left H.p.threshold_pos.le U.near)
 let xq:= 2*Real.sqrt Xc*temp Xc; have hxT: H.p.threshold=temp Xc:= (Papal.prices_plot Y s i k paid).1 ▸ (Y.meter.boot s).1
 have hc: ‖mp‖ ≤ xq:= by
    unfold xq; rw [←hxT]; apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) H.p.threshold_pos.le)).mpr; intro i; change ‖Rc*_‖≤_; rw [norm_mul]; exact mul_le_mul U.mantle ((PiLp.norm_apply_le (p:=2) _ _).trans ((Gauge.curvature_norm ..).trans (hT i))) (norm_nonneg _) (by positivity)
 have hs:0≤ slotError gaugeRules (radiusB Xc) (ageC Xc):=by unfold slotError faceCutError; have hc:=SU.group.colorScale_pos; have hg:=gaugeRules.positive; positivity
 have hwq: ‖mp-xp‖ ≤ G:= by
    apply (pi_norm_le_iff_of_nonneg hg0).mpr; intro i; exact (V.port_cost (Bθ s k) (Pθ s k) Rc t b U.ship gaugeRules vv vt (BProof.coin_pos ..|>.le) p.mask hρ i).trans ((mul_le_mul_of_nonneg_right U.mantle hs).trans p.shine)
 have ht':‖mp‖≤ D:= hc.trans (p.spray.trans' (le_add_of_nonneg_right hg0)); have hl':‖xp‖≤ D := by have h:=norm_sub_norm_le xp mp; rw [norm_sub_rev] at h; have hw:xq+G ≤ D:= p.spray; linarith only [h,hc,hwq,hw]
 let K:=scratch Xc; have h' : x y=xp:= mute_same hd' xp hl'; change |(z*(Φ pp-η)).re - _| ≤ _; unfold Aφ Φ'; rw [h']
 have hU :‖F mp-F xp‖ ≤ K:= (U.cost.price _ hd _ _ ht' hl').trans ((mul_le_mul_of_nonneg_left hwq (show 0≤ ζ*D^m from by positivity)).trans p.eyes)
 have ht: ‖Φ pp-F xp‖ ≤ 2*K:= (norm_sub_le_norm_sub_add_norm_sub (Φ pp) (F mp) (F xp)).trans ((add_le_add (U.scene pp ht) hU).trans_eq (two_mul K).symm)
 apply (hw (Φ pp) _).trans; exact (mul_le_mul h ht (norm_nonneg _) ((norm_nonneg _).trans h)).trans p.wax0
#print axioms Batch.starch
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
