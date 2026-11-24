import YM.SU5.LoomForce.MirrorLedger
import YM.SU5.WindTorque.Turbine
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Spindle
open Buffered Pannier Pannier.Chancel Rous Afterglow
open Py Py.Rate Py.Rate.LocalLimit Preparation Preparation.Yoke
open Afterglow.Tower.VacuumSelection.Spine
open Gleam Gleam.Wake Regis.Head Regis.Wake Tempest
variable (B:ℕ) (R:ℤ) (x:Site N){p:BudgetPoint}{K:Scree.Loom N}
local notation "ξ"=>node x
local notation "τ"=> Surplus.tax
local notation "I"=> Panels B
local notation "φ"=> fling 3 R N
variable {e:ℝ}{q:ℕ} (z:Checked p K e d a k q)(E:Pattern P T r d a v)
variable {D:ℕ}(y: D≥ 12+B+creditJ+separation (node x) (sendSite R (node x)))
local notation "Aκ"=> creditJ
local notation "Z"=> BlockP D ξ
variable (A G:ℝ)(a0:0≤A) (h:2*(B+1)<(More N).val)(WT : TankSpot d u) (V : Rules group)(S: Mantle V B p.threshold u) (L: HopeT d b g 3) (bρ:p.B=B)
local notation "Uκ"=> auditTax R
local notation "C"=> A*G^2
local notation "Τ"=>p.threshold

abbrev mark (b:Bool) (K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(R:ℤ)(E:Pattern P T r d a v)(A G:ℝ)(x:Site N): Mark N:=fun V=>auditTax R b A G K p x k E V.1 • 1
local notation "Ξ" b':max=> mark b' K p k R E A G x
include z y bρ
lemma genuineStamp(b:Bool) : AtSupport false Z (Ξ b) ∧ covariant (Ξ b) := by
 let F:=Ξ false; let G':=gaugeSeed K p k x E
 obtain ⟨p₁,p₂⟩:=zones B R x D y bρ
 have ht:F=(↑C:ℂ) • G':=funext fun i=> (mul_smul _ _ _)
 have hp':AtSupport false (inspectFoot p x) F:= ht ▸ (gauge_support K p k x E z).smulM _
 have hp :covariant F:= by
   intro g i; change auditTax R false A G K p x k E _ • 1= _; unfold auditTax; simp only [Bool.false_eq_true,↓reduceIte]; change ( (↑C :ℂ)*τ K p x k E (Lattice.gauge _ i.1)) • 1= twist _ (( (↑C :ℂ)*τ K p x k E i.1) • 1); rw [tax_invariant x z E,twist_scalar,map_one]
 have hf:Ξ true = reflMark 3 R (Ξ false):=by funext V; unfold reflMark mark auditTax; rw [theta_smul,theta_one,star_mul']; congr 1; rw [show star (↑C :ℂ) = (C:ℝ) from Complex.conj_ofReal _,tax_real x z]; rfl
 cases b
 · exact ⟨hp'.mono p₁,hp⟩
 rw [hf]; refine ⟨(hp'.refl 3 R).mono ?_, covariant_reflected hp' hp R 3⟩; refine le_trans (le_of_eq ?_) p₂; unfold inspectFoot; congr!
 unfold Shape.anon haul slipV; rw [mul_smul]; rfl

omit y bρ in
lemma drinks (b:Bool) : GaugeInvariant (auditTax R b A G K p x k E):=by
 intro g U; unfold auditTax; refine congrArg _ ?_; cases b; exact tax_invariant x z E g U
 rw [tilt_rule]; simp only [ite_true]; rw [Push.Local.pull_gauge]; exact tax_invariant x z E _ _

omit bρ y in
lemma stencilPay (b:Bool) : Measurable (Uκ b A G K p x k E) := by
 have ht:Measurable (τ K p x k E):= (continuous_id.matrix_trace).measurable.comp (enve_pass x (E.A x) z (E.moorA x)).meas
 cases b; exact measurable_const.mul ht; exact measurable_const.mul (ht.comp ((fling_cont ..).measurable))

local notation "ℓ"=> occupancy a v g
abbrev age (T:ℝ)(B:ℕ)(u:ℝ):= broadCash T (4*B*u)
include a0 WT V S L h
omit y in
lemma stamp_cost (V':Pane N)(j:Bool): ‖auditTax R j A G K p x k E V'‖ ≤ C*age ℓ B Τ:=by
 unfold auditTax; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg a0 (sq_nonneg G))]; exact mul_le_mul_of_nonneg_left (inBasket B h V x z E bρ WT L S _) (mul_nonneg a0 (sq_nonneg G))
#check @genuineStamp
#check @drinks
#check @stamp_cost
#print axioms genuineStamp
end YM.CF.LitCurrent.Surplus
set_option quotPrecheck false
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
open Next.Rank Spindle
open Buffered Pannier Pannier.Chancel Rous Afterglow
open Py Py.Rate Py.Rate.LocalLimit Preparation Preparation.Yoke
open Afterglow.Tower.VacuumSelection.Spine Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Gleam Gleam.Wake Regis.Head Regis.Wake Tempest
-- oops closes earlier opens header; insert header
variable {P:Preparation}{j:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus j))(s i n:ℕ)
local notation "N"=> Journey.side Y i s
local notation "p"=> (RootBook Y i n s).p
local notation "K"=> (Y.voyage i).CapeT s
variable (B D:ℕ)(R:ℤ)(x:Site (Journey.side Y i s))
-- later uses only p set, B and z etc
variable {T T':SOp (Journey.side Y i s)}{r k q:ℕ}{d a b v u g e:ℝ}
  (z:Checked (RootBook Y i n s).p ((Y.voyage i).CapeT s) e d a k q)
  (E:Pattern T T' r d a v)
  (A I G:ℝ)(a0:0≤A)
  (h:2*(B+1)<(More (Journey.side Y i s)).val)
  (L:TankSpot d u)(V:Rules group)
  (S:Mantle V B (RootBook Y i n s).p.threshold u)(Q: HopeT d b g 3)
variable (bw:(RootBook Y i n s).p.B=B)
   (hk:B=Pressure.radiusB (Vale.hat P.R.L P.x s))
   (y:D≥12+B+creditJ+separation (node x) (sendSite R (node x)))
local notation "φ"=> readingFob B R x
local notation "τ"=> (Surplus.auditTax R)
local notation "Xb"=> (Vale.hat P.R.L P.x s)
local notation "κ"=> sPow P s I
local notation "Q₀" t:max=> mark t K p k R E A G x
open Jewel Lamour.Bridge Celeste Clock Hookah Afterglow.Tapestry Cliplet WakeInvestment Pressure Worth Worth.Pays
-- Costs selects as in heights w late. use to reach seat estimates on common Wick probe F.
#check @landQ
local notation "W" b:max=> landQ N (Q₀ b) (node x) D

variable (hb:creditJ≤B) (v0: |G| ≤ 2*bornQ P s)
  (hd:(2*(D:ℝ)+1)^4≤ sPow P s I) (gV:(↑(Fintype.card (Panels B)):ℝ)≤ sPow P s I)
  (D1:ℝ)(ct: charges B (node x) h (untouched (E.A x) k) ≤ D1)

local notation "Z"=> BlockP D (node x)
local notation "sK"=> sPow P s I
local notation "Sκ"=> A*G^2
local notation "Ακ"=> A*(2*D1)
-- general receipt takes any polynomial of ≤4-order and verifies genuine Mark ratio.
variable {F:(Panels B→ℝ)→ℂ} {U:Pane (Journey.side Y i s)→ℂ}
    (hp:Paint F 4 (sPow P s I))
include hb hk y hd gV hp v0
lemma singlesky (t:GaugeInvariant U)(u:Measurable U)(g:∀ x, ‖U x‖≤ κ)(M:Mark N)
    (h:∀ x:Fields N,M x=U x.1 • 1)(S:AtSupport false (BlockP D (node x)) M)
    (q: covariant M)(hq:∀ X:Pane N, WellDrawn Y s i n (1/2) (BlockP D (node x)) X→ ‖U X-F ((φ).material G X)‖≤ scratch Xb) : Broom Y s i n φ I (1/2) G (2*D) 0 4 (landQ N M (node x) D) F :=by
 refine ⟨S,q,fun x=>?_,fun i=>blocks_rest _ _ _,le_trans (b:=(2*(D:ℝ)+1)^4) ?_ hd ,le_trans (b:=(2*(D:ℝ)+1)^4) ?_ hd,U, ⟨hk ▸ teacup B R x D y hb,hp,gV,(by norm_num),v0,⟨u,κ,g⟩,t,g,hq⟩,?_⟩
 · rw [show (landQ N M _ _).x=M from rfl,h]; refine ((Cadre.unit (s:=_)).scale (U x.1)).buy le_rfl (by simpa using g x.1)
 · push_cast; have h':0≤ (D:ℝ) := Nat.cast_nonneg _; linarith only [le_self_pow₀ (by linarith : 1 ≤ 2*(D:ℝ)+1) (by decide : (4:ℕ)≠0)] -- goal 0≤ /_
 · exact_mod_cast (show (BlockP D (node x)).card ≤ (2*D+1)^4 from by simpa [BlockP,two_mul] using Corona.halo_size {node x} D)
 intro x t; rw [show (landQ N _ _ _).x=M from rfl,h,noble_linear,map_smul]; rw [←noble_linear,noble_unit,smul_eq_mul,mul_one]; simp only [sub_self,norm_zero]; apply WakeInvestment.chip_pos ..|>.le -- `scratch`
#check @singlesky
#check @Broom

local notation "Π[" i "]" => polynomialPad B h x E k A i
local notation "ν"=> Broom Y s i n φ I (1/2) G (2*D) 0 4
structure ManageBud (C err tilt T s:ℝ): Prop where
   cost : C ≤ s
   ticket : C^2 ≤ s
   error : err ≤ T
   both : 2*C*err+err^2 ≤ T
   hue : tilt ≤ s
   dark : tilt*tilt + tilt*tilt ≤ s
local notation "ℓc"=>occupancy a v g
local notation "Νβ" => Sκ*age ℓc B (p).threshold
local notation "Ββ" => Sκ*allErrorMax V ℓc B (p).threshold (skyline Xb)

include z a0 h V L S Q ct bw
omit hp
lemma both_assets (t: ManageBud (Νβ) (Ββ) (Ακ) (scratch Xb) κ):
    (∀ j,ν (W j) (Π[j])) ∧ ν (landQ N ((Q₀ true)*(Q₀ false)) (node x) D) (fun X=> (Π[true]) X*(Π[false]) X) := by
 let F := φ; let H(j:Bool):=τ j A G K p x k E
 let G'(j:Bool):=Π[j]
 let X(j:Bool):= Q₀ j
 have h0(j):= genuineStamp B R x z E y A G bw j
 have hg(j): GaugeInvariant (H j):= drinks R x z E A G j
 have ht(j): Measurable (H j) := stencilPay R x z E A G j
 let μ:=Νβ; let vx:= Ββ
 have hm(j:Bool)(U:Pane N): ‖H j U‖≤μ:= stamp_cost B R x z E A G a0 h L V S Q bw U j
 have hy(j:Bool):Paint (G' j) 2 Ακ:= enforce B h x E k A D1 a0 j ct
 have he(j)(U: Pane N)(hp:WellDrawn Y s i n (1/2) Z U): ‖H j U- G' j ((F).material G U)‖ ≤ vx := costPad B R x z E U bw A G a0 (WakeInvestment.chip_pos ..).le V L S Q D y (by have hs:= (p).threshold_pos; linarith : 1/2*(p).threshold < (p).threshold) hp.1 hp.2 j -- tune greek
 refine ⟨fun j=> ?_,?_⟩
 · exact singlesky Y s i n B D R x I G hk y hb v0 hd gV (meterInc (hy j) (by norm_num) t.hue) (hg j) (ht j) (fun x=>(hm j x).trans t.cost) _ (fun _=> rfl) (h0 j).1 (h0 j).2 (fun x h=>(he j x h).trans t.error)
 have hQ:0≤ μ:=(norm_nonneg (H false 1)).trans (hm false 1)
 refine singlesky Y s i n B D R x I G hk y hb v0 hd gV (meterInc (meterMul (hy true) (hy false)) le_rfl t.dark) (U:=(H true*H false)) (fun g u=>congrArg₂ (·*·) (hg true g u) (hg false g u)) ((ht true).mul (ht false)) ?_ _ ?_ ((h0 true).1.mulM (h0 false).1) ?_ ?_
 · intro x; rw [Pi.mul_apply,norm_mul]
   exact (mul_le_mul (hm _ _) (hm _ _) (norm_nonneg _) hQ).trans ((pow_two μ) ▸ t.ticket)
 · intro x'; simp only [mark,Pi.mul_apply, smul_mul_smul_comm,one_mul]; rfl
 · intro g U; simp only [Pi.mul_apply,map_mul]; exact congrArg₂ (·*·) ((h0 true).2 g U) ((h0 false).2 g U)
 intro U hx; let A':=F.material G U; let f:=H false U; let g:= H true U; let k:=G' true A'; let s:=G' false A'
 have hk': ‖g-k‖ ≤ vx:=he _ U hx; have hc:0≤ vx:=(norm_nonneg _).trans hk'; have ha:= (norm_nonneg k); have hs: ‖f-s‖ ≤ vx:=he _ U hx
 change ‖g*f-k*s‖ ≤_; rw [show g*f-k*s=g*(f-s)+(g-k)*f-(g-k)*(f-s) by ring]
 apply le_trans _ t.both; refine (norm_sub_le ..).trans ((add_le_add (b:=μ*vx+vx*μ) ((norm_add_le ..).trans ?_) (d:=vx*vx) ?_).trans_eq ?_)
 rw [norm_mul g (f-s),norm_mul (g-k) f]; exact add_le_add (mul_le_mul (hm true U) hs (norm_nonneg _) hQ) (mul_le_mul hk' (hm false U) (norm_nonneg _) hc)
 rw [norm_mul (g-k) (f-s)]; exact mul_le_mul hk' hs (norm_nonneg _) hc
 change μ * vx+ vx*μ+vx*vx = 2*μ*vx+vx^2; ring
#print axioms both_assets
end YM.CF.LitCurrent.Surplus
