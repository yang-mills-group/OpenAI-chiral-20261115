import YM.SU5.LoomForce.LightWard
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
open Regis.Head Gleam Gleam.Wake Tempest
variable (B:ℕ)(R:ℤ)(x:Site N) {p:BudgetPoint}{K:Scree.Loom N}
local notation "M"=> More N
local notation "φ"=> fling 3 R N
local notation "J"=> Turn B
local notation "Σ"=> Panels B
local notation "ξ"=> node x
local notation "Θ"=> readingFob B R x
variable {h:2*(B+1)<(More N).val}{e:ℝ}{q:ℕ} (z:Checked p K e d a k q)(E:Pattern P T r d a v)
variable (U:Pane N)
local notation "L"=> lapAsset x k B h E
local notation "f"=> fineY B h x E k
local notation "τ"=> Surplus.tax K p x k E
local notation "Τ"=> p.threshold
local notation "μ"=> Spindle.patch B ξ
local notation "ρs"=> untouched (E.A x) k
local notation "Ξ"=> occupancy a v g
-- before ordinary caps and torus path b may vary
abbrev auditTax (R:ℤ)(b:Bool)(A ρ:ℝ)(K:Scree.Loom N)(p:BudgetPoint)(x:Site N)(k:ℕ)(E:Pattern P T r d a v)(U:Pane N) := ((A*ρ^2:ℝ):ℂ)*Surplus.tax K p x k E (if b then fling 3 R N U else U)
def extraDrift (t b α:ℝ):= 2*group.colorScale*α*t * (4*b)
abbrev allErrorMax (V:Rules group)(C:ℝ)(B:ℕ)(t α:ℝ):=let Lq:=4*(B:ℝ)*t; broadError C Lq (rawError V Lq B t α)+ (C*extraDrift t B α *Lq)

lemma price_visa (α:ℝ)(b:Bool) : peeler B b ((Θ).material α U) = α • snapFace B (if b then Surplus.reflected B ξ R U else receiveMark B ξ U 1) :=by
 funext x; cases b
 · unfold snapFace; simp only [↓reduceIte,Bool.false_eq_true,receiveMark, one_smul]; rfl
 simp only [ite_true,peeler,snapFace, Surplus.reflected,Pi.smul_apply,PiLp.smul_apply];
 change _ * (α *_) = α*(_*_:ℝ); rw [mul_left_comm]; rfl

variable (bP: p.B=B)(A G:ℝ)(a0:0≤A)(up:0≤ t)(V:Rules group)
variable (K₀:TankSpot d u)(D:Mantle V B p.threshold u)(Q₀: HopeT d b g 3)
local notation "E'"=> allErrorMax V Ξ B Τ t
include z E h V K₀ Q₀ D bP
lemma carry_on : ‖τ U‖ ≤ broadCash Ξ (4*B*Τ):= inBasket B h V x z E bP K₀ Q₀ D U
include up
lemma hat_spurs (k':pingS Τ (offsetMask B x) (φ U)) (t₁:Tiny (Spindle.patch B ξ) (φ U) t) (t':Tiny ((Spindle.patch B ξ).image (sendSite R)) U t) :
    ‖τ (φ U) - L (Surplus.reflected B ξ R U)‖ ≤ E' := by
 let I:= install B ξ ∘L collectF B ξ h; let T' := receiveMark B ξ (φ U) 1; let V' := Surplus.reflected B ξ R U
 let X:= I T'; let Y:=I V'; let Rq:=4*(B:ℝ)*Τ
 rw [← bP] at k'; obtain ⟨fX,hx,-,-⟩:= permit_trace B h V x z E bP K₀ D (φ U) k'
 have he(i:J):= bounded_reflect R B ξ i U t' up p.threshold_pos.le fX
 have hw := group.colorScale_pos; have hf(z:FrameA B) (v:ℝ)(u:‖z‖≤v) : ‖I z‖ ≤ 4*B*v:= (install_price ..).trans ((collect_price B ξ h z).trans (mul_le_mul_of_nonneg_left u (by positivity)))
 have hU:0 < Τ:= p.threshold_pos
 have hy := hf T' Τ ((pi_norm_le_iff_of_nonneg hU.le).2 fun i=>(he i).2.1); have hu:= hf V' Τ ((pi_norm_le_iff_of_nonneg hU.le).2 fun i=>(he i).1)
 let C:= extraDrift Τ B t; have hr:‖X-Y‖≤ C:=by unfold X Y; rw [←map_sub]; exact (hf _ _ ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=>(he i).2.2)).trans_eq (by unfold C extraDrift; ring)
 let y:=τ (φ U); let Z:=taxpayer x E (k:=k); apply le_trans (norm_sub_le_norm_sub_add_norm_sub y (Z X X) (Z Y Y)); refine add_le_add (paint_it B h V x z E bP K₀ Q₀ D (φ U) up k' t₁) ?_; have hl:= stencil_cost z E x Q₀
 rw [show Z X X - Z Y Y= Z (X-Y) X + Z Y (X-Y) from by simp_rw [map_sub,_root_.sub_apply]; abel]
 have hm(g' h':tangD N)(a b:ℝ)(e:‖g'‖≤a)(f':‖h'‖≤b): ‖Z g' h'‖ ≤ (2:ℝ)⁻¹* Ξ * (a*b):= (aperture_cost x z E Q₀ g' h').trans (by have hp:0≤a:=(norm_nonneg _).trans e; gcongr)
 exact (norm_add_le ..).trans ((add_le_add (hm (X-Y) X C Rq hr hy) (hm Y (X-Y) Rq C hu hr)).trans_eq (by unfold C Rq; ring))
-- input WellDrawn, at horizon. Same footprint S. buys for pair and both singles.
variable (D0:ℕ) (d':D0≥12+B+creditJ+separation (node x) (sendSite R (node x)))
local notation "κx"=> BlockP D0 ξ
local notation "ξX"=> auditTax R
include d' a0
lemma costPad {α:ℝ}(l:α<Τ)(t':Tiny κx U t)(p0:ordinary (possession κx) α U) (q:Bool):
      ‖auditTax R q A G K p x k E U - polynomialPad B h x E k A q ((Θ).material G U)‖ ≤ A*G^2*E':=by
 obtain ⟨v0,v1,p₁,e,p₂⟩:= enterMirror B R x D0 d' U l t' p0 bP
 unfold polynomialPad; rw [price_visa,evaluator_roll]
 let k0: ℝ:= A*G^2; have hk:0≤k0:=mul_nonneg a0 (sq_nonneg G); let V:=if q then Surplus.reflected B ξ R U else receiveMark B ξ U 1
 let T':= τ (if q then φ U else U)
 have ht:‖T'- L V‖ ≤ E':=by
   cases q
   · have hx:= paint_it B h ‹Rules group› x z E bP K₀ Q₀ D U up (bP.symm ▸ p₁) v0
     apply le_trans hx (le_add_of_nonneg_right ?_); unfold extraDrift; have hu:= group.colorScale_pos; have hp:= p.threshold_pos; have hm:=stencil_cost z E x Q₀; positivity
   exact hat_spurs B R x z E U bP up ‹Rules group› K₀ D Q₀ p₂ e v1
 rw [← polynomial]
 have hK(y:ℂ):‖(k0:ℂ)*T'-(k0:ℂ)*y‖=k0*‖T'-y‖:=by rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg hk]
 have hf:= mul_le_mul_of_nonneg_left ht hk
 have hn:(A:ℂ)* (G:ℂ)^2= (k0:ℂ):=by unfold k0; push_cast; rfl
 change ‖(k0:ℂ)*T'-(A:ℂ)*ζPay q (_ * L V)‖ ≤ k0*_
 have hu:star (G:ℂ)=(G:ℂ):= Complex.conj_ofReal _
 cases q
 · unfold ζPay; simp only [Bool.false_eq_true,ite_false]; rw [←mul_assoc,hn,hK]; exact hf
 · unfold ζPay; simp only [ite_true,star_mul',star_pow,hu]; rw [←mul_assoc,hn,hK]; apply le_trans (Eq.le ?_) hf; rw [show T'-star (L V)=star (T'-L V) from (by rw [star_sub, show star T'=T' from tax_real x z E _]) , norm_star] -- T' notation match?
#check @costPad
#print axioms costPad
end YM.CF.LitCurrent.Surplus
