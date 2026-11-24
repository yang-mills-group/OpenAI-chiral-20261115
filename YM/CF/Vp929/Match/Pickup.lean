import YM.CF.Vp929.Match.Rays
import YM.CF.Fixed.Voltage.OffNib
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
namespace MatchW
open Py.Rate Haro Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
open scoped Mew
local notation "Qu"=> Tenant.quota^2
variable (T S:BeatL n) {p:BudgetPoint}{v W e:ℝ}{B:ℕ}{L:Scree.Loom n}
open Technique
variable {T S} (Ω:Technique p W e d B L T S a b c r)
namespace Technique
local notation "Xp"=> Ω.note + Ω.note
local notation "Kr"=> Rinse (Seat n) (Copy n)
local notation "Er"=> ΘS r
local notation "λχ" i:max=> Ω.bond.litB Ω.H Ω.pay W Ω.floor Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize i
local notation "πχ"=> Pair (ΘS r)
local notation "I_"=> Complex.I
variable {Wk f m₁ m₂ u0 Λ ψ δ θ x g γΓ θΓ dΓ vδ r₁ s:ℝ}
local notation "Pk"=> cap1 p (BondL.øK r) W
local notation "VK"=> Vow.Cusp n
local notation "Θp"=> Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ
variable (Th: Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ)
local notation "opV" I:max k:max=> Timer (Cadre.chip (cribR (Ω.note+Ω.note)) I) (Ω.note+Ω.note) r₁ (wu p) wΨ (widthK n p.B) (spanV p.B) γΓ dΓ (spanV p.B*dΓ) dΓ k (Ω.note+Ω.note)
abbrev buzero (r:ℝ)[Nonempty (ΘS r)] :ΘS r:= ⟨0,by rw [norm_zero]; exact (norm_nonneg _).trans (Classical.arbitrary (ΘS r)).property⟩
abbrev rePoint(i:ΘS r):Pair (ΘS r):=(i,buzero r)
local notation "νo" i:max Q:max=> Ω.νpoint (rePoint i) (Q,0)
include Ω
lemma zeros_ : Ω.ler (buzero r)=0 ∧ Ω.lerW (buzero r)=0 ∧ Ω.lerC (buzero r)=0:=by
 have p {X:Type}[AddCommGroup X][Module ℝ X]{T:ΘS r→X}(p:Poetic T): T (buzero r)=0:=by obtain ⟨H,t⟩:=p; exact (t _).symm.trans (map_zero H)
 exact ⟨p Ω.lerQ.1,p Ω.lerQ.2.1,p Ω.lerQ.2.2⟩
lemma κ0 (i:Er)(u:ℂ): Ω.κm (rePoint i) u=Ω.linse i :=by
 change Ω.linse i+u • Ω.linse (buzero r)=_
 have he:Ω.linse (buzero r)=0:= by
    let U:= Ω.linse (buzero r); funext X D Y F j; apply Subtype.ext; change (U X D Y F j).val=0
    rw [(show PictureT p (cipherK B) U (Ω.lerC (buzero r)) from bias_pic p W (cipherK B) _).actsF,Ω.zeros_.2.2]; split; swap; · rfl
    unfold coll_T; split; · change (Pastry.cane (Dwell n)).eval (0*_)=0; rw [zero_mul,map_zero]
    change (Pastry.cane _).eval (0* _)=0; rw [zero_mul,map_zero]
 rw [he,smul_zero,add_zero]
abbrev pivotP (i:Er)(F:VK):= Stax.lamp (P:=p) F (Ω.linse i)
def νoP(i:Er)(F:VK):= Nu p (rebP (Ω.pivotP i F)) (rebP F) (Ω.lyr i)
lemma realP (u:Er)(F:VK): Ω.waveW (rePoint u) (F,0)= (Ω.pivotP u F,0)∧ νo u F=(Ω.νoP u F,0):=by
 have h(v:ℂ): Ω.nuR (rePoint u) F v=Ω.νoP u F:=by unfold nuR νoP chest seekR; rw [κ0,show Ω.lyr (rePoint u).2=0 from (by unfold lyr; rw [show (rePoint u).2=buzero _ from rfl,Ω.zeros_.1,Ω.zeros_.2.1,add_zero]),smul_zero,add_zero]
 have f:Pair.plus (F,0)=F:=by rw [Pair.plus,smul_zero]; exact add_zero ..
 have g:Pair.minus (F,0)=F:=by rw [Pair.minus,smul_zero]; exact sub_zero ..
 constructor
 · unfold waveW chest; rw [f,g,κ0,κ0]; apply Pair.ext_pm <;> simp [Pair.plus_cat,Pair.minus_cat] <;> simp [Pair.plus,Pair.minus,pivotP]
 unfold νpoint; rw [f,g,h,h]; apply Pair.ext_pm <;> simp [Pair.plus_cat,Pair.minus_cat] <;> simp [Pair.plus,Pair.minus]

local notation "Xo" i:max => Ω.bond.uDa Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize
lemma T_realP(i: ΘS r)(F:VK)(T0: RegBudget n)(τ:Ids n): let t:= (Xo F) i T0 τ; Ω.txStar (rePoint i) (F,0) (T0,0) τ=(t,0)∧Ω.rollT (rePoint i) (F,0) (T0,0) τ=(t+Ω.ler i,0):=by
 intro t; have he:p= p:=rfl
 have h:Ω.txStar (rePoint i) (F,0) (T0,0) τ=(t,0):=by
    unfold txStar; rw [(Ω.realP i F).2,show (rePoint i).2=buzero _ from rfl,Ω.zeros_.2.1]; apply Prod.ext
    · change T0+Ω.lerW i+cast_E (Ω.νoP i F) τ=t; unfold νoP; rw [Ω.ler_p i]; rfl
    change 0+0+cast_E (0:Vow.Pax n) τ=0; rw [zero_add,zero_add]; funext X V; exact smul_zero (bassH (Bake.lagE X))
 unfold rollT; rw [h,show (rePoint i).2=buzero _ from rfl,Ω.zeros_.1]; exact ⟨rfl,Prod.ext rfl (zero_add _)⟩

variable {m w:ℝ}{j:ℕ}{M: Male}
open Levier Salt Ione Nacre
structure Hire (p:BudgetPoint)(F:Cusp n)(W:ℝ)(B:ℕ)(Z:RegBudget n)(T: Vow.Cusp n)(f r v w α:ℝ):Prop where
 sale : PreR p F Z T f W r v
 dignity: Cash.poise (rebP F)
 okay:ZealQ F
 money: Billable p W B F w α
omit Ω
omit [Nonempty (ΘS r)] in
lemma Hire.swalk {F:Cusp n}{Z:RegBudget n}{T:Vow.Cusp n}(q:Hire p F W B Z T f r v m₁ m₂)(s:Sweep n)(V:Orbit n)(w:Injective (priorP V.2))(X:Aura n)(D:SO)(u:D⊆ X.val): F (moldA s X) (actY s D) (yellA s V)=suit_Y s (F X D V) :=by
 by_cases d:D.Nonempty; · exact q.okay s V w X D d u
 rw [Finset.not_nonempty_iff_eq_empty.mp d]; rw [show actY s ∅=∅ from Finset.map_empty _]; exact q.dignity.2 s X V

include Ω Th
open BondL
local notation "Π"=> p.supportExponent+1+1
lemma sells (i:ΘS r)(F:Cusp n)(E:RegBudget n)(U0:Cusp n)(hi:Hire p F W B E U0 f m u0 m₁ m₂)(j:ℕ)(pX:1 ≤ j)(M:Male)(X:Finset (Scree.Hub n))(x:Haro.liveB X)(t:∀ T:Scree.Hub n,coverNumber p.B T.val.2 ≤ 1→T∈ X)(H:Lens Wk)(τ:Ids n): let F1:=Ω.pivotP i F; let T1:= (Xo F) i E τ; Cash.poise (Ω.νoP i F)∧ PickY p F1 (T1+Ω.ler i) U0 f W m Λ (r₁⁻¹*ψ) θ wΨ ∧ EdgeC p Ω.H Ω.pay T S F F1 (riseV i):=by
 intro F1 T1; obtain ⟨I,Fc,h,k⟩:= hi.money; let A:= Ω.bond; have hw(s:Sweep n)(X:Aura n)(V:Orbit n)(w:Injective (priorP V.2)) (D: SO)(u:D⊆X.val):F (moldA s X) (actY s D) (yellA s V)=suit_Y s (F X D V):= hi.swalk s V w X D u
 let αk:=Qu*b*r; let βk:=Qu*c*r; let K:= Dq p a (Qu*(b*r)) (Qu*(c*r)) u0 θ vδ W ψ δ r; have he: Pace p a (Qu*(b*r)) (Qu*(c*r)) W r ψ δ m₁ m₂ u0 θ vδ r₁ Wk:=by rw [←mul_assoc, ←mul_assoc]; exact Py.altPulse Th.speed Th.radius.le
 obtain ⟨t₀,-,P,pψ,H0,J,Esk⟩:= go_Open (M:=M) Ω.floor F p Ω.H Ω.pay Ω.pos Ω.raw Th.radius Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.fresh I Fc hi.dignity.1 hw hi.dignity.2 pX Wk H E U0 hi.sale X x t Th.leg Th.lead Ω.tags Ω.piety Ω.bill h k A Ω.economic he i τ
 refine ⟨⟨π_u _ (show Bake.Turf (rebP F1) from Ω.bond.roof_K Ω.H Ω.pay W Ω.floor i F Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize hi.dignity.1) hi.dignity.1,?_⟩, ?_, Esk⟩
 · have hv:0 ≤ ρL p:=by unfold ρL wΨ; linarith [p.exponent_pos]
   have hu:ρL p ≤ wu p:= by unfold ρL wu wΨ; linarith
   have hp:0 < wΨ:=by norm_num [wΨ]
   obtain ⟨m,V,V',-⟩:= Ω.bond.glyph_v Ω.H Ω.pay W Ω.floor i F Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Fc t₀ hv hp (by unfold ρL wΨ wu; linarith) wΨ m₁ vδ θ hp le_rfl (fun x=> (tall_m _ (fun i=> (Fc i _ (empty_subset _)).merit.wage (zero_le_one.trans Ω.floor)) hu x).trans (h x)) Th.lead he.ht he.earn he.wings
   obtain ⟨_,_,qe,_,g,-⟩:= J.price; let ty:= Ω.rollH Th i; exact veil_Ψ (Ω.lyr i) m Ω.floor V V' g hi.dignity.2 (Ione.addT p ty.2 ty.1)
 have he:K ≤ Λ:=by unfold K; rw [←mul_assoc,←mul_assoc]; exact Th.dust;
 let u':= Fixed.Voltage.upgradeI p Utrue J.foot he; exact ⟨u',⟨u',J.post.sell⟩,J.price⟩
end Technique
end MatchW
end YM.CF.Sour
