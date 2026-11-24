import YM.CF.Song.Jags
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Haro Ione BondL Larch Glyph
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
local notation "F0"=> body_Q
abbrev wΨ:ℝ:=1/4
abbrev wu(P:BudgetPoint):ℝ:=P.supportExponent+1+1+1
abbrev feeΨ(P:BudgetPoint)(a b c W:ℝ):ℝ:=(P.order+1:ℝ)*W^2*aimV P.B a (wu P+2)*(5*b+c)
abbrev rentΦ(P:BudgetPoint)(γ d:ℝ):ℝ:=spanV P.B*d*γ+spanV P.B*wΨ⁻¹*γ*d
open Push.AbsoluteSums Trees Ursell
abbrev tintK(P:BudgetPoint)(φ θ s:ℝ):ℝ:=Nor.reserveT P.power P.order P.B 1*(uk_b φ s θ (degreePrice P.B θ wΨ))
abbrev tiltB(W:ℝ)(P:BudgetPoint):ℝ:= W*4^P.power*(2^P.power*16)
abbrev φcape(P:BudgetPoint)(a b c W:ℝ):ℝ:= Glyph.cap2 P c W a+Glyph.cap2 P b 1 a
structure Pace (P:BudgetPoint)(a b c W r γ d S v α θ z ζ Wk:ℝ) :Prop where
 ny: 2* P.supportExponent*Fief.tileN 1≤ a/2*P.B
 nf: 2*(wu P+2)*Fief.tileN 1≤ a/2/2*P.B
 zen:0 ≤d
 fee: feeΨ P a b c W ≤ d
 star: S+ζ*v < γ
 lean:0 ≤ γ
 tap:spanV P.B*γ≤1
 endP: spanV P.B*d≤ wΨ
 car:d+spanV P.B*d*γ-(wΨ-spanV P.B*d)*γ < 0
 wings:S+γ+z*(d+rentΦ P γ d) ≤ θ
 ht:0<θ
 earn: degreePrice P.B θ wΨ<1
 sale:tiltB Wk P*(α+φcape P a b c W+tintK P (rentΦ P γ d) θ z) / W^2 ≤ r
variable {R0 W:ℝ}(W0:1≤W){N:Side}{T S:BeatL N}(F:Vow.Cusp N) (p:BudgetPoint) {a b c d e z t:ℝ}{q:ℕ}{L:Scree.Loom N}(g:Roof N t e q L)(he:0< e)
local notation "Zh"=> body_Q (N:=N) R0
structure EdgeC (T S:BeatL N)(F B:Cusp N)(Z:Op SU.Slot):Prop where
 body (x: Orbit N)(pX:FleetS p.threshold x.1)(X Y:Op (Single N))(v:Scree.Phys N)(hx:IsStarProjection X)(q:Thera.TagG X Y)(z:Sea X v)(t:T (roller he g x).val=X)(u:S (roller he g x).val=Y): let O:=flags p.threshold x.1; let P:= nursery X hx; let W:=acts (exp (dg Y)) v
            acts (P.cook (hGas O (hailV O B x))) W=scaleZ Z (acts (P.cook (hGas O (hailV O F x))) W)
variable (htA:0 < a)(h1:a≤1)(hk:0<R0){z0 z1:ℝ}(k:HopeT e z0 z1 p.order)(hv:p.threshold ≤ z1)(hx:p.threshold ≤ t)(hQ:q+10 ≤ p.B)(hq:cipherK q≤ 5*p.B)(hB:3≤p.B)(hv1:1≤p.power)
variable (I:blazeK N)(f:∀ X:Aura N,∀ D⊆X.val,Fray p W (cipherK q) X D (F X D) (I X D))(r:Bake.Turf (fun X=>F X ∅))
open Levier Salt Ione Nacre
variable (pS: ∀ s:Sweep N,∀ i:Aura N,∀ V:Orbit N,Injective (priorP V.2)→∀ D⊆i.val,F (moldA s i) (actY s D) (yellA s V)=suit_Y s (F i D V))
variable (Ω₁: Sym_a (fun X=>F X ∅))
variable {M:Male}{j:ℕ}(u:1 ≤j)(Wk:ℝ)(hW:Lens Wk)(U0:RegBudget N)(X0:Vow.Cusp N){u0 v0 α θ σ δ γ ζ:ℝ}(tp: PreR p F U0 X0 u0 W v0 α)
variable (T_:Finset (Scree.Hub N))(hw:liveB T_)(pB:∀ T:Scree.Hub N,coverNumber p.B T.val.2 ≤1 → T∈T_)
variable (eK:1 ≤ ζ)(h_z: 0 < z)(ht_T:TagT T S (body_Q (N:=N) R0) e)(Fp:Piety N T S (body_Q (N:=N) R0) a R0 b c e)
local notation "b₁"=> Tenant.quota^2*b
local notation "c₁"=> Tenant.quota^2*c
abbrev η₁:= wingRent (Fir.Aop-(1/2:ℂ) • 1) 1
abbrev ρL:= p.supportExponent+1+1+wΨ
abbrev Dq(P:BudgetPoint)(a b c α θ z W γ d R0:ℝ):ℝ:=α+φcape P a b c W+tintK P (rentΦ P γ d) θ z+Glyph.cap1 P (øK R0) W
variable (hr:η₁*R0≤ b)(Ω₂:∀ i:Seat N,tallB (urnL I) p.B (wu p) i≤σ)(Ω₃:∀ i:Seat N,tallB (Vow.hymn I) p.B (wu p) i ≤ δ)
include W0 he g htA hk h1 k hv hx hQ hq hB f r pS Ω₁ u hW hw pB tp ht_T hv1 Ω₂ Ω₃ h_z eK Fp hr
lemma goX (D:Pace p a (b₁) (c₁) W R0 γ d σ δ α θ z ζ Wk):∃ (i:ΘS R0)(E:RegBudget N)(G:Cusp N), BondL.Picket p G E X0 T_ M j u0 W v0 (Dq p a (b₁) (c₁) α θ z W γ d R0) (ζ⁻¹*γ) θ wΨ ∧ EdgeC p g he T S F G (riseV i):=by
 let z00:ΘS R0:=⟨0,by rw [norm_zero]; exact hk.le⟩; haveI : Nonempty (ΘS R0):=⟨z00⟩
 obtain ⟨l⟩:= renderX _ _ _ Fp; obtain ⟨A,QA⟩:=ember l ht_T (continuous_subtype_val.comp continuous_subtype_val) (fun z=>z.val.property) hk.le (fun z=>z.property) h1 hr
 let Θi:=A.bead W p; have hb:0 ≤ Θi:=((A.litB g he W W0 k hv hx hQ hq hB z00).buys hB (zero_le_one.trans W0)).dice; have hu:0 ≤ spanV p.B:=Nat.cast_nonneg _ -- tune
 have hL:0 ≤ wu p-wΨ*1:=by unfold wu wΨ; linarith [p.exponent_pos]
 have hB1(o:Seat N):nook (Θi*loom_v (wu p+2) 0 (widthK N p.B) 0) o≤d:= (A.duty W p (wu p+2) htA (by unfold wu; linarith [p.exponent_pos]) D.nf o).trans D.fee -- shadow problem
 have hi(X:Aura N)(D:Support (More N))(p':D⊆ X.val):0 ≤ I X D:= (f _ _ p').merit.wage (zero_le_one.trans W0)
 have hg(o: Seat N):nook (roofL I ζ * loom_v (wu p) wΨ (widthK N p.B) 0) o < γ:=by rw [←parse,mul_zero,sub_zero,age_t]; exact lt_of_le_of_lt (add_le_add (Ω₂ o) (mul_le_mul_of_nonneg_left (Ω₃ _) (zero_le_one.trans eK))) D.star
 have op:= Cadre.stallK ζ eK (wu p) wΨ (widthK N p.B) (vigor ..) γ d (show 0 ≤ wΨ by norm_num [wΨ]) Θi I hi hb hB1 D.zen hu D.lean D.tap D.endP hg hL D.car -- tune
 have hp:0 < wΨ:=by norm_num [wΨ]
 have ht:0≤ ρL p:= by unfold ρL wΨ; linarith [p.exponent_pos]
 have pf:ρL p+wΨ≤ wu p-wΨ*1:=by unfold ρL wΨ wu; linarith
 obtain ⟨i,E,SQ⟩:= A.keep_K g he W W0 F k hv hx hQ hq (by assumption) f r pS op ht hp pf R0 QA wΨ σ z θ hp le_rfl (fun i=> (tall_m _ (fun i=> hi _ _ (empty_subset _)) (show ρL p ≤ wu p from (by unfold wu ρL wΨ; linarith)) i).trans (Ω₂ _)) h_z D.ht D.earn D.wings htA D.ny h1 Ω₁ hw pB M u Wk hW U0 X0 tp hk hv1 (by apply le_trans (le_of_eq ?_) D.sale; unfold tiltB tintK φcape rentΦ; ring)
 refine ⟨i,E,_,SQ,⟨fun x hxX X Y v hy pX z t b => startP A g he W W0 x i F k hv hx hQ hq ‹_› f r pS op ht hp pf X Y v hy pX z ht_T hxX t b⟩⟩ -- ‹_› threshold confusion
end YM.CF.Sour
