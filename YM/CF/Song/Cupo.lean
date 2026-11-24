import YM.CF.Song.Pads
import YM.CF.Song.Agape
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
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
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {N:Side} (T S:BeatL N)(E:χL N κ)
local notation "Sta"=> fC N S E
local notation "Bel"=> κR N E
local notation "Q"=> tickA N
local notation "Lx"=> Firing N
namespace BondL
variable {a b c d e s:ℝ}{T S E}(A: BondL T S E b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
variable (s_:Sweep N)(V:Orbit N)(i:κ)(Z:Aura N)(pF:Injective (priorP V.2))
open Levier Salt Ione
local notation "Λ"=> sauce s_.charge (detX s_.s) (γS s_)
local notation "OA"=> σX p Z ∅
local notation "WZ"=> yellA s_ V
local notation "Px"=> p.B
local notation "Sg"=> Support (More N)
local notation "Ut"=> (moldA s_ Z)
open Cadre Wray Larch Ione
variable {H p0:ℝ}{I: Aura N→ Support (More N)→ ℝ}(F:Vow.Cusp N)
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤5*p.B)(w:3≤p.B)
variable (f:∀ X:Aura N,∀ D⊆X.val,Fray p W (cipherK q) X D (F X D) (I X D))(r:Bake.Turf (fun X=>F X ∅))
variable (pS: ∀ s:Sweep N,∀ i:Aura N,∀ V:Orbit N,Injective (priorP V.2)→∀ D⊆i.val,F (moldA s i) (actY s D) (yellA s V)=suit_Y s (F i D V))
local notation "τx"=> A.bead W p
local notation "L'"=> (fun i:κ=> litB A g h W w0 k hv y hx v w i)
variable {z u μ ℓ α β ε K0 M1 J:ℝ}{l:ℕ} (op:Timer (Cadre.chip (cribR (A.bead W p)) I) (A.bead W p) z u μ (widthK N p.B) (spanV p.B) M1 J ε K0 1 (A.bead W p))(ht:0 ≤ ℓ)(hp:0 < α)(pf:ℓ+α≤ u-μ*1)
local notation "νL"=> pivotS A g h W F w0 hv y hx v w k
local notation "N'"=> Cadre.chip (cribR τx) I
local notation "N₁"=> nutL (cribR τx) I
local notation "φW"=> (ε*M1+spanV p.B*α⁻¹*M1*J)
local notation "κK"=> (A.litB g h W w0 k hv y hx v w i)
variable (K:ℝ)(U:Sour.pureB A K)
open Push.AbsoluteSums Haro Glyph Trees
local notation "G0"=> fun X:Aura N=>F X ∅
local notation "P'"=> (p.supportExponent+1+1)
variable (δ σ s φ' :ℝ)(d0:0<δ)(vφ:p.supportExponent+1+1+δ≤ℓ)(hv_:∀ i:Seat N,tallB (urnL I) p.B (p.supportExponent+1+1+δ) i ≤ σ) -- quote notation? include parameters. preserve compiler.
variable (hx_:0<s)(hQ:0 < φ')(hu:degreePrice p.B φ' δ<1)(pt:σ+M1+s*(K0+(ε*M1+spanV p.B*α⁻¹*M1*J)) ≤ φ')
open Ursell
local notation "Vx"=> (Sco I (A.bead W p))
local notation "Vℓ"=> (ScoL I (A.bead W p))
local notation "A0"=> (urnL I+urnL (Sco I (A.bead W p))+s • ((A.bead W p) +urnL (ScoL I (A.bead W p))))
local notation "qB"=> degreePrice p.B φ' δ
local notation "F'" => (fun X:Aura N=>νL i X ∅)
local notation "RΨ"=> (Φψ A g h W F w0 hv y hx v w k i)
include w0 g h k hv y hx v w op ht hp pf f d0 vφ hv_ hx_ hQ hu pt
lemma glyph_v : Ready stern p.B A0 (p.supportExponent+1+1) φ' δ (degreePrice p.B φ' δ) ∧ (∀ X:Aura N, Medal p X.val ∅ ((F') X) W (A0 X)) ∧(∀ X:Aura N,Medal p X.val ∅ ((G0) X) W (A0 X)) ∧(∀ X:Aura N,Medal p X.val ∅ ((F') X-(G0) X) W (s⁻¹*A0 X)) ∧ (∀ X:Aura N, Medal p X.val ∅ (RΨ X) W (Vℓ X ∅))∧(∀ i:Seat N,tallB (Vow.hymn Vx) p.B P' i ≤ z⁻¹*M1)∧∀ i:Seat N,tallB (urnL Vℓ) p.B P' i≤ φW:=by
 obtain ⟨x,w',u'⟩:=worth_K A g h W w0 i F k hv y hx v w f op ht hp pf; let H:=zero_le_one.trans w0; have hu(x): 0≤ (A.bead W p) x:=op.mid x -- hu shadow
 have hf(i:Aura N)(D:Support (More N))(r:D⊆i.val):0≤ Vx i D:= (x i D r).1.merit.wage H
 have hv₁(i:Aura N)(D:Support (More N))(r:D⊆i.val):0≤ Vℓ i D:= (x i D r).2.merit.wage H
 have h2(i):0 ≤ (A.bead W p) i+ urnL Vℓ i:= add_nonneg (hu i) (hv₁ i _ (empty_subset _)); have h3(i):0 ≤ I i ∅:= (f i _ (empty_subset _)).merit.wage H; have h4(i):0 ≤ s*((A.bead W p) i+urnL Vℓ i):= mul_nonneg hx_.le (h2 i); have ht(i): Vx i ∅≤ A0 i:= le_trans (le_add_of_nonneg_left (a:=Vx i ∅) (h3 i)) (le_add_of_nonneg_right (h4 i)) -- param b tune
 have hL: 0 < z:= zero_lt_one.trans_le op.slope -- notation heart issue
 have h1(o:Seat N):tallB (urnL Vx) p.B (P'+δ) o≤ M1 ∧ tallB (Vow.hymn Vx) p.B P' o≤ z⁻¹*M1 ∧ tallB (urnL Vℓ) p.B (P'+δ) o≤φW:=by
    obtain ⟨a,b⟩:=lam_H (b:=M1) Vx o z p.B (u-μ*1) hL hf (by rw [parse]; exact w' o); have hc:tallB (roofL Vℓ z) p.B ℓ o≤ φW:=by nth_rw 1 [show ℓ=ℓ-0*1 from by ring]; rw [parse]; exact u' o
    have hh':P'+δ≤ u-μ*1:= vφ.trans ((le_add_of_nonneg_right hp.le).trans pf)
    exact ⟨(tall_m _ (fun i=>hf i _ (empty_subset _)) hh' o).trans a,(tall_m _ (fun i=>sum_nonneg (fun j u=>hf _ _ (mem_filter.mp u).2.2)) ((le_add_of_nonneg_right d0.le).trans hh') o).trans b,(tall_m _ (fun i=> hv₁ i _ (empty_subset _)) vφ o).trans (lam_H Vℓ o z p.B _ hL hv₁ hc).1⟩
 refine ⟨ready_T (P:=p) hQ d0 (by assumption) (fun i=> (hf _ _ (empty_subset _)).trans (ht i)) ?_,fun i=> (x _ _ (empty_subset _)).1.merit.big (ht i),fun i=>(f _ _ (empty_subset _)).merit.big ((le_add_of_nonneg_right (hf i _ (empty_subset _))).trans (le_add_of_nonneg_right (h4 i))), ?_,fun i=> (x _ _ (empty_subset _)).2.merit,fun i=> (h1 i).2.1,fun i=> (tall_m _ (fun j=> hv₁ j _ (empty_subset _)) (le_add_of_nonneg_right d0.le) i).trans (h1 i).2.2⟩
 · intro i; rw [tall_add,tall_add,tall_s,tall_add]; refine le_trans (add_le_add (add_le_add (hv_ i) (h1 i).1) (mul_le_mul_of_nonneg_left (add_le_add (show tallB (A.bead W p) p.B (P'+δ) i ≤ K0 from ?_) (h1 i).2.2) hx_.le)) pt
   exact (tall_m _ op.mid (show P'+δ ≤ u-μ*0 by have he:=op.hop; linarith only [pf,hp,vφ,he]) _).trans (by rw [parse]; exact op.birth _)
 intro X; have hz:νL i X ∅-F X ∅=Stax.birthL (L' i).payX X ∅+ RΨ X:= by unfold pivotS Stax.lamp; change F X ∅+_+RΨ X-F X ∅=_; abel
 rw [hz]; have hv'':=Stax.aptL F I f ((L' i).payX) τx ((L' i).buys w H) w0 X _ (empty_subset _); refine (hv''.merit.plus (x X _ (empty_subset _)).2.merit).big ?_; unfold δWeight; rw [if_pos rfl, le_inv_mul_iff₀ hx_]; exact le_add_of_nonneg_left (add_nonneg (h3 X) (hf X _ (empty_subset _)))
variable (he0:0 < a)(fα: 2*p.supportExponent*Fief.tileN 1 ≤ a/2*p.B)(e': a ≤1)(Ω₁:Sym_a (fun X=>F X ∅))
variable (τ:Ids N)
local notation "T'"=> A.seekB (p:=p) g h i
local notation "E'"=> cast_E (Nu p (F') (G0) T') τ
local notation "Dt"=> (Nor.reserveT p.power p.order p.B 1*(uk_b φW s φ' qB))
include he0 fα e' Ω₁ r pS U
lemma lensK : IncX Utrue E' p W Dt ∧ ∀ V:Orbit N,coldE p (FeeD p (F')) V= coldE p (FeeD p (G0)) V+exponentL p T' V.1+ exponentL p E' V.1:=by
 obtain ⟨aK,pv,t,hP,kh,vS,vK⟩:=glyph_v A g h W w0 i F k hv y hx v w f op ht hp pf δ σ s φ' d0 vφ hv_ hx_ hQ hu pt; obtain ⟨pk,he,x⟩:=A.coin_I g h W w0 i F k hv y hx v w f r pS op ht hp pf K U he0 fα e'
 have hq:=Ione.addT p pk he; rw [←add_assoc] at hq; have hx':= A.spark g h W w0 i F k hv y hx v w f r pS op ht hp pf; have ht':= A.roof_K g h W w0 i F k hv y hx v w r; have he':= (A.jointW g h W w0 i F k hv y hx v w f r pS op ht hp pf K U).reb
 refine ⟨globe_u _ _ hx_ aK w0 pv t hP kh he' hx' Ω₁ hq ht' r τ vK,fun V=>?_⟩ -- tune
 exact circa _ _ hx_ aK w0 pv t hP kh he' hx' Ω₁ hq ht' r τ V
lemma sweet_t(X:Scree.Hub N)(V:Pane N):Continuous fun i:κ=> cast_E (Nu p (fun X=>νL i X ∅) (G0) (A.seekB (p:=p) g h i)) τ X V:=by
 let Y(i:κ):=(fun X=>νL i X ∅); let l(k':κ):= Nu p (Y k') (G0) (A.seekB (p:=p) g h k'); let ht'(i:κ):= glyph_v A g h W w0 i F k hv y hx v w f op ht hp pf δ σ s φ' d0 vφ hv_ hx_ hQ hu pt; have hb(Z:Aura N): Continuous fun i:κ=> l i Z (V,τ):=by
    unfold l Nu zenS; split; swap; exact continuous_const
    let x:Orbit N:=(V,τ)
    let B:= fee_C Y x Z (fun j=> A.auraT g h W w0 x _ F k hv y hx v w f op ht hp pf _ (empty_subset _)) w0 _ (ht' (Classical.arbitrary _)).1 (fun i=> (ht' i).2.1) (add_nonneg (add_nonneg p.exponent_pos.le zero_le_one) zero_le_one); exact (B.sub continuous_const).sub (continuous_finsetSum _ (fun j _=> A.plank_C g h W w0 k hv y hx v w j x)) -- tune args order
 let z:=bassH (Bake.lagE X); exact ((hb (Bake.lagE X)).const_smul z) -- tune
end BondL
end YM.CF.Sour
