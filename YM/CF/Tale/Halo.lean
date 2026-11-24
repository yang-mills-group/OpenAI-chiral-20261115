import YM.CF.Tale.Loom
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure
open Skye Scree Siete
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open Heir AnalyticBridge.SectorAffine.Offset AnalyticBridge.VerifiedReset
variable{c f:Side}{S:StepData c f}{G:Gauge}{T:Tube SU.group S}{m:ℕ}{J:S.Choices}
variable {x z s t a α r C δ K:ℝ}{F:Forest S.ratio}
open SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open StressFlux
-- actual canonical observation charges along root choice; Wald.No offsets in orbit packing yet
variable {L: Side}(P: Patch)(p:5≤ P.L.val)(Pt:Teller SU.group)(hs:P.Branches Pt.bind SU.group)(q:Chi)(a:ℝ)(ha:0<a)(Ω:ℝ)(hΩ:0<Ω)(j k n:ℕ)(ht:4≤j)(hv:2≤ k)(W:Push.Uniform.Before SU.group Pt.top.width Pt.top.paths Pt.j Pt.bind (k+1+1))(l:ℕ)(hl:l≤18)
variable {A':Stores S}
local notation "G₀"=> SU.group
local notation "cΛ"=> Pt.bind.penalty
local notation "Fζ" x:max=> fiery SU.group x P.L
local notation "Y" x:max=> (Ω*fiery SU.group x P.L)
variable (pJ:Pt.j=j)
private lemma herbal (o:Site c)(b d:PlaqAxes) : LocalOn (halo 2 {o}) (a_Op c o b d) ∧ GaugeInvariant (a_Op c o b d):=by
 refine ⟨fun i j h=> ?_,fun i j=>?_⟩
 · unfold a_Op; simp_rw [petals_reads o _ i j h]
 unfold a_Op; simp_rw [petals_gauge,inner_adjoint]
include W hl ha hΩ hs p hv ht pJ
local notation "Πx"=> (P.L)
abbrev quanta(V:Config (SU.group) c→ Config SU.group f)(o:Site f)(x y: PlaqAxes): Directions SU.group c→ℝ:= (a_Op f o x y) ∘ V ∘ increment 1
-- Anchor σ of singleton. same root. Mom projection entries.(S.tangent sense). purchases at exact candidates in local tomography.Buff.
structure Wyth (T:Tube SU.group S)(X:Support f)(U:Config SU.group c→ Config SU.group f) (o:Site c) (p : BudgetPoint) (L:Side)(a:ℝ):Prop where
 sonic(x y s r:PlaqAxes)(h: halo 2 {S.ratio.embed o}⊆X): ‖iteratedFDeriv ℝ 2 (quanta U (S.ratio.embed o) x y) 0 ![clipT p o s,clipT p o r]-(zolo p L r x s y+ zolo p L s x r y)‖≤ a*p.threshold^2
-- staging d:L.tW.
lemma score_v : ∃ t:ℝ,0<t∧∀ᶠ x in atTop,0<gateX SU.group P.L l (n*k+n*k) x t∧∀ E R:BudgetPoint, Find E R k n x P.L→∀ {c f:Side} (S:StepData (More c) (More f))(T:Tube SU.group S), Cert P Pt S T x→(∃ (F:Flight j j)(w:(More f).val=(More c).val * F.L.val), F.L=P.L∧ Oaken (T:=T) cΛ j j F w)→∀ (J:S.Choices)(A:Stores S)(F:Forest S.ratio)(X:Support (More f))(U:Support (More c))(o:Site (More c)), A.flags=flags (temp x) (1:Config SU.group (More c))→ sizedP SU.group P Pt S T F → S.ratio.embed o∈ X → Short S R X→∀ (I:Type)[Fintype I][DecidableEq I](M:Museum F x A X U I),(∀ i:I,separation (S.ratio.parent (S.ratio.embed o)) (incF M i) ≤ 7*(1+radiusB x)) →∀ (β:ℝ), y SU.group P.L x/2 ≤ β →∀ N:Config SU.group (More f),∀ Z:LogArray SU.group (Active A x F),(∀ i∈coZ M,‖Z i‖≤gateX SU.group P.L l (n*k+n*k) x t) → Wyth T X (recent T β J q (Y x) l N Z) o E P.L a :=by
 obtain ⟨γ,C,hγ,hC,H⟩:= faith_S Pt.bind.penalty j j Pt.bind.penalty_pos ht ht
 obtain ⟨r,Q,hr,hQ,h⟩:= Heir.recital SU.group P Pt hs k hv
 obtain ⟨ε,he,v⟩:= grace_k Q a γ C hQ hγ ha hC P.L k n hr -- tune
 obtain ⟨t,jp0,T⟩:= portraitZ k l Ω hΩ Pt P hs hv hl W q ε he n
 refine ⟨t,jp0,?_ ⟩; filter_upwards [T,h,v,Folio.subscribe Pt P] with x hx ht_ hV h'
 refine ⟨?_,fun E R hv' {c f} S T hC _=>?_ ⟩; swap -- tune branch binds witness
 · rename_i o'; obtain ⟨P',w,t,e⟩:=o'; -- t shadow !!
   intro J A F X U o g hg ho hp I _ _ M hP β hβ N Z hZ
   have hk: S.ratio.parent (S.ratio.embed o)=o:=Ratio.embed_parent ..; let A_H:=atoms T M β J q (Y x) l N Z (fun _=> (1:SU.E)); have hY:Guide _ (E.dirBound o) 0 (A_H ∘ increment 1) k (ε*fiery SU.group x P.L):=hx.2 S T hC A F 1 hg g J β hβ I M E hv'.hK hv'.large o (fun i=> hk ▸ hP i) N Z (fun i p=>(hZ i p).trans (gate_mono _ _ jp0 le_rfl (Nat.le_add_right ..))) _ -- t
   obtain ⟨a',hq₁,q₁,hζ,p',hx0,hX⟩:=hV; have hT:= ht_ S T hC.got hC.funds hC.size F J
   set r' := termQ x n; let U':= recent T β J q (Y x) l N Z; let b':= S.ratio.embed o; have hw : loom E (Heir.reach x) 1 ≤ r':=by unfold r' termQ loom; rw [hv'.large,hv'.hK,one_mul]
   have H':= h' S T hC.funds.1 hC.got; have hsX:= hC.size; let Y'(V:townX (More c)):= (curt (Heir.reach x) o V,A_H (increment 1 V)); let V':= display T F x J true ∘ Y'
   have hf: herald S X U' V':= buzz M β q l N Z o hT hY hζ hw a' H' hp hv'.hU ho -- tune
   refine ⟨fun p₂ p₃ v w' pΩ=>?_ ⟩; let F':=(fun W:Directions SU.group (More c)=> increment 1 (V' W)); rw [←hv'.large] at hX
   have he':2*radiusB x<(More c).val:=by omega
   refine le_trans ?_ hX; rw [show iteratedFDeriv ℝ 2 (quanta U' b' p₂ p₃) 0= iteratedFDeriv ℝ 2 (a_Op _ b' p₂ p₃ ∘ F') 0 from ?_]; swap
   · apply Filter.EventuallyEq.eq_of_nhds; apply EventuallyEq.iteratedFDeriv; apply Eventually.mono hf; rintro v ⟨k,s⟩; have hu:=herbal b' p₂ p₃; let Kv:=U' (increment 1 v); exact ((hu.2 k Kv).symm.trans (hu.1 (F' v) _ (fun i u w=> s i (mem_union_left _ (pΩ u)) (mem_union_left _ (pΩ w)))).symm) -- gauge coherence
   have hi:= Φp Pt.bind.penalty j j P' w M β q l N Z o e hT hY hζ hw a' hQ hq₁ q₁ hv H' hp hv'.hU ho p₂ p₃ v w' C γ H (radiusB x) (show radiusB x≤ Heir.reach x from by unfold Heir.reach; omega) he' (by rw [t]; exact p) p' hx0 -- ABI
   rw [t] at hi; exact hi
 
 · unfold gateX feeI; have he:= Scales.pos SU.group P.L x; positivity
end YM.CF.Tale
