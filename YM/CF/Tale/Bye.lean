import YM.CF.Tale.Score
import YM.CF.Hom.Myrrh
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
variable {x y z s t a α r C δ K:ℝ}{F:Forest S.ratio}
section receipt
variable (A:ℝ)(h:0<A)(p:Tour T F x J m r C)(hv:0≤ temp x)(v:0<r)(u:temp x ≤A)(g:2 ≤ m)
include h p hv v u g
lemma spin_t : ‖mainStroke T F true‖≤ C+A*C:=by
 let R:=mainStroke T F true; let f:=display T F x J true
 have he:= (p.costs true); have hp:= he.uniform 0 (by rw [norm_zero]; exact v.le); have hC:=hp.nonneg
 rw [mul_comm A]; exact (show ‖R‖ ≤‖fderiv ℝ f 0‖ + ‖fderiv ℝ f 0-R‖ from (by rw [norm_sub_rev]; apply le_trans (norm_le_norm_sub_add ..); linarith)).trans (add_le_add (price_one hp (by omega)) (he.miss.trans (mul_le_mul_of_nonneg_left u hC))) -- tune norm 
end receipt
variable (k:ℝ)(j n:ℕ)(P:Flight j n)(w:f.val=c.val*P.L.val)
structure Oaken : Prop where
 scale: S.ratio = deckY j n P w
 first: installed (S.ratio) T.R.A0=installed (deckY j n P w) (Lt k j n P)
-- flat-chart claim receipts
variable {A':Stores S}{d:ℝ}{X:Support f}{Y:Support c}{I:Type}[Fintype I][DecidableEq I](M:Museum F x A' X Y I)(β:ℝ)(q:Chi)(D:ℕ)(U:Config SU.group f)(Z:LogArray SU.group (Active A' x F))
local notation "Kφ"=> (recent T β J q d D U Z)
local notation "Δ"=> (atoms T M β J q d D U Z (fun _:Site c=> (1: SU.E)))
variable (o:Site c)
local notation "Xq"=> (deckY j n P w).embed o
local notation "pΩ"=> (S.ratio.embed o)
local notation "Wφ"=> (fun v:townX c=> ((curt (Heir.reach x) o v), (Δ (increment 1 v))))
local notation "W"=> (display T F x J true ∘ Wφ)
variable (p_:Oaken (S:=S) (T:=T) k j n P w) 
variable {E Y': BudgetPoint}(QW:Heir.Act T F x J m t C)(u:Guide (Directions SU.group c) (E.dirBound o) 0 (atoms T M β J q d D U Z (fun _:Site c=>(1:SU.E))∘ increment 1) m z)(hZ:z≤ r)(hs:loom E (Heir.reach x) 1 ≤ r)(vt:r<t)(hv:1≤ C)(hq:r≤1)(h0:temp x ≤r)(hx:2≤ m){P_: Teller SU.group}(E':Folio.Bulletin x P_ T)(hY:Short S Y' X)(hp: Y'.B≤2 * radiusB x)(hg: S.ratio.embed o∈ X)
def herald (S:StepData c f)(X:Support f)(U:Config SU.group c→ Config SU.group f)(v: Directions SU.group c→ Directions SU.group f): Prop:=∀ᶠ x in 𝓝 (0:Directions SU.group c),∃ k:Site f→ SU.E, Agrees (inspected X) (increment 1 (v x)) (Lattice.gauge k (U (increment 1 x)))
include u hZ hs vt E' hY hp hg QW
lemma buzz : herald S X Kφ W:=by
 let A:= Wφ; let g:=fun _:Site c=>(1:SU.E)
 have hp': Guide _ _ 0 A m r:= ((curt_q o E _ m).rise hs).duo (u.rise hZ)
 filter_upwards [hp'.1.continuousAt.norm.eventually (gt_mem_nhds (hp'.size.trans_lt vt))] with v p
 let G i:= SU.group.lieExp (φ T F true (A v).1 i); let q':=increment (1:Config SU.group c) v; let K:= (curt (Heir.reach x) o) v; let U':= Kφ q'; let t:= increment 1 ((display T F x J true) (A v))
 refine ⟨fun i=> G i * g (S.ratio.parent i),?_⟩; rw [← show Lattice.gauge G (Lattice.gauge (fun i=>g (S.ratio.parent i)) U')=Lattice.gauge (fun i=> G i * g (S.ratio.parent i)) (Kφ (increment 1 v)) from (by unfold g; simp [Lattice.gauge,U',q'])]; intro i h l; change t i=_; rw [show t= sounds T F x J true (A v) from QW.represents true _ p.le]
 have ht:S.ratio.parent pΩ=o:= Ratio.embed_parent ..; apply obtain_s T M β J q d D U Z g E' (M.asks_origin hg) q' K _ i h l ((separation_comm ..).trans_le ((short_patch hY hp hg h).trans (by omega))) true -- tune
 intro i p; change  (1:SU.E)* q' i* (1:SU.E)⁻¹= _; unfold K increment q'; rw [curtP,if_pos (show separation o i.1 ≤ Heir.reach x from (by rwa [ht] at p))]; simp [increment]
include p_ h0 hv hx hq
local notation "χ"=> (clinicFee m C * r^2)
local notation "θ"=> E.threshold
lemma Φp(A B X Y:PlaqAxes)(M' a0:ℝ)(h:Thy j n k a0 M') (i:ℕ)(he:i ≤ reach x)(hB:2*i<c.val)(hL:5≤ P.L.val)(hd:χ+z≤1)(hA: temp x ≤ 1): ‖iteratedFDeriv ℝ 2 (a_Op f (S.ratio.embed o) A B ∘ increment 1 ∘ W) 0 ![clipT E o X,clipT E o Y]- (zolo E P.L Y A X B + zolo E P.L X A Y B)‖≤ humpV a0 M' (χ+(C+1*C)*r) (χ+z) E.threshold ((P.L.val:ℝ)⁻¹ ^ 2) i :=by
 let G:= W
 have hs': 0<t:=lt_of_le_of_lt ((show (0:ℝ)≤loom E (reach x) 1 from (by unfold loom; have h:=E.threshold_pos; positivity)).trans hs) vt
 have hT:= spin_t 1 (by norm_num) QW.toTour (Work.E04.temp_nonneg x) hs' hA hx
 obtain ⟨u0,u1⟩:= exhibit E G o (Heir.reach x) u hZ QW.toTour h0 hv hq vt.le hx hs rfl _ hT
 let Tz:=trade_L k j n P w o (Heir.reach x); rw [p_.scale]; apply sonic_S k j n P w o E (Heir.reach x) i he hB hL h u0 (show Guide _ _ 0 (W-⇑Tz) m _ from ?_) hd hx -- tune implicit
 have hp:(Heir.route T ∘ (curt (Heir.reach x) o))= (Tz:Directions SU.group c→ Directions SU.group f):=by unfold Tz Heir.route trade_L; rw [show main T=_ from p_.first]; rfl
 rwa [← hp]
end YM.CF.Tale
