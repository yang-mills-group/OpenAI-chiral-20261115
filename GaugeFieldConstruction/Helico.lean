import GaugeFieldConstruction.ZoneLine
import YM.CF.Moto.Road
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
variable (o:Skye.Seat n)
open scoped ComplexConjugate
-- signed Fourier interpolation
abbrev tips (s: slice)(x:Views): ℝ := s.elim x.1 x.2
abbrev voltS (s:slice):Views:= Sum.elim (fun i=> (Pi.single i 1,0)) (fun i=> (0,Pi.single i 1)) s
def ξK (k:lotV): Views→L[ℝ]ℝ:= κviews o (measuresN o k).1 (measuresN o k).2
lemma tipN {i:slice}: ‖voltS i‖≤1:=by cases i <;> simp [voltS,Prod.norm_def,Pi.norm_single] -- tune
lemma lays(x:Views) : ∑ i:slice,tips i x • voltS i=x:=by
 rw [Fintype.sum_sum_type]; apply Prod.ext _ _ <;> simp [Prod.fst_sum,Prod.snd_sum,tips,voltS]; · ext i; simp [Finset.sum_apply,Pi.single_apply]
 ext i; simp [Finset.sum_apply,Pi.single_apply] -- tune fsum
lemma tips_e (i j:slice): tips i (voltS j) = if i=j then 1 else 0:=by rcases i with i|i <;> rcases j with j|j <;> simp [tips,voltS,Pi.single_apply] -- tune
lemma roam_add (x y:Cover)(s:Plane): rom (x+y) s=rom x s+rom y s:=by simp only [rom_p,Pi.add_apply,Int.cast_add,add_mul,sum_add_distrib]
lemma roam_neg (x:Cover)(s:Plane): rom (-x) s= -rom x s:=by simp only [rom_p,Pi.neg_apply, Int.cast_neg, neg_mul,sum_neg_distrib]
lemma roam_step(i:Axis)(x:Plane): rom (step i) x=x i:=by simp [rom_p, step_apply] -- tune
lemma ξspot (x:Cover)(p:lateral x≤4)(u:20<n.val)(i:Plane): pointF o (parked o x) i= (1/2:ℝ)*rom (siteOffset o) i+ rom x i:=by unfold pointF; rw [spot_lift o x p u]; unfold spotSize; rw [two_smul]; change (1/2:ℝ)* rom _ i=_; rw [roam_add,roam_add]; ring
abbrev neutralK : lotV:= (none,none)
def coinOr(i:Ortho)(x:Views):ℝ:=i.elim 0 fun i=>tips i x
lemma ξspot_E (x:lotV)(u:20<n.val)(v:Views): ξK o x v= ξK o neutralK v+coinOr x.1 v+coinOr x.2 v:=by
 have he(i:lotV): ξK o i v= -(pointF o (parked o (knots i).1) v.1) + pointF o (parked o (knots i).2) v.2:=rfl
 have ht(i:lotV): ξK o i v= -((1/2:ℝ)*rom (siteOffset o) v.1+rom (knots i).1 v.1)+((1/2:ℝ)*rom (siteOffset o) v.2 + rom (knots i).2 v.2):=by rw [he,ξspot o _ (knot_rad i).1 u,ξspot o _ (knot_rad i).2 u]
 have hf(i:Ortho) : -rom (spad i).1 v.1+rom (spad i).2 v.2=coinOr i v:=by
    have hz(x:Plane): rom 0 x=0:=by rw [rom_p]; simp
    cases i with |none=> simp [spad,hz,coinOr]| some a=>rcases a with i|i <;> simp [spad,petals,roam_neg,roam_step,coinOr,tips,hz]
 have hv:knots neutralK=innerX:=by unfold knots; rw [show spad neutralK.1=0 from rfl,add_zero,add_zero]
 rw [ht x,ht,hv]; dsimp only [knots,Prod.snd_add,Prod.fst_add]; rw [roam_add,roam_add,roam_add,roam_add]; linarith only [hf x.1,hf x.2]
abbrev saleCoeff (x y:Site n)(h:ℝ):ℂ:= ((h:ℂ)^2 * Caller o x * Caller o y)⁻¹
abbrev modelK (x y:Site n)(h:ℝ)(A:Pal):Op (Single n):= seed_k x y (saleCoeff o x y h • A)
lemma pounce(x y:Site n)(A:Pal)(u:h≠0)(v:Views): streamF o (modelK o x y h A) h v= PayS (κviews o x y) v • A:=by
 let Q:= κviews o x y; have hx:=Complex.ofReal_ne_zero.mpr u; have hc(z:Site n):Caller o z≠0:=norm_ne_zero_iff.mp ((call_bit o z) ▸ one_ne_zero) -- tune direction
 unfold modelK; rw [streamS]; simp_rw [star_P]; rw [sum_eq_single x,sum_eq_single y]; · rw [if_pos ⟨rfl,rfl⟩,smul_smul]; have he:= show PayS Q v * (h:ℂ)^2* Caller o x* Caller o y= PayS Q v*((h:ℂ)^2 *Caller o x * Caller o y) from (by ring); rw [he,mul_assoc (PayS Q v),saleCoeff,mul_inv_cancel₀ (by exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) (hc _)) (hc _)),mul_one]
 · intro w _ p; rw [if_neg (fun t=>p t.2.symm),smul_zero]
 · simp
 · intro w _ p; simp [Ne.symm p]
 simp
abbrev yardLot := lotV → Pal
def notesK (f:yardLot)(h:ℝ): Op (Single n):= ∑ k:lotV,modelK o (measuresN o k).1 (measuresN o k).2 h (f k)
lemma trait_K (x y:Site n)(A:Pal)(u:SheetQ A):MarkPH (modelK o x y h A):=by -- tune names
 intro g p s; unfold modelK; rw [star_P]; split; exact (u.tax g).smul_left _; exact Commute.zero_left _
lemma notes_mark (f:yardLot)(u:∀i,SheetQ (f i)): MarkPH (notesK o f h):=by
 intro g i j; unfold notesK; let q(k:lotV):= modelK o (measuresN o k).1 (measuresN o k).2 h (f k); rw [show matPH (∑ k:lotV, q k) i j= ∑ k:lotV,matPH (q k) i j from ?_]; swap; · ext a b; change (∑ k:lotV,q k) (Moto.hailV i a) (Moto.hailV j b)=_; simp only [Matrix.sum_apply]; rfl -- tune tap
 unfold Commute SemiconjBy; rw [Matrix.sum_mul, Matrix.mul_sum]; exact sum_congr rfl fun k w=> (trait_K o _ _ _ (u k) g i j).eq
lemma notes_fee(f:yardLot)(u:h≠0)(v:Views): streamF o (notesK o f h) h v=∑ k:lotV,PayS (ξK o k) v • f k:=by
 have ht(k:lotV): streamF o (modelK o (measuresN o k).1 (measuresN o k).2 h (f k)) h v=PayS (ξK o k) v • f k:= pounce o _ _ _ u _ -- tune
 simp_rw [← ht]; unfold streamF notesK; rw [sum_comm (s:=univ) (t:=univ) (f:=fun (k:lotV) (x:yardZ (n:=n))=>flare_one (portB x.1) (portB x.2) (PayS _ _ * hill_Z o (modelK o (measuresN o k).1 (measuresN o k).2 h (f k)) h x.1 x.2))] -- tune rw
 apply sum_congr rfl; intro i _; unfold hill_Z; rw [Matrix.sum_apply]; simp only [Finset.mul_sum,map_sum]
-- At ≤2 need control actual shift polar.
private def ZkL(x:Pal):ℂ→L[ℝ]Pal:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) x |>.restrictScalars ℝ
def signalK(k:lotV)(A:Pal):PalOne:=postF (bookP (ξK o k) 1) (ZkL A)
lemma stemsS(k:lotV)(A:Pal): AptK (fun i=> PayS (ξK o k) i • A) (signalK o k A):=by
 have ht(k): AptK (PayS (ξK o k)) (bookP (ξK o k) 1):= (factor_sale (ξK o k) 1).equal (Eventually.of_forall fun i=>mul_one _)
 exact (ht k).geomF (ZkL A)
def comV (f:yardLot):PalOne := oleSum univ (fun i=> signalK o i (f i))
lemma stamps (f:yardLot)(u:h≠0): markJet o (notesK o f h) h=comV o f:=by
 have ht: AptK (fun x=> streamF o (notesK o f h) h x) (comV o f):= ((AptK.sumV univ _ _ (fun i _=> stemsS o i (f i))).equal (Eventually.of_forall fun i=> (by rw [Finset.sum_apply]; exact (notes_fee o f u i).symm))) -- tune
 exact (K_pays o _ _).unique ht
private lemma oh(f: Views→ PalOne)(u:Views): (f u).1=(f u).1:=rfl
abbrev Zring(k:lotV)(v:Views):ℂ:= Complex.I* (↑(ξK o k v):ℂ)
lemma stamp_f0(f:yardLot): (comV o f).1=∑ i:lotV,f i:=by
 unfold comV oleSum; rw [Prod.fst_sum]; apply sum_congr rfl; intro i _; change (bookP (ξK o i) 1).1 • f i=_; rw [fund0]; exact one_smul .. -- smul meta
lemma stamp_f1(f:yardLot)(v:Views): (comV o f).2.1 v=∑ i:lotV,Zring o i v • f i:=by
 unfold comV oleSum; rw [Prod.snd_sum,Prod.fst_sum,_root_.sum_apply]; apply sum_congr rfl; intro i _; change ((bookP _ (1:ℂ)).2.1 v) • f i= _; rw [fund1,mul_one]
lemma stamp_f2(f:yardLot)(v w:Views): (comV o f).2.2.val v w=∑ i:lotV,(Zring o i v*Zring o i w) • f i:=by
 unfold comV oleSum; rw [Prod.snd_sum,Prod.snd_sum,Submodule.coe_sum, _root_.sum_apply,_root_.sum_apply]; apply sum_congr rfl; intro i _; change ((bookP _ (1:ℂ)).2.2.val v w) • f i=_; rw [fund2,mul_one]
end Layout
end Lenten
end YM.CF.TableF
end
