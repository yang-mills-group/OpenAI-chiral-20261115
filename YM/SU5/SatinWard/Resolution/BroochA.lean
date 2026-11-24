import YM.SU5.SatinWard.Resolution.Carnation
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Synod
import YM.SU5.SatinWard.Resolution.Achilles
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
open CF.Fir _root_.YM.Regis.Circuit.SpringDay.Spring
variable {s:ℕ}
local notation "ζ"=> CF.Papyrus.Franc.SatinForce.Flash
local notation "K₁"=> principalKid
local notation "K₀"=> Op SU.Slot
-- economy grouping spin then family.Q equals trace pairing
abbrev twinIdx:= plusSpin × minusSpin
abbrev slotPair:= SU.Slot × SU.Slot
abbrev poKent (q:twinIdx)(r:slotPair): principalKid:= ((q.1,r.1),(q.2,r.2))
abbrev puBand(A B:K₀):ℂ:=∑ i:slotPair,A i.1 i.2 * B i.2 i.1
abbrev polA (i j:Axis)(d:Gaia)(q r:twinIdx):ℂ:= petal i q.1 q.2 * petal j r.1 r.2 * (ζ r.2 q.1 d*ζ q.2 r.1 d) -- Coe fix
abbrev polSpin (i j:Axis) (d:Gaia):ℂ:= ∑ q:twinIdx,∑ r:twinIdx, polA i j d q r
private lemma hKent (M:principalKid→ℂ) : (∑ i:principalKid,M i) = ∑ i:twinIdx,∑ j:slotPair,M (poKent i j):=by
 rw [←Fintype.sum_prod_type (fun v:twinIdx × slotPair=> M (poKent v.1 v.2))]; let q:twinIdx×slotPair≃principalKid:=⟨fun v=>poKent v.1 v.2,fun v=>( (v.1.1,v.2.1),(v.1.2,v.2.2)),fun _=>rfl,fun _=>rfl⟩; exact (Equiv.sum_comp q M).symm
lemma leaf_kids (A B:K₀)(i j:Axis)(d:Gaia)(q r:twinIdx)(u v:slotPair):
       ordinaryW i A (poKent q u)*ordinaryW j B (poKent r v)*kindDU d (poKent q u) (poKent r v) = if v=u.swap then polA i j d q r*(A u.1 u.2 * B u.2 u.1) else 0:=by
 unfold ordinaryW kindDU polA fieldKid poKent; simp only [Matrix.kronecker_apply]
 by_cases h:v=u.swap; · subst v; rcases u with ⟨u,w⟩; change petal i q.1 q.2 *A u w * (petal j r.1 r.2 * B w u) * ((if u=u then ζ r.2 q.1 d else 0)*(if w=w then ζ q.2 r.1 d else 0)) = if _ then _ else _; (repeat' rw [if_pos rfl]); ring -- rw if_pos ambiguous
 rw [if_neg h]; by_cases p:v.2=u.1 <;> simp only [p, ↓reduceIte,zero_mul,mul_zero]; rw [if_neg (fun f=> h (Prod.ext f.symm (by assumption))),mul_zero,mul_zero]
lemma boutique (i j:Axis)(A B:K₀)(d:Gaia): bouquet i A j B d= polSpin i j d* puBand A B:=by
 let X(q r:principalKid):=ordinaryW i A q*ordinaryW j B r*kindDU d q r
 change (∑ p:K₁,∑ q:K₁,X p q)= _; simp_rw [hKent, show ∀ q r u v,X (poKent q u) (poKent r v)=_ from fun _ _ _ _=> leaf_kids ..] -- infer RHS dependent? _ implicit lambdas not generalized? tuning
 unfold polSpin; rw [sum_mul]; apply sum_congr rfl; intro q h; rw [sum_comm, sum_mul]; refine sum_congr rfl ?_; intro v h; unfold puBand; rw [mul_sum]; refine sum_congr rfl ?_; intro i h; rw [Finset.sum_ite_eq',if_pos (mem_univ _)] -- eq vs eq'
open Ember
abbrev sunGlyph :plusSpin:=⟨0,by simp [plusHalf]⟩
abbrev dayGlyph :plusSpin:=⟨1,by norm_num [plusHalf]⟩
abbrev eveGlyph :minusSpin:=⟨2,by norm_num [plusHalf,SpinIdx]⟩
abbrev gigGlyph :minusSpin:=⟨3,by norm_num [plusHalf,SpinIdx]⟩
private lemma duoPlus(Z:plusSpin→ℂ):(∑ i:plusSpin,Z i)=Z sunGlyph+Z dayGlyph:= by
 rw [show (univ: Finset plusSpin)={sunGlyph, dayGlyph} from ?_,sum_insert ?_, sum_singleton]; · exact notMem_singleton.mpr (fun e=>Fin.zero_ne_one (congrArg (fun x:plusSpin=> (x:SpinIdx)) e))
 ext ⟨i,hi⟩; rw [mem_insert,mem_singleton,iff_true_intro (mem_univ _),true_iff]; change i∈plusHalf at hi; rw [plusHalf, mem_filter] at hi; by_cases p:i.val=0; · exact Or.inl (Subtype.ext (Fin.ext p))
 exact Or.inr (Subtype.ext (Fin.ext (show i.val=1 from by omega)))
private lemma duoMinus(Z:minusSpin→ℂ):(∑ i:minusSpin,Z i)=Z eveGlyph+Z gigGlyph:= by
 rw [show (univ: Finset minusSpin)={eveGlyph,gigGlyph} from ?_,sum_insert ?_,sum_singleton]; · apply notMem_singleton.mpr; intro h; have e:= congrArg (fun x:minusSpin=> (x:SpinIdx)) h; norm_num [eveGlyph,gigGlyph,SpinIdx] at e; revert e; decide +kernel
 ext ⟨i,hi⟩; rw [mem_insert,mem_singleton,iff_true_intro (mem_univ _),true_iff]; have he:i.val≥2:= Nat.le_of_not_gt (fun x=> hi (mem_filter.mpr ⟨mem_univ i,x⟩)); by_cases p:i.val=2; · exact Or.inl (Subtype.ext (Fin.ext p))
 exact Or.inr (Subtype.ext (Fin.ext (show i.val=3 from by omega)))
private lemma sumT (Z:twinIdx→ℂ):(∑ i:twinIdx,Z i)= Z (sunGlyph,eveGlyph)+Z (sunGlyph,gigGlyph)+(Z (dayGlyph,eveGlyph)+Z (dayGlyph,gigGlyph)):=by rw [Fintype.sum_prod_type Z]; simp_rw [duoPlus, duoMinus]
local notation "ℐ"=> Complex.I
private def helmet (u:Axis→ℂ)(i j:SpinIdx):ℂ:= ∑ a:Axis,rubrix i j a*(-2*ℐ*(u a))
abbrev wingKernel (X:Gaia)(i:Axis):ℝ:= Maxwell.grad i Maxwell.Green X
abbrev kinCost (i:Axis)(X:Gaia):ℝ:= -2*(2*wingKernel X i^2 - ∑ μ:Axis, (wingKernel X μ)^2)
-- prove scalar for 3; other by rotation taste need rank all components for Lap. maybe evaluate general. `polar-- gamma squares` symbolic. Fin L.
-- import Adef. both gauges fixed. Use complex u polynomial not c.
private abbrev hypo (i:Axis)(u:Axis→ℂ)(k l:twinIdx):ℂ:= petal i k.1 k.2 * petal i l.1 l.2 * (helmet u l.2 k.1*helmet u k.2 l.1)
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
private lemma AA_stamp : Aop=Matrix.diagonal (![1,1,0,0]):=by rw [Adef]; ext i j; fin_cases i<;>fin_cases j<;>norm_num [grading,Matrix.one_apply,Matrix.diagonal_apply]
@[local simp] private lemma uu2 {α:Type*}(a b c d:α) : ![a,b,c,d] ( (2:Fin 4))=c:=rfl 
@[local simp] private lemma uu3 {α:Type*}(a b c d:α) : ![a,b,c,d] ( (3:Fin 4))=d:=rfl 
private lemma hE20 (f:Axis→ℂ): helmet f (eveGlyph:SpinIdx) (sunGlyph:SpinIdx)=-2*(ℐ*f 2+f 3):=by norm_num [helmet, eveGlyph, sunGlyph, rubrix, gammaOp, YM.Axis,SpinIdx, Fin.sum_univ_four]; try (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  skip); ring_nf <;> norm_num [Complex.I_sq] <;> ring
private lemma hE30 (f:Axis→ℂ): helmet f (gigGlyph:SpinIdx) (sunGlyph:SpinIdx)=-2*(ℐ*f 0-f 1):=by norm_num [helmet, gigGlyph, sunGlyph, rubrix, gammaOp, YM.Axis,SpinIdx, Fin.sum_univ_four]; try (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  skip); ring_nf <;> norm_num [Complex.I_sq] <;> ring
private lemma hE21 (f:Axis→ℂ): helmet f (eveGlyph:SpinIdx) (dayGlyph:SpinIdx)=-2*(ℐ*f 0+f 1):=by norm_num [helmet, eveGlyph, dayGlyph, rubrix, gammaOp, YM.Axis,SpinIdx, Fin.sum_univ_four]; try (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  skip); ring_nf <;> norm_num [Complex.I_sq] <;> ring
private lemma hE31 (f:Axis→ℂ): helmet f (gigGlyph:SpinIdx) (dayGlyph:SpinIdx)=-2*(-ℐ*f 2+f 3):=by norm_num [helmet, gigGlyph, dayGlyph, rubrix, gammaOp, YM.Axis,SpinIdx, Fin.sum_univ_four]; try (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  skip); ring_nf <;> norm_num [Complex.I_sq] <;> ring
private lemma lE02(a:Axis): Tap.petal a sunGlyph eveGlyph= ![0, 0, 1/2, ℐ/2] a:=by fin_cases a<;> norm_num [Tap.petal,sunGlyph, eveGlyph,AA_stamp,gammaOp,YM.Axis,SpinIdx,Matrix.diagonal_mul] <;> (first | rfl | (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  ring_nf <;> norm_num [Complex.I_sq]<;> ring) | (ring_nf <;> norm_num [Complex.I_sq] <;> ring))
private lemma lE12(a:Axis): Tap.petal a dayGlyph eveGlyph= ![1/2, ℐ/2, 0, 0] a:=by fin_cases a<;> norm_num [Tap.petal,dayGlyph, eveGlyph,AA_stamp,gammaOp,YM.Axis,SpinIdx,Matrix.diagonal_mul] <;> (first | rfl | (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  ring_nf <;> norm_num [Complex.I_sq]<;> ring) | (ring_nf <;> norm_num [Complex.I_sq] <;> ring))
private lemma lE03(a:Axis): Tap.petal a sunGlyph gigGlyph= ![1/2, -ℐ/2, 0, 0] a:=by fin_cases a<;> norm_num [Tap.petal,sunGlyph, gigGlyph,AA_stamp,gammaOp,YM.Axis,SpinIdx,Matrix.diagonal_mul] <;> (first | rfl | (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  ring_nf <;> norm_num [Complex.I_sq]<;> ring) | (ring_nf <;> norm_num [Complex.I_sq] <;> ring))
private lemma lE13(a:Axis): Tap.petal a dayGlyph gigGlyph= ![0, 0, -(1/2), ℐ/2] a:=by fin_cases a<;> norm_num [Tap.petal,dayGlyph, gigGlyph,AA_stamp,gammaOp,YM.Axis,SpinIdx,Matrix.diagonal_mul] <;> (first | rfl | (simp only [show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl,show (3:Fin 4)=Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero];  ring_nf <;> norm_num [Complex.I_sq]<;> ring) | (ring_nf <;> norm_num [Complex.I_sq] <;> ring))
private theorem hemCost(i:Axis)(u:Axis→ℂ): ∑ k:twinIdx,∑ l:twinIdx, hypo i u k l= -2*(2*u i^2-∑ μ:Axis,(u μ)^2):=by
 simp_rw [sumT]; simp only [hypo]; (repeat' (first | rw [hE20] | rw [hE21] | rw [hE30] | rw [hE31] | rw [lE02] | rw [lE12] | rw [lE03] | rw [lE13] )); fin_cases i<;>norm_num [YM.Axis,Fin.sum_univ_four]<;> ring_nf <;> norm_num [Complex.I_sq] <;> try simp only [show (⟨2,by decide⟩:Fin 4)=2 from rfl,show (⟨3,by decide⟩:Fin 4)=3 from rfl]
 all_goals ring
lemma polKernel(i:Axis)(d:Gaia): polSpin i i d=(kinCost i d:ℂ):=by
 let u:Axis→ℂ:=fun k=> ↑(wingKernel d k); unfold polSpin polA; simp_rw [show ∀ j:SpinIdx,∀ i, ζ j i d= helmet u j i from fun _ _=> rfl] -- only rw once needs simp_rw
 change (∑ k:twinIdx,∑ l, hypo i u k l)=_; rw [hemCost]; unfold kinCost u; push_cast; rfl
#print axioms boutique
#print axioms polKernel
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
