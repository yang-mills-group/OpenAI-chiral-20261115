import YM.SU5.SatinWard.Resolution.PseudoSpin
import YM.SU5.SatinWard.Resolution.Spangled
import Merino.Brooch.Seal
import Anomaly.Separate.PureP

/-!
# The X/W characters and spin probe action
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
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
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU


namespace SignSlot
open Buffered Swell Porticus Hest Nacre StressExchange Merino.Brooch
local notation "K0"=> Op SU.Slot
variable {p:BudgetPoint}
lemma boom_herm (i:Axis): star (Tap.boom i)=Tap.boom i:=by
 unfold Tap.boom; rw [op_star_kron,star_one]; unfold Tap.taxi; rw [show Fir.zen (step i)=Complex.I • gammaOp i from ?_]; swap; · unfold Fir.zen; rw [sum_eq_single i]; simp; intro j _ h; simp [h]; simp
 rw [star_smul,star_mul,star_smul, (gammaAdj _).star_eq,gradingAdj.star_eq,Matrix.mul_smul, Matrix.smul_mul,gradingSwap]; norm_num
local notation "X+"=> baseF false
local notation "X-"=> baseF true
-- weighted formal W bilinear. λ=1.Scale at Slot block; Pal Binned adj.PR
abbrev colorL (A:Op SU.Slot):Pal:= (1:Op SpinIdx) ⊗ₖ A
abbrev silenceΦ (A:Op SU.Slot):Pal:= Complex.I • (colorL (star A)* baseF false+colorL A * baseF true)
private lemma commuting (V:Op SpinIdx)(A:K0): Commute (colorL A) (V ⊗ₖ (1:K0)):=by show _*_=_*_; unfold colorL; rw [op_kron_mul,op_kron_mul]; simp
lemma color_bin(v:K0)(j:Bool): Commute (baseF j) (colorL v):=(binA j ▸ commuting (binV j) v).symm -- orientation inspect
local notation "A₊"=> baseF false
local notation "A₋"=> baseF true
lemma grade_ortho : baseF false * baseF true=0:=by rw [show A₋=1- A₊ from rfl,mul_sub,mul_one,φ_sq]; abel
lemma grade_ortho' : baseF true * baseF false=0:=by rw [show A₋=1- A₊ from rfl,sub_mul,one_mul,φ_sq]; abel
lemma culm_nothing (v:K0) : culm (silenceΦ v)=0:=by
 unfold culm silenceΦ; rw [Matrix.mul_smul,Matrix.smul_mul,mul_add,(color_bin (star v) false).left_comm (baseF false), ←mul_assoc _ (colorL v), (color_bin v false).eq,mul_assoc _ (baseF false),grade_ortho,φ_sq]; simp [mul_assoc,grade_ortho]
lemma ditF_left (i:Axis) : ditF false i=Complex.I • Tap.boom i:=by simp [ditF]
lemma sigma_vir (v:K0): culm (silenceΦ v)=0:= culm_nothing v
variable (o:Site n) (A:Op SU.Slot)
local notation "K♠"=> bud_k o o o
local notation "H"=>baseF true
lemma nose_spanH (i:Axis)(j:Bool) : Moto.nose (spanH j o i) o=rain_U o o • ditF j i:=by
 rw [show Moto.nose (spanH j o i) o=rain_U o o • moonB j i (lift (o-o)) from rfl]; unfold moonB; simp
lemma XΦ_birth : jetsL o (bud_k o o o (silenceΦ A))= axialSchedule A:=by
 rw [pub_eq]; refine Prod.ext (by
    change snapH _ _ _=_; rw [vibra o o o (silenceΦ A) _ _ _ _ (show Moto.nose _ _ =_ • A₊ from rfl) (show Moto.nose _ _ =_ • A₋ from rfl),φ_a]; exact sigma_vir A) (Prod.ext (funext fun i:Axis=> ?_) (funext fun i:Axis=> ?_))
 · change culm (snapH _ _ _)=petal i⊗ₖ A; rw [vibra o o o (silenceΦ A) _ _ _ _ (nose_spanH o i false) (show Moto.nose _ _ = _ • A₋ from rfl)]; unfold culm
   rw [show (ditF false i)ᴴ=star (ditF false i) from rfl]; unfold silenceΦ; rw [ditF_left,star_smul,boom_herm,Complex.star_def,Complex.conj_I,Matrix.smul_mul, Matrix.mul_smul]; let U:=colorL A; let V:=colorL (star A)
   have hz: (V*A₊+U*A₋)* A₋=U*A₋:=by rw [add_mul,mul_assoc,mul_assoc,grade_ortho,φ_sq]; simp -- syntax
   rw [smul_smul, neg_mul,Complex.I_mul_I,neg_neg,one_smul, mul_assoc (Tap.boom _),hz, ←mul_assoc A₊,show A₊*Tap.boom i= _ from boom_A i]; let P:= petal i⊗ₖ (1:K0); change P*(U*A₋)*A₋ = _
   have he: P*U= petal i⊗ₖ A:=by unfold P U colorL; rw [op_kron_mul]; simp
   let v:=pet_normShape i A; have hp:petal i⊗ₖ A * A₋=petal i⊗ₖ A:=by
      nth_rw 1 [←v]; change (A₊*_*A₋)*A₋=_; rw [mul_assoc,φ_sq]; exact v
   rw [←mul_assoc P,he,hp,hp]
 change culm (snapH _ _ _)=petal i⊗ₖ star A; rw [vibra o o o (silenceΦ A) _ _ _ _ (show Moto.nose _ _= _ • A₊ from rfl) (nose_spanH o i true),φ_a]; unfold silenceΦ culm
 let U:=colorL A; let V:=colorL (star A); have ht: A₊*(V*A₊+U*A₋)=V*A₊:=by rw [mul_add,(show A₊*(V*A₊)=V*(A₊*A₊) from (color_bin ..).left_comm _), (show A₊*(U*A₋)=U*(A₊*A₋) from (color_bin ..).left_comm _),grade_ortho,φ_sq]; simp
 rw [Matrix.mul_smul, ht,Matrix.smul_mul, show ditF true i=-(Complex.I) • Tap.boom i from rfl,Matrix.mul_smul,Matrix.mul_smul,Matrix.mul_smul, smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul,mul_assoc V,show baseF false*Tap.boom i= _ from boom_A i]
 rw [show V*(petal i⊗ₖ (1:K0))= petal i⊗ₖ star A from by unfold V colorL; rw [op_kron_mul]; simp]; exact pet_normShape i (star A)
lemma silenceComm (v:K0)(g:SU.E)(h:Commute v (matter g).val)(p:Commute (star v) (matter g).val) : Commute (silenceΦ v) (KinX g):=by
 have ht (b:K0)(h:Commute b (matter g).val): Commute (colorL b) (KinX g):=by show _*_=_*_; unfold colorL; change (1⊗ₖb)*colorL _=_; unfold colorL KinX; simp only [op_kron_mul,h.eq] -- inspect
 exact (( (ht _ p).mul_left (color_bin _ false)).add_left ((ht v h).mul_left (color_bin _ true))).smul_left Complex.I
lemma latticeFieldEstimates : K♠ = seed_k o o:= by funext v; unfold bud_k; rw [Haro.wind_t] -- rainV = wind
-- occasional binder X, pragmata
local notation "Xc"=> tickA n
lemma tagFormula : baseF false=Fock.cutM (univ.filter (fun i:Kt=> i.1∈plusHalf)):=by -- copy
 rw [←binA,show binV false=Fock.cutM Lat.plusHalf from (by unfold binV Fir.angle; rw [if_neg (by decide),sub_sub_cancel]; exact Fir.Adef.trans raising.symm)]; ext p q
 by_cases u:p.1=q.1<;>by_cases w:p.2=q.2<;>simp [Fock.cutM,u,w,Matrix.one_apply,Prod.ext_iff]; rw [Prod.ext u w]; simp
lemma tick_bud (V:Pal): Xc*K♠ V= K♠ (baseF false * V):=by
 rw [latticeFieldEstimates o,touchP,tagFormula]
 ext ⟨⟨x,i⟩,w⟩ ⟨⟨y,j⟩,z⟩; rw [Fock.cutM,Matrix.diagonal_mul]; by_cases s:o=x<;>by_cases t:o=y<;> simp [seed_k,Hove.portB, Matrix.diagonal_mul,Fock.cutM,Window.mem_Tset,s,t] -- tune
lemma bud_star (V:Pal): star (K♠ V)= K♠ (star V):=by rw [latticeFieldEstimates]; ext p q; change star (if o=q.1.1∧o=p.1.1 then V (Hove.portB q) (Hove.portB p) else 0)=(if o=p.1.1∧o=q.1.1 then star (V (Hove.portB q) (Hove.portB p)) else 0); split_ifs <;> (first| exact star_zero ℂ| rfl| tauto)
lemma bud_right (V:Pal): K♠ V *Xc= K♠ (V*baseF false):=by
 have he:= congrArg star (tick_bud o (star V)); rw [star_mul, bud_star,star_star, (Cascade.plus_P n).isSelfAdjoint.star_eq,bud_star,star_mul,star_star,show star A₊=A₊ from φ_a false] at he; exact he
lemma bud_neg (V:Pal): K♠ (-V)= -K♠ V:=by rw [latticeFieldEstimates]; ext i j; by_cases v:o=i.1.1∧o=j.1.1 <;> simp [seed_k,Matrix.neg_apply,v]; split <;> simp_all
lemma bud_sub(V W:Pal):K♠ (V-W)=K♠ V-K♠ W:=by rw [latticeFieldEstimates]; ext i j; by_cases v:o=i.1.1∧o=j.1.1 <;> simp [seed_k,Matrix.sub_apply,v]; split <;> simp_all
lemma bud_scale (x:ℝ)(V:Pal): K♠ (x • V)=x • K♠ V:=by rw [latticeFieldEstimates]; ext i j; by_cases v:o=i.1.1∧o=j.1.1 <;> simp [seed_k,v]
lemma bud_last (V:Pal): K♠ V*(1-Xc)= K♠ (V*A₋):=by rw [mul_sub, mul_one,bud_right,show A₋=1-A₊ from rfl,mul_sub,mul_one,bud_sub]
lemma bud_center (V:Pal): Xc*K♠ V*(1-Xc)= K♠ (culm V):=by rw [tick_bud,bud_last]
abbrev onsiteSensor (o:Site n)(V:Pal): Mark n:= onsiteOne (bud_k o o o V)
-- show averaging of silent Mark via scalar proof. Later Weight exact normalization.
lemma silent_plain(U:Fields n): onsiteSensor o (silenceΦ A) U= Matrix.trace (Xc* bud_k o o o (silenceΦ A)) • 1:=by
 change preJ _ _=_; unfold preJ; rw [bud_center,sigma_vir,show bud_k o o o 0 =0 from by rw [latticeFieldEstimates o]; ext i j; simp [seed_k]]; simp [dg,dyad]
lemma spin_center (i:Axis): Xc* K♠ (petal i⊗ₖ A) *(1-Xc)= K♠ (petal i⊗ₖ A):= by rw [bud_center,show culm _= _ from pet_normShape i A]
lemma spin_small (i:Axis): Matrix.trace (K♠ (petal i⊗ₖ A))=0:= by
 let S:=K♠ (petal i⊗ₖ A); have hp:=spin_center o A i; have hv:(1-Xc)* Xc=0:= by rw [sub_mul,one_mul,(Cascade.plus_P n).isIdempotentElem.eq,sub_self]
 change S.trace=0; nth_rw 1 [← show Xc*S*(1-Xc)=S from hp]; rw [Matrix.trace_mul_comm,←mul_assoc,hv,zero_mul,Matrix.trace_zero]
lemma spin_current (i:Axis)(X :Fields n): onsiteSensor o (petal i⊗ₖ A) X= dg (K♠ (petal i⊗ₖ A)):=by
 change preJ _ _=_; let S:=K♠ (petal i⊗ₖ A); have hp:Xc*S*(1-Xc)=S:=spin_center o A i
 have hv:Xc*S=S:=by nth_rw 1 [←hp]; rw [←mul_assoc, ←mul_assoc,(Cascade.plus_P n).isIdempotentElem.eq]; exact hp
 unfold preJ; rw [hp,hv,spin_small]; simp; rfl
end SignSlot
end YM.CF.QuadClock

