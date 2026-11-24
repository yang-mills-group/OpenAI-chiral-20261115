import YM.CF.Vp929.Canon.Musc
import YM.CF.Tap.Pallet
import YM.CF.Vp929.Budget.Arith
import GaugeFieldConstruction.StigmaFe
import YM.CF.Vp929.Stage.Shore
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
open BrentFe Ember
open YM.GaugeFieldConstruction.Flavor
-- POTION exact commutation
set_option maxHeartbeats 80000
variable {n L:Side}{q a:ℝ}{V:Op (Single n)}
lemma Scoria.slotP_fe (x:BigFe)(e:Frequency L n q)(j:ℕ)(M:Male)(S:TestW.Scoria j M V a)(b:Axis→ Bool)(p:let t:=spar j M (1:Pane n); twist (FieldFe n x) ((1-t)*V*t)=(1-t)*V*t):
 let D:=TkFe SpinIdx (Ferr x).val; let Z:=potion j M (heroP V) (song q b); D*Z=Z*D:=by
 intro D Z; let A:=Tern j M (loft V); let Y:= Rush.cart n A; let J:= song q b; let F:=potion j M (heroP V); let B:= (coΛ n x).val; let t:= spar j M (1:Pane n)
 obtain ⟨he,hp,hZ⟩:=S.earm; have hx: B*Y= Y*B:=by
    have ht:(FieldFe n x).val*((1-t)*V*t)=(1-t)*V*t*(FieldFe n x).val := (tw_fe ..).mp p; change (1-t)*V*t=love n Y at he; rw [he,FieldPay, ←map_mul,←map_mul] at ht; exact (love _).injective ht
 let ζ(s:SpinIdx×SU.Slot→ℂ)(i:Model n):=mode J (Rush.natural i.1)*s i.2
 have hv(s:SpinIdx×SU.Slot→ℂ): Y *ᵥ ζ s= ζ (Z*ᵥ s):= funext fun ⟨m,b'⟩=> earns hZ (sung e _) (sung_fee e _) s m b'
 have hb(s:SpinIdx×SU.Slot→ℂ): B *ᵥ ζ s= ζ (D*ᵥ s):=by
    funext ⟨m,i⟩; change ( (jump (Equiv.refl (Site n)) (fun _=> D))*ᵥ _ ) _ =_ ; simp only [ζ,Matrix.mulVec,dotProduct,Fintype.sum_prod_type, jump_apply]; rw [sum_eq_single m]; swap; · intro z _ vz; simp [Ne.symm vz]
    swap; · simp
    simp only [Equiv.refl_apply,ite_true]; simp only [Finset.mul_sum]; exact sum_congr rfl fun i h=>sum_congr rfl fun j h=>sum_congr rfl fun k h=>by ring
 have hh(s:SpinIdx×SU.Slot→ℂ) :(D*Z)*ᵥ s=(Z*D)*ᵥ s:=by
    have hg:= congrArg (fun A=> A *ᵥ ζ s) hx; simp only [←Matrix.mulVec_mulVec,hv,hb] at hg; funext u; rw [←Matrix.mulVec_mulVec, ←Matrix.mulVec_mulVec]; exact mul_left_cancel₀ (show mode J (Rush.natural (0:Site n))≠0 from Complex.exp_ne_zero _) (congrFun hg (0,u)) -- tune mulVec_mulVec
 ext i l; simpa [Matrix.mulVec,dotProduct,Matrix.one_apply] using congrFun (hh (fun k=>(1:Tap.Pal) k l)) i
private abbrev ωA := Axis→Bool
private def χfe(b:Bool)(R:Signed) : Equiv.Perm (Axis→ Bool) where
 toFun η v:= (b.xor (R.flip (R.perm.symm v))).xor (η (R.perm.symm v))
 invFun η v:= (b.xor (R.flip v)).xor (η (R.perm v))
 left_inv η:=by funext i; simp; cases b<;>cases R.flip i<;>cases η i<;>rfl
 right_inv η:=by funext i; simp; cases b<;>cases R.flip (R.perm.symm i)<;>cases η i<;>rfl
private lemma shiftFe (p:ωA)(r:ℝ)(b:Bool)(R:Signed):song r (χfe b R p)= cadence R b (song r p):=by
 funext i; obtain ⟨j,rfl⟩:= R.perm.surjective i; unfold cadence; cases b<;>cases h:R.flip j <;> cases g:p j <;> simp [χfe,song,h,g,signs] -- tune sign ambig
local notation "binF"=> bins SU.Slot
local notation "binN"=> 1-binF
private def boxX(z:Pal): Pal:=binF*z*(binN)
private lemma boxV(z:Pal): Binned (boxX z):=by
 let P:=binF; let A:=binN
 have he:P*P=P:=binsSq _; have hz:A*A=A:=by unfold A; rw[sub_mul,one_mul,mul_sub,mul_one,binsSq]; abel
 change P*(P*z*A)*A=P*z*A; rw [←mul_assoc P,←mul_assoc,he,mul_assoc _ A,hz]
private lemma box_s(z:Pal)(i:Axis): spaX (boxX z) i=spaX z i:=by
 rw [show boxX z= _ from (spa_p z).symm]; exact spa_s ..
private lemma box_k(z:Op SU.Slot):Commute binF ((1:Op SpinIdx)⊗ₖ z):=by
 unfold bins Commute SemiconjBy; rw [op_kron_mul,op_kron_mul,mul_one,one_mul,one_mul,mul_one]
private lemma box_u (z:Pal)(A:Op SU.Slot)(p:Commute z ((1:Op SpinIdx)⊗ₖ A)):Commute (boxX z) ((1:Op SpinIdx)⊗ₖ A):=((box_k A).mul_left p).mul_left ((Commute.one_left _).sub_left (box_k A))
private lemma box_pose (b:Bool)(R:Signed)(U:UNI SpinIdx)(v:JetS R b (detX R) U):
 let X:= sings b (twoU U b); X binF= if (detX R) then binN else binF:=by
 intro X; unfold X bins; rw [Scroll.wingK, show sings b _ (1:Op SU.Slot)=1 by rw [singT,win_i,map_one]]
 have ht:=angleX v true; cases hx:detX R<;>rw [hx] at ht
 · simp only [Bool.false_eq_true, ↓reduceIte]; exact congrArg (· ⊗ₖ (1:Op SU.Slot)) (show sings b U Aop=Aop from ht) -- tune
 rw [show sings b U Aop= _ from ht]; change (1-Aop)⊗ₖ (1:Op SU.Slot)= 1-_ ; simp only [sub_eq_add_neg,op_kron_neg,Matrix.add_kronecker, Matrix.one_kronecker_one]
private abbrev boseFe (q:ℝ)(i:Axis)(F:Momentum→Pal):Pal:= (16*q)⁻¹ • ∑ η : Axis→Bool, signs (η i) • F (song q η)
private lemma shadeRay (b:Bool)(R:Signed)(U:UNI SpinIdx)(v:JetS R b (detX R) U)(e:Frequency L n q)(F:Momentum→Pal)(p:AxisP F)(i:Axis):
 sings b (twoU U b) (boxX (boseFe q (R.perm i) F))= Thera.jazz (detX R) (hush (b.xor (R.flip i)) (boxX (boseFe q i F))):=by
 let r:= b.xor (R.flip i); let k:= detX R; let C:=boseFe q (R.perm i) F; let Z:=boseFe q i F
 let X:=sings b (twoU U b); let χ:=χfe b R
 have ht: X C= Thera.jazz k (hush r Z):=by
    let y(η:Axis→Bool):=signs (η i) • F (song q η); let V(η:Axis→Bool):=signs (η (R.perm i)) • F (song q η)
    let u:=(16*q)⁻¹
    have he(η:Axis→Bool):X (V (χ η))=Thera.jazz k (hush r (y η)):=by
       unfold X V; rw [shiftFe]; unfold y
       rw [singT,Scroll.win_r,map_smul, ←singT,p.rise R b U v _ (sung e η)]
       have hv:χ η (R.perm i)=r.xor (η i):=by simp [χ,r,χfe]
       rw [hv]; change signs _ • Thera.jazz k (F _)= _ -- tune ; rw after by on next
       cases k<;>cases r<;>cases η i<;> simp [signs,Thera.jazz,hush, star_smul] -- tune neg alignment
    change X (u • ∑ η:Axis→Bool, V η)=Thera.jazz k (hush r (u • ∑ η:Axis→Bool,y η))
    rw [←Equiv.sum_comp χ V]; unfold X; simp only [singT,Scroll.win_r,win_sum,map_smul,map_sum]; change u • ∑ η:Axis→Bool,X (V (χ η))= _; simp_rw [he]; cases k <;> cases r<;>simp [Thera.jazz,hush]
 have hb:X (binN)= 1-X binF:=by unfold X; rw [singT,win_l,win_i,map_sub,map_one,singT]
 change X (boxX C)=Thera.jazz k (hush r (boxX Z)); unfold boxX; rw [show ∀ M N:Pal, X (M*N)=X M * X N from fun _ _=> singm ..]; rw[ show ∀ M N:Pal,X (M*N)=X M*X N from fun _ _=>singm ..,ht,hb]; rw [show X binF= if k then binN else binF from box_pose b R U v]; cases k<;> cases r<;> simp [Thera.jazz,hush, bins,Aadj, op_star_kron,mul_assoc] -- tune
lemma pick_rayFe (e:Frequency L n q)(F:Momentum→ Pal)(p:AxisP F)(X:Op SU.Slot)(h:∀ η, Commute (F (song q η)) (TkFe SpinIdx X)): Commute (pickM (sovX q F)).val X:=by
 let D(i:Axis):=boxX (boseFe q i F)
 obtain ⟨H,T⟩:= Tap.color_all D (fun i=>boxV _) (fun R b U v=>shadeRay b R U v e F p) (fun i g=> box_u _ _ (Commute.smul_left (Commute.sum_left univ _ _ (fun η _=> Commute.smul_left (p.hold g _ (sung e η)) _)) _)) -- tune signature
 have he:spaX (D 0) 0=spaX (sovX q F) 0 := box_s ..
 rw[he] at H; rw[pickM_left H, ←he]
 have ht: Commute (D 0) ((1:Op SpinIdx) ⊗ₖ X):= box_u _ _ ((Commute.sum_left univ _ _ (fun η _=> (h η).smul_left _)).smul_left _)
 have hx:= ht.eq; rw [T,op_kron_mul,op_kron_mul,mul_one,one_mul] at hx; exact spa_i 0 hx
lemma fairwaveFe (x:BigFe)(g:RegBudget n)(b:BudgetPoint)(d c:ℝ)(p:IncX Utrue g b d c)(r:1≤d)(k:b.power=2)(M:Male)(j:ℕ)(w:1≤j)(e:Frequency L n q) (h: let t:=Dial.spar j M (1:Pane n); let V:= StackL g univ; twist (FieldFe n x) ((1-t)*V*t)=(1-t)*V*t): Commute (waveTest q g j M).val (Ferr x).val:=by
 obtain Z:=gem (live_full n) p r k w M 0 (fun i _=>Nat.zero_le _); exact pick_rayFe e _ (Psy j w M Z.axisP) _ (fun i=>Commute.symm (Z.slotP_fe x e j M i h)) -- field notation tune
#print axioms fairwaveFe
end TestW
end Test
end YM.CF.Py.Rate
