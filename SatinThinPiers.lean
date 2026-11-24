import SatinThinLine
import YM.CF.Moto.Rune
import YM.CF.Hove.Prune
/-! Ramps, lifted in the matter geometry. ROOT matters for these transfers. -/
set_option autoImplicit false
set_option maxHeartbeats 680000
set_option synthInstance.maxSize 20000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.QuadClock
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Levier Skye Scree Hove Haro Tap Moto
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Ione StressFlux AnalyticBridge.VerifiedReset

variable {n:Side}{c t:Bool}{s:Signed}{U:UNI SpinIdx}(H:JetS s c t U)
include H
lemma step_Base(b:Bool): sings c (twoU U c) (baseF b) = baseF (t.xor b):=by
 rw [← binA,← binA]; unfold binV; rw [wingK]; rw [singT,win_l,win_i,map_sub,map_one,←singT, angleX H b, singT,win_i,map_one]
lemma step_Top (b:Bool)(i:Axis): sings c (twoU U c) (ditF b (s.perm i))= sign s i • ditF (t.xor b) i:=by
 let A(i:Axis):= grading*gammaOp i; have he(b:Bool)(i:Axis): ditF b i= (if b then ((1/2:ℝ) • A i) ⊗ₖ (1:Op Slot) else -(((1/2:ℝ) • A i) ⊗ₖ (1:Op Slot))):=by
    unfold ditF Tap.boom Tap.taxi; rw [show Fir.zen (Lattice.step i) = Complex.I • gammaOp i from (by unfold Fir.zen; rw [sum_eq_single i]; simp; intro _ _ h; simp [h]; simp), Matrix.mul_smul]
    unfold A; cases b; swap
    all_goals simp only [ite_true,Bool.false_eq_true,ite_false,smul_neg, ← Complex.coe_smul, Matrix.smul_kronecker,smul_smul]; norm_num; rw [mul_left_comm Complex.I,Complex.I_mul_I]; simp
 rw [he,he]; have hg:=H.grade; have hu:=H.cliff i; unfold A; cases b <;> cases t<;> cases g:s.flip i<;> simp only [g,hush_false,hush_true] at hg hu<;> simp only [g,sign,singT,win_n,map_neg,ite_true,ite_false,Bool.false_eq_true,Bool.xor_true,Bool.xor_false,Bool.not_true,Bool.not_false] <;> rw [←singT, Scroll.wingK]; all_goals simp only [singT] at *; all_goals simp [win_i,map_one, hu,hg,op_kron_neg]
lemma step_Moon (b:Bool)(i:Axis)(x:Cover): sings c (twoU U c) (moonB b (s.perm i) (s.act x))= sign s i • moonB (t.xor b) i x:=by
 unfold moonB; rw [singT,win_a,map_add,win_c,twist_scalar,← singT,←singT,step_Top H,step_Base H,Signed.act_at,smul_add]
 have ht(x:ℤ) : cSignX c (x:ℂ)=(x:ℂ):=by unfold cSignX; split; rw [star_intCast]; rfl -- tune
 rw [ht]; unfold sign; cases s.flip i<;> simp
omit H

abbrev portQi (s:Shape)(i:Option Axis): Option Axis:= i.map s.s.perm
abbrev signOpt (s:Signed):Option Axis→ℝ
 | none => 1
 | some i=> sign s i
abbrev Foot (n:Side):= Matrix (Single n) Kt ℂ
def fillOpt (b:Bool)(o:Site n): Option Axis→ Foot n
 | none => rampF b o
 | some i=> spanH b o i
abbrev feeOpt (o x:Site n):= Rush.wind o (Lattice.lift (x-o))
def footOpt (b:Bool)(x:Cover): Option Axis→Pal
 | none=> baseF b
 | some i=>moonB b i x
lemma noseOpt(b:Bool)(o x:Site n)(i:Option Axis): nose (fillOpt b o i) x=feeOpt o x • footOpt b (lift (x-o)) i:=by cases i<;>rfl
lemma scarOpt_sq (i:Option Axis)(s: Signed): signOpt s i*signOpt s i=1:=by cases i; exact one_mul _; rename_i i; simp only [signOpt,sign]; split<;> ring
lemma chargeOpt(a:Shape)(q:JetS a.s c t U)(b:Bool)(x:Cover)(i:Option Axis): sings c (twoU U c) (footOpt b (a.s.act x) (portQi a i)) = signOpt a.s i • footOpt (t.xor b) x i:=by
 cases i; simpa only [portQi, Option.map_none,footOpt,signOpt,one_smul] using (step_Base q b); exact step_Moon q b ..
lemma liftP(a:Shape)(o x:Site n)(hx:10*separation (a.mills n x) (a.mills n o)<n.val): lift (a.mills n x-a.mills n o)=a.s.act (lift (x-o)):=by
 -- from VerifiedReset/Spin.spin_coord. M assumption about Old distance; ensure at new.
 rw [Shape.mills,Shape.mills,spin_separation] at hx
 apply lift_eq_iff.mpr
 refine ⟨?_,fun i=>?_⟩
 · rw [←wrap_signed,wrap_lift,Signed.act_sub,Shape.mills,Shape.mills,affine,affine]; abel
 obtain ⟨j,rfl⟩:=a.s.perm.surjective i; have hi:=component_le (x-o) j; unfold separation at hx; rw [Signed.act_at]; split<;> omega
lemma bill_R (a:Shape)(o x:Site n)(hx:10*separation (a.mills n x) (a.mills n o)<n.val):
    feeOpt (a.mills n o) (a.mills n x)= a.payA o * a.payA x * feeOpt o x:=by
 let X:= lift (x-o); have hp:= footFee a o X; unfold feeOpt; rw [liftP a o x hx]; rw [show o+wrap _ X=x from (by unfold X; rw [wrap_lift]; abel)] at hp; change Rush.wind _ (a.s.act X)=_; linear_combination (norm:=ring) a.payA o * hp - (Rush.wind (a.mills n o) (a.s.act X)) * a.reflex o
lemma noseV (a:Shape)(q:JetS a.s c t U)(b:Bool)(o x:Site n)(i:Option Axis)(hx:10*separation (a.mills n x) (a.mills n o)<n.val):
    sings c (twoU U c) (nose (fillOpt b (a.mills n o) (portQi a i)) (a.mills n x))=signOpt a.s i • (((a.payA o)*a.payA x) • nose (fillOpt (t.xor b) o i) x):=by
 have ht (o x:Site n): cSignX c (feeOpt o x)= feeOpt o x:=by cases c; rfl; exact fee_real _
 rw [noseOpt,singT,win_c,ht,twist_scalar, liftP a o x hx, ←singT,chargeOpt a q b, bill_R a o x hx,smul_comm,noseOpt]; rw [mul_smul]
lemma payR (P:Op (Single n))(x y:Site n)(a:Shape)(c:Bool)(U:UNI SpinIdx): matPH (sings c (prepU a U (xtra c) n) P) x y =(a.payA x*a.payA y) • sings c (twoU U c) (matPH P (a.mills n x) (a.mills n y)):=by
 obtain ⟨A,rfl⟩:=(love n).surjective P; change matPH (sings c (prepU a U (xtra c) n) ((love n) A)) x y=(a.payA x*a.payA y) • sings c (twoU U c) (matPH ((love n) A) _ _); unfold matPH rentH; rw [wingX,StarAlgEquiv.symm_apply_apply,StarAlgEquiv.symm_apply_apply,tap_sg]; unfold milU; rw [star_smul,a.real_payA,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,mul_smul,singT,twist_formula]; rw [smul_comm]; rfl
-- prior P lives on short.
def FinLife (P:Op (Single n))(o:Site n) : Prop:= ∀ x y, matPH P x y ≠ 0 → 10*separation x o<n.val ∧ 10*separation y o<n.val
lemma finPartition (S:Scree.Hub n)(o:Site n)(U:InkD n){P:RG.BudgetPoint}{h c:ℝ}(w:PressB P S U h c)(u:S.val.1=node o)(v:Nonwrapping S.val.2 S.val.1) : FinLife (orbitPH (U 1)) o:=by
 intro x y p
 have hp:∃ i j, (matPH (orbitPH (U 1)) x y) i j≠0:= Classical.byContradiction (fun l => p (by push Not at l; exact funext₂ fun i j=> l i j)) -- tune Matrix
 obtain ⟨i,j,g⟩:=hp; let X:=Haro.tray (hailV x i) (hailV y j)
 have ht: X ⊆ camp S.val.2:=by change Prism.portB _ _ _ ≠0 at g; rw [Prism.port_eq] at g; refine mem_powerset.mp (mem_filter.mp (?_:X ∈ Pastry.Wheat (camp S.val.2))).1; by_contra h; apply g; split_ifs; rfl; change _ * Pastry.crumb (U 1).val X = _; rw [(w.fitted 1).door (show X∉ Pastry.Wheat (camp S.val.2) from h),mul_zero] -- tune
 have he(x:Site n)(z:node x∈ S.val.2):10*separation x o<n.val:=by have hz:= v (node x) z; rw [u,ζdist] at hz; unfold More at hz; change 10*(2*separation x o)< n.val*2 at hz; omega
 exact ⟨he x ((mem_filter.mp (ht (show (true,hailV x i)∈ X from by simp [X,Haro.tray]))).2),he y ((mem_filter.mp (ht (show (false,hailV y j)∈ X from by simp [X,Haro.tray]))).2)⟩
end YM.CF.QuadClock
