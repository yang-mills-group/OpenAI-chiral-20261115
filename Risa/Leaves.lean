import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes
abbrev Stitch:= PlaqAxes×Bool×Bool
def digs(i:Axis)(a:Bool): Lattice.Step:=⟨i,a⟩
abbrev emptyT(b:PlaqAxes):RG.Slot:=⟨[],b⟩
lemma clean_face(b:PlaqAxes)(x:Site n): (emptyT b).atSite U x= StressFlux.plate U x (posDir b.val.1) (posDir b.val.2):=by
 rw [atSite_path]
 unfold slotFace Slot.offset emptyT
 simp [travel,stop]; rfl
noncomputable def corsage (b:Stitch): Signed:=⟨Equiv.refl _,fun i=> if i=b.1.val.1 then b.2.1 else if i=b.1.val.2 then b.2.2 else false⟩
abbrev ringT (G:Gauge)(b:Stitch) : RG.Slot:= skewSlot G (emptyT b.1) (corsage b)
abbrev lipT(G:Gauge)(b:Stitch):ℝ:= skewSig G (emptyT b.1) (corsage b)
lemma dial_s (b:Stitch)(x:Site n): StressFlux.plate U x (digs b.1.val.1 b.2.1) (digs b.1.val.2 b.2.2)= lipT G b • (ringT G b).atSite U x:=by
 let s:=corsage b
 have h:affine s x (0:Site n)=x:=by rw [affine,Signed.act_zero,zero_add]
 let q:= (reflects (emptyT b.1) s (0:Site n) x U)
 have t:= plate_pull s x U (0:Site n) (posDir b.1.val.1) (posDir b.1.val.2)
 rw [clean_face,t,h] at q;
 have e₁:(posDir b.1.val.1).rotate s = digs b.1.val.1 b.2.1:=by simp [Step.rotate,posDir,s,corsage,digs]
 have e₂:(posDir b.1.val.2).rotate s=digs b.1.val.2 b.2.2:=by
    have h':b.1.val.2≠b.1.val.1:=(show b.1.val.1 < b.1.val.2 from b.1.property).ne'; simp [Step.rotate,posDir,s,corsage,digs,h']
 rwa [e₁,e₂] at q
-- Linear decode
noncomputable def floret (G: Gauge)(i:PlaqAxes)(x:Stitch→G.Color): G.Color:=
 ((4:ℝ)⁻¹) • ((lipT G (i,false,false) • x (i,false,false) - lipT G (i,false,true) • x (i,false,true))-(lipT G (i,true,false) • x (i,true,false)- lipT G (i,true,true) • x (i,true,true)))
lemma floret_sub(i:PlaqAxes)(x y:Stitch→G.Color): floret G i x-floret G i y=floret G i (x-y):=by simp only [floret,Pi.sub_apply,smul_sub]; module
lemma cblossom(i:PlaqAxes): ContDiff ℝ 1 (floret G i):=by unfold floret; fun_prop
lemma floret_smul(i:PlaqAxes)(x:Stitch→G.Color)(a:ℝ): floret G i (a • x)=a • floret G i x:=by simp only [floret,Pi.smul_apply,smul_sub]; module
lemma floret_bound(i:PlaqAxes)(x:Stitch→G.Color): ‖floret G i x‖≤ ‖x‖:=by
 let a:=‖x‖; have h(b:Stitch): ‖lipT G b • x b‖≤ a:=by rw [norm_smul,Real.norm_eq_abs,skewSq,one_mul]; exact norm_le_pi_norm x b
 let v(s:Bool× Bool):G.Color:= lipT G (i,s) • x (i,s)
 have hs(s): ‖v s‖≤a:= h (i,s)
 unfold floret; rw [norm_smul,Real.norm_eq_abs]; norm_num
 have hp(s t:Bool×Bool): ‖v s-v t‖ ≤ a+a:= (norm_sub_le ..).trans (add_le_add (hs _) (hs _))
 have ht:= (norm_sub_le (v (false,false)-v (false,true)) (v (true,false)-v (true,true))).trans (add_le_add (hp _ _) (hp _ _)); exact (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤ (1:ℝ)/4)).trans_eq (show (1:ℝ)/4*(a+a+(a+a))=‖x‖ by unfold a; ring_nf)
lemma floret_gauge(i:PlaqAxes)(x:Stitch→G.Color)(t:G.El):floret G i (fun b=> G.adjoint t (x b))= G.adjoint t (floret G i x):=by simp [floret]
lemma leaves (t:Signed)(b:Site n)(i:PlaqAxes): floret G i (fun x=> ((ringT G x).atSite (pull t b U) 0))=AnalyticBridge.VerifiedReset.petals (pull t b U) 0 i:=by
 unfold floret petals clover stencil
 simp_rw [←dial_s (U:=pull t b U)] -- defeq digs false.Flow. palindrome.
 rfl
#print axioms leaves
end Risa
end YM.Gleam.Luster
