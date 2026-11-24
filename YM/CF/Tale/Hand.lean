import YM.CF.Tale.Ride
import YM.CF.Hove.Curb
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Tale
set_option quotPrecheck false
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
-- Transverse linear gauge moment, transported spot. canonical blocks only. no t-period interpolation
variable (k:ℝ)(j t:ℕ)(h:0<k)(p:4≤j)(v:4≤t)(P:Flight j t)
variable {f c:Side}(w:f.val=c.val *P.L.val)(o:Site f)(d b a:Axis)(i:TypeFace 1)
open MultiNext.SignedSource
local notation "Z"=> Exterior.coord d
local notation "L"=> P.L
abbrev deckY:= P.visitRatio (f:=f) (c:=c) w
local notation "G"=> deckY j t P w
abbrev Lt := (P.duo k).A0
local notation "R"=> Lt k j t P
local notation "T"=> advanceC L R [a]
local notation "y"=> (deckY j t P w).residue o
local notation "U"=> T (y,i) Z
open Matrix
abbrev modeT (Sx:Side) (a b:Axis) (i j:TypeFace 1):ℝ:= if a=b ∧ i=j then ((Sx.val:ℝ)⁻¹)^2 else 0 -- symbol uses invalid id?
include h p v
lemma vow_Q (o':d ≠ b): (Summable (fun x:Cover=> (x b:ℝ)* U x)) ∧ ∑' x:Cover,(x b:ℝ)* U x= modeT L a b i (Exterior.coord d):=by
 let g(x:Cover):ℂ:= U x; obtain ⟨a₀,C,h₀,tx,hC⟩:= (secure_both k h p v).1.honored p 1
 have hg: Row.strip T  a₀ (C/(P.L.val:ℝ)^(1+[a].length)):=hC P _ (by simp; omega); obtain ⟨A,t',H⟩:= Hove.loan_h a₀ h₀; have hk:=H (Row.constant_strip T hg (y,i) Z); obtain ⟨hp,ht⟩:= Tap.moments hk (by norm_num) b
 let V(x:Cover):= (x b:ℝ) * U x
 have hV:Summable V:=by
    have he:= (Complex.reCLM.hasSum hp.hasSum).summable; apply Summable.congr (f:=fun x:Cover=> Complex.re ((x b:ℂ) * g x)) he (fun x=>by unfold V g; simp)
 have he := (ht.congr_of_eventuallyEq (show (fun x:ℝ=> Next.Free.spread (Flight.pilot k) 1 [a] P y (Tap.bout b x) i Z)=ᶠ[𝓝 0] _ from ?_ )).unique (entry_X k j _ h p v P d a b y i o'); swap; · filter_upwards [Tap.bout_v b] with t u; change _=Row.read (T) _ (y,i) Z; unfold Lt; rw [Flight.duo, show advanceC _ _ [a]= _ from (secure_both k h p v).1.traverse p 1 (by simp; omega) P]; exact ((secure_both k h p v).1.bankRead p 1 (by simp; omega) P y u i Z).symm
 refine ⟨hV,Complex.ofReal_injective ?_⟩; rw [Complex.ofReal_tsum]; simp_rw [Complex.ofReal_mul,Complex.ofReal_intCast]; apply mul_left_cancel₀ Complex.I_ne_zero; rw [he]; unfold modeT; split_ifs <;>simp [div_eq_mul_inv, ← inv_pow]
local notation "B1"=> Co c (TypeFace 1)
variable (D: Co c (TypeFace 1) → SU.group.Color)
lemma ζuse : MultiNext.SignedSource.Newt.load (installed G R) D (o+Lattice.step a,i) - MultiNext.SignedSource.Newt.load (installed G R) D (o,i)=MultiNext.SignedSource.Newt.load (installed G T) D (o,i):=by
 obtain ⟨a₀,C,h₀,tx,hC⟩:= (secure_both k h p v).1.honored p 1
 have he(l:List Axis)(p:l.length ≤ [a].length):Whole (advanceC L R l):= ⟨a₀,_,h₀,hC P l (by simp at p; omega)⟩
 have ht:= MultiNext.SignedSource.Newt.spatial G R D [a] P.odd he o i 0; simp [MultiNext.SignedSource.Newt.iterate,MultiNext.SignedSource.Newt.jump,add_comm] at ht; exact ht -- ambiguity CF.Newt rename
end YM.CF.Tale
