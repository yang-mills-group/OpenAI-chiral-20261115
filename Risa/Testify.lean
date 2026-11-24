import Risa.Dune
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 3000
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
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
local notation "D1" => CF.Compass.decor
variable {φ:Stitch→G.Color}
variable (Xh:Hike) {o:Site n} (p':BudgetPoint) (σ:Signed)
local notation "χ"=> Xh.cost
local notation "Γ"=> (ridges:ℝ)
local notation "𝕥"=>p'.threshold
local notation "Υ₀"=>posess G Xh
-- adaptation Hospitality.Evidence sparse cut. river. Payroll proof.
include B P
lemma here_s(A:Support c)(D:Finset (Cell n))(V Y:fieldDir G n 1) (q':Clip)(e:q'=q)(f:Cell n)(g:zenith r D A m f): Etch.river q' f (tiler B P V + advent B P r D A m Y)=faceCurl f (V+Y):=by
 subst q'; rw [← Etch.river_now q B P, LinearMap.map_add (tiler B P)]; ext i
 change (Real.sqrt q.direct)⁻¹ * ((tiler B P V) (f,false,i) + ((if zenith r D A m f then (tiler B P Y) (f,false,i) else 0))) = _; rw [if_pos g]; rfl
omit B P in
private lemma ifSlot {G:Gauge}(R:Rules G)(k:ℕ)(x:ℝ):0≤ slotError R k x:=by unfold slotError faceCutError; have he:= G.colorScale_pos; have hx:=R.positive; positivity
lemma inside_ag {ι:Type*}[Fintype ι](Ap:Etch G ι)(y:ℝ)(h:Ap.payroll ≤ m)(g:stint r m A D o){V Y:_root_.YM.Regis.Head.Dir G n}(l:TrustLogs (V+Y) U r A v)(K:0≤v)(d:v ≤ R.c)(f:0<β): |Ap.palette y σ o U - Ap.chalk q (y*coupling β) σ o (starFee B P r A D m Y β V)| ≤ Ap.priceS R y v:=by
 rw [Etch.pin, Etch.chalk]; let c'(i:ι):=skewSlot G (Ap.slot i) σ; let L(i:ι):= slotFace (c' i) o; let E(i:ι):=skewSig G (Ap.slot i) σ
 let x(i:ι):= y • E i • (c' i).atSite U o; let Y'(i:ι):=(y*coupling β) • E i • Etch.river q (L i) (starFee B P r A D m Y β V); let a:= Ap.priceS R y v
 have he: ‖x-Y'‖ ≤ |y| * slotError R Ap.payroll v:= by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg y) (show 0≤ slotError R Ap.payroll v from ?_))).mpr (fun i=>?_)
    · exact ifSlot R _ _
    have ht:= Ap.payroll_paid i σ; have hm:= ((Work.E04.slot_separation (c' i) o).trans ht).trans h
    have hp:zenith r D A m (L i):=by
       refine ⟨g.1.shift (by apply le_trans (Nat.add_le_add_right hm (Sequest m)); unfold hallBill Sequest; omega),?_⟩
       intro b hb; have hP:=g.2 _ hb; have he:=separation_triangle b.1 (L i).1 o
       rw [separation_comm (L i).1] at he; change separation o (L i).1 ≤ m at hm; unfold hallBill Sequest at *; omega
    have hY: Y' i= y • E i • faceCurl (L i) (V+Y):=by
       unfold Y' starFee; rw [_root_.map_smul,here_s B P _ _ V Y q rfl _ hp]; rw [mul_smul,smul_comm (coupling β) (E i), smul_inv_smul₀ (coupling_pos f).ne']
    rw [Pi.sub_apply,hY,show x i= y • E i • (c' i).atSite U o from rfl,←smul_sub,←smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,show |E i|=1 from skewSq ..,one_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg y); exact grantSlot l K d _ (g.1.shift (y:=o) (by simp [hallBill,Sequest]; omega)) ht
 rw [←Real.norm_eq_abs]; exact (Ap.steady.norm_sub_le x Y').trans ((mul_le_mul_of_nonneg_left he Ap.favor.prop).trans_eq (mul_assoc ..).symm)
variable (Rs:Rules G)(y:ℝ)
local notation "£"=>|y| *𝕥
noncomputable abbrev sunFee(p:BudgetPoint):= Etch.priceS (Υ₀) Rs y v+(χ)⁻¹^2*((ridges:ℝ)* (|y| *p.threshold)^4)
lemma sun_safe:0 ≤ sunFee Xh Rs y p' (v:=v):= add_nonneg (Etch.priceS_pos (Υ₀) Rs y) (by unfold ridges; positivity)
lemma same_act(h:(Υ₀).payroll ≤ m)(g:stint r m A D o){V Y:_root_.YM.Regis.Head.Dir G n}(l:TrustLogs (V+Y) U r A v)(K:0≤v)(d:v ≤ Rs.c)(f:0<β)(E:D=weak p'.threshold U)(w:20 ≤ m):
 |solicit G p' y σ o U- (Υ₀).chalk q (y*coupling β) σ o (starFee B P r A D m Y β V)| ≤ sunFee Xh Rs y p' (v:=v):=by
 -- R/Rs mismatch.D use Rs.
 have x:= inside_ag B P σ (Υ₀) y h g l K d f; let a:= (party G y σ o U); have hs:= Risa.echo (σ:=σ) p' (E ▸ g) w; let hp:= cast_part G p' y σ o U hs
 have he : |solicit G p' y σ o U- (Υ₀).palette y σ o U|≤ χ⁻¹^2*(Γ*£^4):=by
    rw [exposed,solicit,if_pos hs]; refine (Risa.expensed Xh).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    refine (sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hp i) 4)).trans_eq ?_; rw [sum_const,card_univ,nsmul_eq_mul]
 apply le_trans (abs_sub_le ..) -- arguments placeholders maybe ambiguous
 exact (add_le_add he x).trans_eq (add_comm ..)
#print axioms same_act
end Risa
end YM.Gleam.Luster
