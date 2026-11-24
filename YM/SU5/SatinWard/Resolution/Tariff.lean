import YM.SU5.SatinWard.Resolution.Rate

/-!
# Character frames (physics-specific Sweep reps)
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
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

open ResolutionFrame
variable (F:ResolutionFrame ι) (C K A:ℝ) (L: Side)
local notation "cι"=> (Fintype.card ι:ℝ)
local notation "ε1" => Real.exp (1:ℝ)
abbrev headFine :ℝ := Real.exp (-1)/8
abbrev receiptCost:ℝ:= 2/headFine
abbrev sprintCost (L:Side) :ℝ:=(L.val:ℝ)^(79/16:ℝ)
lemma headPos:0<headFine:=by unfold headFine; positivity
lemma receipt_pos:0<receiptCost:=div_pos zero_lt_two headPos
lemma sprint_pos:0<sprintCost L:=by unfold sprintCost; positivity
lemma accuracy_pos (p:1≤C)(q:1≤K)(r:1≤A):0<accuracy C K A:=by unfold accuracy nullPay; positivity

/- Assume BOTH A ≥ this start cost AND enough L purchased to blunt hidden rebalance cost.
All before h, arity/geometry/character/v. Use of w =inv(L)^4 even at the exponent Xi.
-/
-- force binder F even if unused
def startCost (F:ResolutionFrame ι)(C K:ℝ):ℝ:= (Fintype.card ι:ℝ)*receiptCost*K* basePay C

def spillCost (F:ResolutionFrame ι)(C K A:ℝ):ℝ:= (Fintype.card ι:ℝ)*receiptCost*accuracy C K A*K* basePay C + K*(A+1)



structure RepositoryRent (F:ResolutionFrame ι)(C K A:ℝ)(L:Side):Prop where
 start: startCost F C K≤ A
 acc:A+1 ≤ (L.val:ℝ)
 error:(Fintype.card ι:ℝ)*(accuracy C K A * nullLoss L) ≤ headFine * F.chiLoss L / 2
 spill : spillCost F C K A * (nullLoss L*sprintCost L) ≤ A
 roll : receiptCost / F.chiLoss L ≤ sprintCost L -- gains
 offset : receiptCost / F.chiLoss L * (accuracy C K A * nullLoss L) ≤ 1

private lemma width_d (x:ℝ)(h:0<x): x^(79/16:ℝ)*(x^(1/16:ℝ))=x^(5:ℕ):=by rw [←Real.rpow_add h,show (79/16:ℝ)+1/16=5 by norm_num,Real.rpow_ofNat]
lemma repo_exists (p:1≤C)(q:1≤K)(e:1≤A)(r:startCost F C K≤ A):
   ∀ᶠ n:ℕ in atTop,∀ L:Side,n≤L.val→ RepositoryRent F C K A L:=by
 let W:=accuracy C K A; let V:=spillCost F C K A
 have c:= accuracy_pos C K A p q e; have hx:=headPos; have hy:= receipt_pos
 let R:= receiptCost
 -- prerequisites L > c etc. L^1/16≥V and L^1/2≥R, L*s holds.
 let B:= max (2*cι*W/headFine) (R*W)
 have b := (tendsto_rpow_atTop (show (0:ℝ)<79/16-4 by norm_num)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
 have a := (tendsto_rpow_atTop (show (0:ℝ)<1/16 by norm_num)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
 have hZ:(0:ℝ)<A:=zero_lt_one.trans_le e
 filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (A+1), (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop B, a.eventually_ge_atTop V, b.eventually_ge_atTop R] with n h v w w' L l
 let x:ℝ:=L.val; have hx₁:0<x:=by unfold x; positivity
 have fg:(n:ℝ) ≤ x:=Nat.cast_le.mpr l; have hv:B≤x:=v.trans fg
 change V≤ (n:ℝ)^(1/16:ℝ) at w; change R≤ (n:ℝ)^(79/16-4:ℝ) at w'
 have hP:V ≤ x^(1/16:ℝ):=w.trans (by gcongr)
 have hh:R≤ x^(79/16-4:ℝ):= w'.trans (by gcongr)
 let ξ:=nullLoss L; let ζ:=F.chiLoss L; have hz:=null_pos L; have hξ:=F.chi_pos L; change 0<ξ at hz; change 0<ζ at hξ; have ry:x*ξ≤ζ:=F.chi_dimension L; change 0 < W at c
 refine ⟨r,h.trans fg,?_,?_,?_,?_⟩
 · have hp:2*cι*W≤x*headFine := (div_le_iff₀ hx).mp ((le_max_left ..).trans hv)
   change cι*(W*ξ) ≤ headFine*ζ/2; linarith only [mul_le_mul_of_nonneg_left ry hx.le, mul_le_mul_of_nonneg_left hp hz.le] -- linarith monoms needs nlinarith? linarith normalize.linear treating atoms!
 · change V*(ξ*x^(79/16:ℝ)) ≤ A
   apply le_trans _ e; apply le_trans (mul_le_mul_of_nonneg_right hP (mul_nonneg hz.le (by positivity)))
   apply le_of_eq; calc
    _ = ξ*(x^(79/16:ℝ)*(x^(1/16:ℝ))):= by ring
    _ = 1:=by rw [width_d x hx₁]; change (x⁻¹)^(5:ℕ)*_=1; rw [inv_pow,inv_mul_cancel₀ (pow_pos hx₁ 5).ne']
 · change R/ζ ≤ x^(79/16:ℝ); apply (div_le_iff₀ hξ).2; refine hh.trans (le_trans ?_ (mul_le_mul_of_nonneg_left ry (by positivity)))
   rw [Real.rpow_sub hx₁]; change _≤ x^_* (x*(x⁻¹)^ (5:ℕ)); apply le_of_eq; rw [Real.rpow_ofNat]; field_simp
 · change R/ζ*(W*ξ) ≤ 1
   have hp:R*W≤x:= (le_max_right ..).trans hv
   rw [div_mul_eq_mul_div]; apply (div_le_iff₀ hξ).2; rw [one_mul,←mul_assoc]; exact (mul_le_mul_of_nonneg_right hp hz.le).trans ry

namespace ResolutionFrame
variable {F C K A L} {η:Type}
abbrev Primary(ι η: Type):= Sum ι η
-- reservoir of disjoint root tags. same across steps.
abbrev enterBasis (F:ResolutionFrame ι)(h q:ℝ): Primary ι η → ArcΦ:= Sum.elim (fun i=> F.atScale h q (leg i)) (fun _=>0)

/- load matrix as Equiv Δ (U here=Δ), hidden offsets in fine units for cancelling. -/
structure Reflow (ι η:Type) where
 U : Coords ι ≃ₗ[ℝ] Coords ι
 leaks : η → Coords ι

abbrev pulseBase(F:ResolutionFrame ι)(L:Side):ℝ:= receiptCost / F.chiLoss L
abbrev pulseHidden(F:ResolutionFrame ι)(L:Side)(C K A:ℝ):ℝ:= F.pulseBase L * (accuracy C K A *nullLoss L)

structure Economics (F:ResolutionFrame ι) (C K A:ℝ)(L:Side)(X Y:BudgetPoint)(κ q Q:ℝ)(s:Reflow ι η):Prop where
 track(i:ι): ‖s.U (leg i)-(F.typical L X Y κ i*(q/Q)) • leg i‖≤ accuracy C K A*nullLoss L
 sail(x:Coords ι):‖s.U.symm x‖ ≤ F.pulseBase L * ‖x‖
 bek(j:η):‖s.leaks j‖ ≤ F.pulseHidden L C K A

structure Energized (F:ResolutionFrame ι)(h Q:ℝ)(X : Primary ι η → ArcΦ)(s:Reflow ι η):Prop where
 ray(i:ι): X (.inl i)= F.atScale h Q (s.U (leg i)) -- direction
 bay(j:η): X (.inr j)+ F.atScale h Q (s.U (s.leaks j))=0

variable [Fintype η][DecidableEq η]

def Reflow.sales(F:Reflow ι η)(L:Side)(i j:Primary ι η):ℝ:= match i,j with -- row=i (old label)
 | Sum.inl i,Sum.inl j=> (F.U.symm (leg j)) i
 | Sum.inr _,Sum.inl _=>0
 | Sum.inl i,Sum.inr j=> sprintCost L * (F.leaks j i)
 | Sum.inr i,Sum.inr j=> if i=j then sprintCost L else 0

lemma economy_go (L:Side) (X:Primary ι η→ArcΦ) (F:ResolutionFrame ι) (s:Reflow ι η) (h Q:ℝ)(p:Energized F h Q X s) (i:Primary ι η):
    (∑ j:Primary ι η,s.sales L j i • X j)=F.enterBasis h Q i:=by
 let B:Coords ι→ₗ[ℝ] ArcΦ:= F.atScale h Q; let Z:=B.comp s.U.toLinearMap
 have he(x:Coords ι): (∑ i:ι, x i • X (Sum.inl i))= B (s.U x):=by rw [show B (s.U x)= Z x from rfl]; simp_rw [show ∀ i,X (.inl i)=Z (leg i) from p.ray]; exact congrFun (congrArg DFunLike.coe (columns_map Z)) x -- defeq
 change (∑ j:ι⊕η, _)= _; rw [Fintype.sum_sum_type]; cases i
 case inl i=>
    simp only [Reflow.sales,zero_smul,sum_const_zero,add_zero,enterBasis,Sum.elim_inl]; rw [he,s.U.apply_symm_apply]
 case inr i=>
    simp only [Reflow.sales,mul_smul,←smul_sum,ite_smul,zero_smul,sum_ite_eq',mem_univ,if_true, enterBasis,Sum.elim_inr]; rw [he,← smul_add,add_comm,p.bay]; exact smul_zero _


variable {X Y:BudgetPoint}{W κ q Q h T a b c:ℝ}{s:Reflow ι η}
lemma economical_bound (r:RepositoryRent F C K A L)(e:Economics F C K A L X Y κ q Q s) (j i : Primary ι η):
  |s.sales L j i| ≤ sprintCost L:=by
 rcases i with i|i
 · rcases j with j|j; exact ((norm_le_pi_norm _ j).trans (e.sail _)).trans (by rw [leg_norm,mul_one]; exact r.roll) -- tune
   exact le_trans (abs_zero.le) (sprint_pos L).le
 rcases j with j|j
 · change |sprintCost L * s.leaks i j| ≤ _; rw [abs_mul,abs_of_pos (sprint_pos _)]; exact mul_le_of_le_one_right (sprint_pos L).le (((norm_le_pi_norm (s.leaks i) j).trans (e.bek i)).trans r.offset)
 simp only [ Reflow.sales]; split_ifs; rw [abs_of_pos (sprint_pos _)]; exact le_trans abs_zero.le (sprint_pos L).le

abbrev rentInk (F:ResolutionFrame ι)(A q h T W κ:ℝ) (L: Side)(i:Primary ι η):ℝ:=W*κprobe mintR L h (A*q) T (κ:ℂ) (F.enterBasis h q i)

variable (R:RepositoryRent F C K A L) (t:Real.exp (-1) ≤ |κ|)(z: |κ| ≤ ε1)(H:1≤h)(w:|T| ≤ nullLoss L*q)(g:Stretch F C)(p:1≤A)(u:1≤K)(f:0<q)(l:q≤Q)(v:Q≤2*q)
include R g p u z f l H w
-- afford also relaxed to external budgets; Inspector actual for (rentInk etc.W). 
lemma rents_formula (e:Economics F C K A L X Y κ q Q s) (hW:|W|≤K)(i:Primary ι η):
 ∑ j:Primary ι η, |s.sales L j i| * F.rentInk A q h T W κ L j ≤ A*Q:=by
 let B:=basePay C; let x:=F.chiLoss L; let P₀:=F.pulseBase L; let U:=F.pulseHidden L C K A; let Z:=sprintCost L; let ε:=nullLoss L
 let G:=F.rentInk (η:=η) A q h T W κ L
 have χ:0<B:=by have ht:=zero_lt_one.trans_le g.large; unfold B basePay; positivity
 let hx:= F.chi_pos L; let hU:= accuracy_pos C K A g.large u p
 let yk:= null_pos L; have hZ:0<Z:= sprint_pos _; let hP:=receipt_pos; change 0<x at hx; have hp:0<P₀:= div_pos receipt_pos hx; have hu:0<U:= mul_pos hp (mul_pos hU yk)
 have hb:=zero_lt_one.trans_le p; let hK:=zero_lt_one.trans_le u
 have αk(j : ι): G (.inl j)≤ K*(B*x*q):=by
    refine (le_abs_self (W*_)).trans ?_; rw [abs_mul]; apply mul_le_mul hW (estimate_mint g f H z p w (leg j) (leg_norm j|>.le) R.acc) (abs_nonneg _) (zero_le_one.trans u) -- tune
 have u₀: P₀*x=receiptCost:=div_mul_cancel₀ _ hx.ne'
 change (∑ j:ι⊕η, _* G j) ≤ _; rw [Fintype.sum_sum_type]; cases i
 case inl i=>
    let y:=s.U.symm (leg i); have hz:‖y‖ ≤ P₀:= (e.sail _).trans (by rw [leg_norm,mul_one]); simp_rw [Reflow.sales,abs_zero,zero_mul,sum_const_zero,add_zero]
    have he:∀ j:ι, |y j| * G (.inl j) ≤ P₀*(K*(B*x*q)):=fun j=> (mul_le_mul_of_nonneg_left (αk j) (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ j).trans hz) (by positivity))
    refine (sum_le_sum (s:=univ) fun i _=> he i).trans ?_; rw [sum_const,nsmul_eq_mul,card_univ]; refine (le_of_eq (b:= startCost F C K*q) ?_).trans (mul_le_mul R.start l f.le hb.le); unfold startCost; change cι * _= cι * _*K*B*q; rw [←u₀]; ring
 case inr i=>
    change (∑ j:ι,|Z * s.leaks i j| * _ )+ _ ≤ _; rw [sum_eq_single i (s:=(univ:Finset η)) (f:=fun j:η=>|s.sales L (Sum.inr j) (Sum.inr i)| * G (.inr j))]; -- gen
    have he (j:ι): |Z * s.leaks i j| * G (.inl j) ≤ (Z*U)*(K*(B*x*q)):= (mul_le_mul_of_nonneg_left (αk j) (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right (by rw [abs_mul, abs_of_pos hZ]; exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (s.leaks i) _).trans (e.bek i)) hZ.le) (by positivity))
    have hi: G (.inr i) ≤ K*((A+1)*ε*q) := by
       apply le_trans (le_abs_self (W*_)); rw [abs_mul]; apply mul_le_mul hW (estimate_hidden f p w) (abs_nonneg _) hK.le
    rw [show s.sales L (.inr i) (.inr i)= Z from if_pos rfl,abs_of_pos hZ]; apply (add_le_add (sum_le_sum (s:=univ) fun i _=> he i) (mul_le_mul_of_nonneg_left hi hZ.le)).trans; rw [sum_const,nsmul_eq_mul,card_univ]; apply le_trans (Eq.le ?eq) (mul_le_mul R.spill l f.le hb.le)
    case eq =>
       change cι*(Z*U*(K*(B*x*q)))+_= (cι*receiptCost*accuracy C K A*K*B+K*(A+1))*(ε*Z)*q; rw [← u₀]; unfold U; change (cι)*(Z*(P₀*(accuracy C K A* ε))*(K*(B*x*q)))+_= _; ring
    all_goals simp_all [Reflow.sales]

include t v
local notation "δP" => headFine*chiLoss F L -- don't use binders below
-- Use income about predicted shape, extract a single normalization for all three/four questions, with NO allowance on momentum ghost from alphaPrice. All bounds an eventual uniform.
theorem corridor (x₀: |a|≤K)(x₁:|b|≤K)(x₂:|c|≤K)
   (ha:(mu L)^(4:ℕ)/4≤ Tune.qCorset X.threshold Y.threshold (L.val:ℝ))
   (hc:Tune.qCorset X.threshold Y.threshold (L.val:ℝ)≤4*mu L^(4:ℕ))
   (ip:Side)(Z:Primary ι η→ ArcΦ)
   (e:∀ i, InΦ (Z i)∧(F.colors ip).Eigenspace (Z i)∧ αPrice L h (A*q) T a b c (F.enterBasis h q i) (Z i) X Y (κ:ℂ)):
   ∃ s:Reflow ι η, Economics F C K A L X Y κ q Q s ∧ Energized F h Q Z s:=by
 let G:=F.atScale h Q; let V:=F.atScale h q; let U(i):= F.typical L X Y κ i*(q/Q); let ε:=accuracy C K A * nullLoss L; have he:= (f.trans_le l).ne'
 choose D d using fun i=> (LinearMap.mem_range.mp ((F.representation (Z i) h Q ip (f.trans_le l) H).1 ⟨(e i).1,(e i).2.1⟩))
 have hd(i) : G (D i) = Z i:= d i
 have hS(i:ι): ‖D (.inl i)- U i • leg i‖≤ ε:=by
    obtain ⟨a',b',c'⟩:= F.rates L X Y h κ q i
    let r:=F.typical L X Y κ i; have hh:G (U i • leg i)= r • V (leg i):=by unfold U G; rw [mul_smul,map_smul,F.ratio_scale h (leg i) q Q he]
    refine estimate_correction g f H z p w K u l _ _ (leg i) (leg_norm _|>.le) x₀ x₁ x₂ (by rw [show F.atScale h Q (D (.inl i))= _ from hd (.inl i)]; exact (e (.inl i)).2.2) ?_ ?_ ?_ -- gen
    · exact (congrArg Prod.fst hh).trans a'
    · exact (congrArg (fun x:ArcΦ=> x.2.1) hh).trans b'
    exact (congrArg (fun x:ArcΦ=> x.2.2) hh).trans c'
 have hT(i:η): ‖D (.inr i)‖≤ ε:=by
    have he:= estimate_correction (F:=F) (X:=X) (Y:=Y) (q:=q) g f H z p w K u l 0 (D (.inr i)) 0 (by simp) x₀ x₁ x₂ ?tag ?red ?blue ?spin; exact (sub_zero (D (.inr i))) ▸ he -- tune
    case tag=> rw [show F.atScale h Q _= _ from (hd (.inr i)),map_zero]; exact (e (Sum.inr i)).2.2
    all_goals simp [ζtap,ζVtap,ξtap]
 obtain ⟨u',q',k⟩:= inventory_neq (fun i:ι=> D (.inl i)) U ε (headFine * F.chiLoss L) hS (fun i=> (F.typical_bounds L X Y κ t z ha hc q Q f l v i).1) R.error (mul_pos headPos (F.chi_pos L))
 have hv(i:ι):u' (leg i)=D (.inl i):=by rw [show u' (leg i)= u'.toLinearMap _ from rfl, q']; exact columns_one ..
 have hh(x):‖u'.symm x‖≤ F.pulseBase L *‖x‖ := by apply le_trans (k x); apply Eq.le; unfold pulseBase receiptCost; rw [div_div] -- tune which orientation/nsmul
 let Z':=Reflow.mk u' (fun i:η=> -(u'.symm (D (.inr i)))); refine ⟨Z',⟨fun i=> hv i ▸ hS i,hh,fun j=>?_⟩,⟨?_,?_⟩⟩ -- ▸ orientation
 · change ‖- _‖≤_; rw [norm_neg]; exact (hh _).trans (mul_le_mul_of_nonneg_left (hT j) (div_pos receipt_pos (F.chi_pos L)).le)
 · intro i; change _=G (u' _); rw [hv]; exact (hd _).symm
 intro i; change _ + G (u' (- _)) =0; rw [map_neg,LinearEquiv.apply_symm_apply,map_neg,hd]; exact add_neg_cancel _

end ResolutionFrame
end ShapeLab
end YM.CF.QuadClock
