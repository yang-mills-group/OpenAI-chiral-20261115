import YM.CF.Wray.Pose
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Iva Eire Font
variable (F:Pilot)(v:Stake.Isle)(w:Hos S n)
local notation "ζ"=>radiusB x
local notation "L_"=> R.L
local notation "C₀"=> Single (mid N B)
-- core prices.activation. net exp can pay also any PP pressure by renormalizing Pose.Bore.Se
variable {σ:ℝ}(Q₀:Pail.Payment R σ)(Z:Pluck R)
lemma totems (u:0≤ v.oath) : Branch.ledgerV (monuments (x:=x) w Z.r2 v.oath) ≤ (w.val.dome (Z.r2*radiusB x)).card*((countH (ζ+1):ℝ)^2*v.oath):=by
 have he(i:Site (Domain N B)):=lens_u (N:=mid N B) i (ζ+1) u
 unfold Branch.ledgerV monuments; simp only [Finset.sum_apply]; simp_rw [sum_comm (s:=(univ:Finset C₀)) (t:=(w.val.dome (Z.r2*radiusB x)))]; -- risk
 simpa only [Branch.ledgerV,sum_const,nsmul_eq_mul] using sum_le_sum (s:=w.val.dome (Z.r2*ζ)) (fun i _=> (he i)) -- tune
-- convert counts
abbrev artL(r:ℕ)(x:ℝ):ℕ:=4*(r*radiusB x+r*radiusB x+1)^4
lemma dome_s(r:ℕ): (w.val.dome (r*radiusB x)).card ≤ artL r x*w.val.shares:=by refine (Corona.halo_size _ (r*radiusB x)).trans ((Nat.mul_le_mul_right _ (Work.E01.place_card w.val)).trans ?_); apply Eq.le; unfold artL; ac_rfl
abbrev heightC(P:Patch)(v b H W:ℝ)(k j l:ℕ)(x:ℝ):=steel k (b*(Esti.dusk j P*plow x^4)+(artL l x:ℝ)*W)+H^2*steel k ((artL l x:ℝ)* ((countH (radiusB x+1):ℝ)^2*v))
lemma heightT{B:ℝ→ℝ}(h:BoreP B)(v':ℝ)(y p:ℝ): BoreP fun x=> heightC R v' y p (B x) k j l x:=by
 have he: BoreP fun x=>(artL l x:ℝ):=by unfold artL; push_cast; let t:= (BoreP.still (l:ℝ)).grip BoreP.radius_c; exact (BoreP.still _).grip ((((t.join t).join (BoreP.still _)).self _))
 unfold heightC steel; exact (((BoreP.still _).grip (((BoreP.still _).grip ((BoreP.still _).grip (BoreP.relB.self 4))).join (he.grip h))).join ((BoreP.still _).grip ((BoreP.still _).grip (he.grip ((boring.self 2).grip (BoreP.still _))))))
lemma canon(H:ℝ)(p:0≤H)(A:Wages)(u:0≤A.burn)(hp:0≤v.oath)(ht:S.patch=R): joinV (stake H) (purpleP v A w k j Q₀ x F Z)≤ steel k (octA w F x R.L)* Real.exp (heightC R v.oath Q₀.glow H A.burn k j Z.r2 x* ↑w.val.shares):=by
 let O:= octA w F x R.L; let z:= naked (steel k O) (n:= LeanV C₀); let h:=heightC R v.oath Q₀.glow H A.burn k j Z.r2 x; let U:=Iva.cull k (monuments (x:=x) w Z.r2 v.oath) (Q₀.glow*Esti.latticeFieldEstimates w.val j x+(w.val.dome (Z.r2*ζ)).card*A.burn); have hz:0≤U:=cull_p _ _ (fun i j=>by unfold monuments; simp only [Finset.sum_apply]; exact sum_nonneg fun u _=> gro_p _ hp _ u i j) (add_nonneg (mul_nonneg Q₀.hi (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) u)) -- sum application defeq?
 let c:ℝ:= w.val.shares
 have hg:joinV (stake H) U ≤ h*c:=by
    unfold U; rw [stars,Esti.dust,ht]; have hK:0 ≤ (k+1:ℝ):=by positivity
    have hx:( (w.val.dome (Z.r2*radiusB x)).card:ℝ)≤(artL Z.r2 x:ℝ)*c:=by unfold c; exact_mod_cast dome_s (x:=x) w Z.r2
    have hc: Branch.ledgerV (monuments (x:=x) w Z.r2 v.oath) ≤ ((artL Z.r2 x:ℝ)*c)*((countH (ζ+1):ℝ)^2*v.oath):= (totems v w Z hp).trans (mul_le_mul_of_nonneg_right hx (mul_nonneg (sq_nonneg _) hp)); exact (add_le_add (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_right hx u) _) hK) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK) (sq_nonneg _))).trans_eq (by unfold h heightC steel c; ring) -- add_le...
 have he:0 ≤ z:=nak_r (foot_r k _ (Real.exp_pos _).le); have hv: joinV (stake H) z=steel k O:=by unfold z naked; rw [joined]; simp [stake]
 have ht':=turnS (stokes p) z (Rue.saber U 0) he (saberZ hz); have h1:=ht'; rw [hv] at h1; exact h1.trans (mul_le_mul_of_nonneg_left ((Rue.peony 0 hz (stokes p)).trans (by rw [pow_zero,mul_one]; exact Real.exp_monotone hg)) (foot_r _ _ (Real.exp_pos _).le))
lemma loomH{Y:ℝ→ℝ}(p:Lento Y)(a:ℝ)(u:0<a)(T:Side):∀ᶠ x in atTop, |Y x| ≤ Real.exp (scaleM G5 T a x):=by
 filter_upwards [lentA T Y p 0 a u 1 zero_le_one] with x h; simpa [scaleM] using (h 1 1 (by simp)) -- uses K.
abbrev eventB(P:Patch)(F:Pilot)(x:ℝ):ℝ:=scaleM SU.group P.L (F.penalty/64) x
lemma tier_p{A:ℝ→Wages} (P:ℝ)(v':ℝ)(t:ℕ)(h:BoreP (fun x=>(A x).burn)):∀ᶠ x in atTop, heightC R v' P c (A x).burn k j t x ≤ eventB R F x:=by filter_upwards [loomH ((heightT (k:=k) (j:=j) (l:=t) (R:=R) h v' P c).lento_w) _ (div_pos F.earn (by norm_num : 0 < (64:ℝ))) R.L] with x h; exact (le_abs_self _).trans (Real.exp_le_exp.mp ((le_abs_self _).trans h))
lemma compass(k j:ℕ)(H:ℝ)(p:0 ≤ H)(L:Tun v Z F σ)(hz:0 ≤ v.oath):∀ᶠ x in atTop,∀ {N P B:Side}(S:StepData (Domain N B) (Domain P B)), S.patch=R→∀ (n:ℕ)(w:Hos S n), joinV (stake H) (purpleP v (paidL v L.K₁ L.K₂ k x (F.hat R x)) w k j L.book x F Z)≤Real.exp (-2*eventB R F x* ↑w.val.shares):=by
 filter_upwards [tier_p (R:=R) (A:=fun x=>paidL v L.K₁ L.K₂ k x (F.hat R x)) (c:=H) F L.book.glow v.oath Z.r2 (k:=k) (j:=j) (tall_a v L.K₁ L.K₂ k|>.fog) -- tune
 ,loomH (Y:=fun _=>(k+1:ℝ)) (Lento.sun _) (F.penalty/64) (div_pos F.earn (by norm_num)) R.L] with x h t N P B S u n w
 let U:= eventB R F x; let A:= paidL v L.K₁ L.K₂ k x (F.hat R x); let Y:=heightC R v.oath L.book.glow H A.burn k j Z.r2 x; let z:ℝ:= w.val.shares; have hz':0< z:= Nat.cast_pos.mpr (vase_d S w.val ▸ card_pos.mpr w.property.1) -- tune
 have ht:0≤U:=mul_nonneg (div_nonneg F.earn.le (by norm_num)) (sq_nonneg _)
 apply (canon (x:=x) F v w L.book Z H p A (flee v L.K₁ L.K₂ k x _|>.pos) hz u).trans; unfold steel; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_abs_self _).trans t) (Real.exp_pos _|>.le)) ((Real.exp_pos _).le)).trans; change Real.exp U*octA w F x R.L * Real.exp (Y*z) ≤ _; rw [octA,←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
 have he: 1 ≤ z:=by unfold z; exact_mod_cast (show 1 ≤ w.val.shares from Nat.pos_of_ne_zero (by intro p; unfold z at hz'; rw [p] at hz'; norm_num at hz'))
 change Y≤ U at h; rw [show -F.penalty/16*(Scales.p G5 R.L x)^2*(w.val.shares:ℝ)=-4*(U*z) from by unfold U z eventB scaleM; ring]; change U+ -4*(U*z)+Y*z≤ -2*U*z; nlinarith only [mul_le_mul_of_nonneg_right h hz'.le,mul_le_mul_of_nonneg_left he ht]
end YM.CF.Wray
