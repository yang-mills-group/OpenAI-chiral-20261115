import GaugeFieldConstruction.Lustre
import GaugeFieldConstruction.Bronco
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Py Trees Hake FlightFlux TableF Boom Axon Lenten.ModuleB Flot Taxi
open HarmP
namespace BellPrice
open Lenten FlightFlux Fluxim
lemma bspokes (a:ℝ)(L:Side)(k:ℕ)(A:ℝ) (c:ℝ)(h:0<c):∀ᶠ x:ℝ in atTop,∀ (N P: Side)(S:StepData N (More P))(Y:BudgetPoint)(X:Scree.Hub P),Y.threshold=temp (x+a) → Y.B≤2*radiusB x → S.patch.L=L → Short S Y X.val.2 → A*Y.threshold*(1+(bitU Y X:ℝ))^k ≤ c:=by
 let K:=1+24*(L.val:ℝ); let V(x:ℝ):=(1+(radiusB x:ℝ)); let p(x):=K*V x
 filter_upwards [Heir.reserve (K:=K) (y:=p) (Eventually.of_forall (fun x=>⟨by unfold p V K; positivity,le_rfl⟩)) a c k h |A|] with x v N P S Y X t u w sh
 have hY:0 ≤Y.threshold:=Y.threshold_pos.le
 have hX:bitU Y X≤ 4*(6*(1+radiusB x)*L.val):= Nat.mul_le_mul_left 4 (w ▸ Heir.width_le sh u)
 have hx:1+(bitU Y X:ℝ) ≤ p x:=by
    have he:(bitU Y X:ℝ) ≤4*(6*V x*L.val):=by unfold V; exact_mod_cast hX
    apply (add_le_add_right he _).trans; unfold p K V; nlinarith only [Nat.cast_nonneg (α:=ℝ) (radiusB x)] -- tune V
 refine (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self A) hY) (pow_le_pow_left₀ (by positivity) hx _) (by positivity) (by positivity)).trans ?_; rw [t]; exact v.le
lemma stanch(s:ℝ)(t:0<s)(L:Side)(x':ℝ) :∀ᶠ x in atTop,∀ (N P: Side)(S:StepData N (More P))(Y:BudgetPoint)(X:Scree.Hub P),Y.threshold=temp (x+x') → Y.B≤2*radiusB x → S.patch.L=L → Short S Y X.val.2 → Stakes s (αN L) X Y:=by
 let K:=waist 1; let b:=αN L; have hx:0<b:=α_pos _; let D:=s*b; have hp:0≤D:=by unfold D; positivity
 have ht:0≤K:=waist_pos _ zero_le_one
 let W:=K*(s*b^2)*2; let A:=ScoreWa SU.group
 have hA:0≤A:=ScoreWa_pos
 let K':=(K*(4*s*b)+A*(4*s*b))*D; have hu:0≤ K':=by unfold K'; positivity
 filter_upwards [bspokes x' L 1 (K*D) (b^3) (by positivity),bspokes x' L 2 W (b^3) (by positivity),bspokes x' L 1 K' (b^3) (by positivity)] with x h h₀ h₁ N P S Y X v u w sh
 let T:=bitU Y X; have hp:0 < Y.threshold:=Y.threshold_pos; have hs: (T:ℝ)≤ 1+T:=le_add_of_nonneg_left zero_le_one
 constructor
 · unfold αSpring; rw [waist_h]; refine le_trans ?_ (h N P S Y X v u w sh); rw [pow_one]; change K*(D*_*_) ≤_; rw [←mul_assoc,←mul_assoc]; exact mul_le_mul_of_nonneg_left hs (by positivity)
 · unfold tideV; rw [waist_h]; change K* ((s*b^2)*Y.threshold*(1+2*(T:ℝ))*T) ≤ _
   calc
   _ ≤ K*((s*b^2)*Y.threshold*(2*(1+(T:ℝ)))*(1+T)) := by gcongr; · linarith only
   _=W*Y.threshold*(1+(T:ℝ))^2:=by unfold W; ring
   _≤ _:=h₀ _ _ S Y X v u w sh
 unfold αSpring strainΦ; rw [waist_h]; calc
    _ = K'*Y.threshold*(T:ℝ) := by unfold K' K A D b T; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hs (mul_nonneg hu hp.le)).trans (by simpa only [pow_one] using h₁ _ _ S Y X v u w sh)
private lemma zax_m(a:ℕ)(b:ℝ)(J:ℕ)(A H κ ε C:ℝ) (v:ℕ) : Zax a b J A H κ ε C v=Zax a b J A H κ ε 1 v*C:=by unfold Zax; ring
lemma zearly (L:Side)(A r G K v:ℝ)(p:0<r)(u:0<v):∃ ε > (0:ℝ),∀ e> (0:ℝ), e≤ε →∀ᶠ x:ℝ in atTop,∀ C:ℝ,0 ≤ C → Zax (radiusB x) r 5 (A*followV [] L) G K e C 3 ≤ v*C :=by
 let X:= lorp 0 (5+90) 3 (population*(A*followV [] L)); let P:= Nexus₁ 6 K; let T:= Boot (k:=6) K
 let Y:= |X*P|+1; have ht:0<Y:=by unfold Y; positivity
 refine ⟨(v/2)/Y,by positivity,fun e hE he=>?_⟩
 have hx: X*(P*e) < v:=by
    rw [←mul_assoc]; exact lt_of_le_of_lt (b:=v/2) (le_trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) hE.le) (by have hu:=(le_div_iff₀ ht).mp he; rw [mul_comm]; exact hu)) (half_lt_self u)
 let g(x:ℝ):= (Real.exp (-(r/2)*(radiusB x:ℝ)))*X*T
 have he:Tendsto g atTop (𝓝 0):=by
    have ht: Tendsto (fun x:ℝ=> (radiusB x:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
    simpa only [g,Function.comp_apply,zero_mul] using (Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (show -(r/2)<0 from by linarith))).mul_const X |>.mul_const T
 filter_upwards [he.eventually (ge_mem_nhds (sub_pos.mpr hx))] with x h C u; rw [zax_m]; apply mul_le_mul_of_nonneg_right _ u; unfold Zax; dsimp only; rw [mul_one,mul_one]; change X*(P*e)+g x≤_; linarith only [h]
open Planned.PrimaryIntegral295 Carrier
-- limit testing.Cost δ. uniform c ratio.
lemma μpre (L:Side)(i:ℕ)(a b:BudgetPoint)(h:a.threshold ≤ 2*b.threshold) : let t:=unitStep L ^(i+1)*2; 0 ≤ Λgear i a.threshold b.threshold L ∧ Λgear i a.threshold b.threshold L ≤ t:=by
 intro t
 have hp:0< a.threshold:=a.threshold_pos; have ht:0 < b.threshold:=b.threshold_pos
 have he:0 ≤ unitStep L ^ (i+1):=by have h:=unitStep_pos L; positivity
 exact ⟨mul_nonneg he (div_pos hp ht).le,mul_le_mul_of_nonneg_left ((div_le_iff₀ ht).mpr h) he⟩
-- consequences of tour shrink. barge + condition. P attitudes ordinary.
lemma barge_cap (L:Side):∃ W:ℝ,1 ≤ W∧∀ (p q:BudgetPoint),p.threshold ≤2*q.threshold →∀ t:ℝ,0≤t→bargeDue p q L t ≤ W*t:=by
 let B:=unitStep L^(1+1)*2; let C:=unitStep L^(2+1)*2; let v:=αN L; let K:=mintPay (caboose*16); let V:=B*B+B*C+(K+v^3*(B*(50*K)))+1; have hx:0≤K:=mT_non _ (mul_nonneg cab_pos.le (by positivity)); have hb:0 < v:=α_pos L; have hC:0 < C:=mul_pos (pow_pos (unitStep_pos _) _) (by positivity); have hB:0 < B:=mul_pos (pow_pos (unitStep_pos _) _) (by positivity)
 refine ⟨V,le_add_of_nonneg_left (by positivity), fun a b p t ht=>?_⟩; let q:=Λgear 1 a.threshold b.threshold L; let w:=Λgear 2 a.threshold b.threshold L
 obtain ⟨x,y⟩:= μpre L 1 a b p; obtain ⟨r,s⟩:= μpre L 2 a b p;
 calc
    _ ≤ B*B*t+B*C*t+(t*K+v^3*(B*(50*K*t))) := by change q*q*t+q*w*t+(t*K+v^3*(q*(50*K*t))) ≤_; refine add_le_add (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul y y x hB.le) ht) (mul_le_mul_of_nonneg_right (mul_le_mul y s r hB.le) ht)) (add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right y (by positivity)) (by positivity)) _)
    _= V*t- t:=by unfold V; ring
    _≤ _:=sub_le_self _ ht
end BellPrice
end YM.CF.Oath
end
