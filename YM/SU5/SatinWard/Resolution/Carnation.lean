import YM.SU5.SatinWard.Resolution.Duette
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

variable (i:minusSpin)(j:plusSpin)
open _root_.YM.Regis.Circuit.SpringDay.Spring
local notation "ph"=> CF.Papyrus.Franc.SatinForce.Flash (i:SpinIdx) (j:SpinIdx)
local notation "Uh"=> tradeW (i:SpinIdx) (j:SpinIdx)
lemma homYouth (a:Axis){z:ℝ}(p:z≠0){x:Gaia}(h:x≠0): fettle a (z • x) = (((z:ℂ)^3)⁻¹)* fettle a x:=by
 have hx: z • x≠0:=smul_ne_zero p h; have hy:= norm_pos_iff.mpr h; unfold fettle; rw [Maxwell.first_Green hx,Maxwell.first_Green h, PiLp.smul_apply,norm_smul, Real.norm_eq_abs,mul_pow,sq_abs]; push_cast; rw [smul_eq_mul]; push_cast; field_simp
lemma homWing {z:ℝ}(h:z≠0){x:Gaia}(p:x≠0): ph (z•x)= ((z:ℂ)^3)⁻¹*ph x:=by unfold CF.Papyrus.Franc.SatinForce.Flash; simp_rw [homYouth _ h p]; rw [mul_sum]; exact sum_congr rfl (fun a _=>mul_left_comm ..)
lemma brightWay (d:Gaia)(p:d ≠0): ContDiffAt ℝ 1 ph d:=by
 have he(a:Axis): ContDiffAt ℝ 1 (fettle a) d:=by
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((gradGradientSmooth p a).of_le (by norm_num)))
 unfold CF.Papyrus.Franc.SatinForce.Flash; exact ContDiffAt.sum fun x _=> contDiffAt_const.mul (he x)
 
lemma cradle {Q:ℝ}:∃ a:ℝ,1≤a ∧ (∀ x∈plinth Q, ‖ph x‖ ≤ a)∧∀ x∈plinth Q,∀ y∈plinth Q, ‖ph x-ph y‖≤ a*‖x-y‖:=by
 let f:=ph; have hp:=peak Q
 have h(x:Gaia)(y:x∈plinth Q):ContDiffAt ℝ 1 f x:= brightWay i j x (norm_ne_zero_iff.mp (by have t:= ((peak_iff ..).mp y).1; linarith))
 obtain ⟨b,t⟩:= hp.bddAbove_image (f:=fun x=> ‖f x‖) (fun x y=> (h _ y).continuousAt.norm.continuousWithinAt)
 have he:LocallyLipschitzOn (plinth Q) f:=by intro x hx; obtain ⟨K,S,q,H⟩:=(h x hx).exists_lipschitzOnWith; exact ⟨K,S,nhdsWithin_le_nhds q,H⟩
 obtain ⟨C,H⟩:=he.exists_lipschitzOnWith_of_compact hp
 let D':= max b (max (C:ℝ) 1); have hd:(C:ℝ) ≤ D':= (le_max_left ..).trans (le_max_right ..); refine ⟨D',(le_max_right ..).trans (le_max_right ..),fun x u=> (t ⟨x,u,rfl⟩).trans (le_max_left ..),fun x u y v=> ?_⟩; exact (by simpa only [←dist_eq_norm] using H.dist_le_mul x u y v :‖f x-f y‖ ≤ (C:ℝ)*‖x-y‖) |>.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) -- args

variable (Q μ:ℝ)(v:0≤μ)
include H v
lemma sharpSpin : ∃ C:ℝ,1≤C ∧ ∀ (R:ℝ)(h:1≤R)(e:μ ≤ R)(x:Cover)(d:Gaia)(a:2≤‖d‖)(y:‖d‖≤Q)(l:‖patchF x R -d‖ ≤ μ/R), ‖ph d‖ ≤ C ∧
    ‖(R:ℂ)^3*Uh x -ph d‖ ≤ C/R:=by
 obtain ⟨a0,h,a,t⟩:= cradle i j (Q:=Q+1); obtain ⟨w,u,x⟩:= H.W_theta i.val j.val [] i.property j.property; let C:= a0*(μ+1) + 16*w; have hC:a0 ≤ C:=by unfold C; nlinarith only [u,mul_nonneg (zero_le_one.trans h) v]
 refine ⟨C,h.trans hC,fun R h e X d p q v=>?_⟩ -- h shadow
 let Z:= patchF X R; obtain ⟨δ,r⟩:= shrink d Z p q h e v; have hz:0<R:=by linarith
 have he:0<‖Z‖:=by linarith only [((peak_iff ..).mp r).1]
 have b:=norm_pos_iff.mp he
 have hr:= scouts r hz; let φ:= rally X; have u0:0<φ:=by linarith
 have θ:X ≠ 0:=by contrapose! u0; subst X; exact le_of_eq (show ‖shaftX 0‖ = _ from by rw [show shaftX 0=0 from (by funext i; change ((0:ℤ):ℝ) = 0; simp), norm_zero])
 have hx: ‖Uh X -ph (scape X)‖≤ w/φ^4:=x X θ
 have hx': (R:ℂ)^3*ph (scape X)=ph Z:=by rw [show scape X=R • Z from (smul_inv_smul₀ hz.ne' _).symm, homWing i j hz.ne' b, ←mul_assoc,mul_inv_cancel₀ (by exact pow_ne_zero _ (by exact_mod_cast hz.ne')),one_mul]
 let L:=a0*μ; let E:=ph; let Z₁:=(R:ℂ)^3*Uh X; have hu:‖Z₁-E Z‖≤(16*w)/R:=by
    unfold Z₁ E; rw [←hx',←mul_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hz.le]; refine (mul_le_mul_of_nonneg_left hx (pow_nonneg hz.le 3)).trans ?_
    rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos u0 _) hz]; change R ≤2*φ at hr; nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz.le hr 4) u.le]
 have hw:‖E Z-E d‖≤L/R:= (t _ r _ δ).trans ((mul_le_mul_of_nonneg_left v ((zero_le_one.trans ‹1≤a0›))).trans_eq (by unfold L; ring))
 exact ⟨(a _ δ).trans hC, (norm_sub_le_norm_sub_add_norm_sub _ (E Z) _).trans ((add_le_add hu hw).trans (by unfold C L; rw [←add_div]; apply div_le_div_of_nonneg_right _ hz.le; linarith only [‹1≤a0›]))⟩

local notation "FA"=> CF.Papyrus.Franc.SatinForce.Flash
noncomputable abbrev fieldKid (X:Gaia)(i:juniorKid)(j:seniorKid):ℂ:= if i.2=j.2 then FA (i.1:SpinIdx) (j.1:SpinIdx) X else 0
noncomputable abbrev kindDU (d:Gaia)(i j:principalKid):ℂ:= fieldKid d j.2 i.1 * fieldKid d i.2 j.1
omit H v in
lemma mirrorX (i:juniorKid)(j:seniorKid){x:Gaia}(p:x≠0):fieldKid (-x) i j= -fieldKid x i j:=by
 unfold fieldKid; split_ifs; · rw [← neg_one_smul ℝ x, homWing i.1 j.1 (by norm_num) p]; norm_num
 simp
lemma shadower (i:juniorKid)(j:seniorKid):∃ A:ℝ,0 ≤ A ∧ ∀ (x y:Cover)(d:Gaia)(R:ℝ), Addressing x y d μ R Q→ Disp R A ((R:ℂ)^3 *costSong (x-y) i j) (fieldKid d i j):=by
 obtain ⟨A,f,u⟩:= sharpSpin H i.1 j.1 Q μ v; have ha:0≤A:=zero_le_one.trans f; refine ⟨A,ha,fun x y d R t=>?_⟩; unfold costSong fieldKid; split_ifs; · obtain ⟨k,v⟩:= u R t.pLease (by linarith only [t.lap]) _ d t.area t.sizes t.meters; exact ⟨ha,k,v⟩
 rw [mul_zero]; exact (Disp.zero R).mono ha (zero_le_one.trans t.pLease)
omit H v
lemma dMinus {x y:Cover}{d:Gaia}{μ R Q:ℝ}(h: Addressing x y d μ R Q): Addressing y x (-d) μ R Q:=⟨h.r₀,h.lap, by rw [norm_neg]; exact h.area, by rw [norm_neg]; exact h.sizes, by
    unfold patchF; rw [scape_sub,smul_sub,sub_neg_eq_add]; refine le_trans ?_ h.meters; unfold patchF; rw [scape_sub,smul_sub]; rw [←norm_neg ( (R⁻¹ • scape y-R⁻¹ • scape x)+d), show -( (R⁻¹ • scape y-R⁻¹ • scape x)+d)=R⁻¹ • scape x-R⁻¹ • scape y-d from by abel]⟩
include H v
lemma dContour : ∃ A:ℝ,0≤A∧∀ (x y:Cover)(d:Gaia)(R:ℝ),Addressing x y d μ R Q→∀ (i j:principalKid), Disp R A ((R:ℂ)^6 * price₂ (x-y) i j) (kindDU d i j):=by
 choose f e v using (fun i:juniorKid×seniorKid=> shadower H Q μ v i.1 i.2); let D:=∑ j, f j; have hD:0 ≤ D:=sum_nonneg fun i _=> e i
 refine ⟨3*D*D,by positivity, fun x y d R Q i j=>?_⟩; have t:=Q.pLease; have hd: d ≠ 0:= norm_pos_iff.mp (by linarith only [Q.area])
 let ν₁:=(j.2,i.1); let ν₂:=(i.2,j.1); unfold kindDU price₂; rw [show -(x-y)=y-x from by abel]
 let z(i:juniorKid×seniorKid):f i ≤D:=single_le_sum (fun i _=> e i) (mem_univ _)
 have hm:= (((v ν₁ y x (-d) R (dMinus Q)).mono (z _) (zero_le_one.trans t)).times ((v ν₂ x y d R Q).mono (z _) (zero_le_one.trans t)) t).increase (-1); rw [mirrorX _ _ hd,norm_neg, norm_one, one_mul, neg_one_mul, neg_one_mul, neg_mul, neg_neg] at hm
 refine (Eq.subst (motive:=fun z=> Disp R (3*D*D) z (kindDU d i j)) ?_ hm); unfold ν₁ ν₂; dsimp only; ring
noncomputable def bouquet (i:Axis)(A:Op SU.Slot)(j:Axis)(B:Op SU.Slot)(d:Gaia):ℂ:=∑ k:principalKid,∑ m:principalKid, ordinaryW i A k * ordinaryW j B m * kindDU d k m
-- tariff.D comparator fixed A before u, all d. Bounded.F♭.Quantity.Could multiply later.
lemma sketchPay (i:Axis)(A:Op SU.Slot)(j:Axis)(B:Op SU.Slot):∃ C:ℝ,0≤ C∧∀ (x y:Cover)(d:Gaia)(R:ℝ), Addressing x y d μ R Q→ Disp R C ((R:ℂ)^6 * duet i A j B (x-y)) (bouquet i A j B d):=by
 obtain ⟨K,e,f⟩:=dContour H Q μ v; let X(k m):=ordinaryW i A k*ordinaryW j B m; let E(k):= ∑ m:principalKid,‖X k m‖*K; refine ⟨∑k:principalKid,E k,sum_nonneg fun i _=> sum_nonneg (fun j _=>by positivity),fun x y d R q=>?_⟩; unfold duet bouquet; rw [mul_sum]; apply Disp.SumD; intro k hk; rw [mul_sum]; apply Disp.SumD; intro m _; rw [mul_left_comm]; exact (f x y d R q k m).increase _
#print axioms sketchPay
omit H v
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

