import YM.SU5.SatinWard.Resolution.Stadium
import YM.SU5.SatinWard.Resolution.Sampler
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
-- annulus and smooth receipts. moment pair.
def plinth (R:ℝ):Set Gaia := Metric.closedBall 0 R ∩ {x| 1≤ ‖x‖}
lemma peak (R:ℝ): IsCompact (plinth R):=(isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
lemma peak_iff (x:Gaia)(R:ℝ): x ∈ plinth R ↔ ‖x‖∈Set.Icc 1 R:=by simp [plinth,and_comm]
-- homogeneity. borrowed Thin/Avalanche/Overpass
private lemma homG (a b i j:Axis) {z:ℝ}(h:0<z){x:Gaia}(p:x≠0): bareCurl a b i j (z•x)=(z^4)⁻¹*bareCurl a b i j x:=by
 have u:z•x≠0:=smul_ne_zero h.ne' p
 have he i j : Maxwell.grad i (Maxwell.grad j Maxwell.Green) (z • x)= (z^4)⁻¹ * Maxwell.grad i (Maxwell.grad j Maxwell.Green) x := by rw [Maxwell.second_Green u, Maxwell.second_Green p]; simp only [PiLp.smul_apply,norm_smul,Real.norm_of_nonneg h.le,smul_eq_mul]; have hv:= norm_pos_iff.mpr p; field_simp
 unfold Maxwell.bareCurl; simp only [Pi.sub_apply,Maxwell.Bare.opp_grad p,Maxwell.Bare.opp_grad u,he, mul_sub,mul_ite,mul_zero]
lemma diagSub (d:Gaia)(f:d≠0):ContDiffAt ℝ 1 (specter F D) d:= Complex.ofRealCLM.contDiff.contDiffAt.comp d ((Maxwell.Bare.curl_diff f _ _ _ _).of_le (by norm_num))
lemma homF {z:ℝ}(h:0<z){x:Gaia}(p:x≠0): specter F D (z•x)= ((z:ℂ)^4)⁻¹*specter F D x:=by unfold specter; rw [homG _ _ _ _ h p]; push_cast; rfl
lemma housing {Q:ℝ}:∃ a:ℝ,1≤a ∧ (∀ x∈plinth Q, ‖specter F D x‖ ≤ a)∧∀ x∈plinth Q,∀ y∈plinth Q, ‖specter F D x-specter F D y‖≤ a*‖x-y‖:=by
 let f:=specter F D; have hp:=peak Q
 have h(x:Gaia)(y:x∈plinth Q):ContDiffAt ℝ 1 f x:= diagSub F D x (norm_ne_zero_iff.mp (by have t:= ((peak_iff ..).mp y).1; linarith))
 obtain ⟨b,t⟩:= hp.bddAbove_image (f:=fun x=> ‖f x‖) (fun x y=> (h _ y).continuousAt.norm.continuousWithinAt)
 have he:LocallyLipschitzOn (plinth Q) f:=by intro x hx; obtain ⟨K,S,q,H⟩:=(h x hx).exists_lipschitzOnWith; exact ⟨K,S,nhdsWithin_le_nhds q,H⟩
 obtain ⟨C,H⟩:=he.exists_lipschitzOnWith_of_compact hp
 let D':= max b (max (C:ℝ) 1); have hd:(C:ℝ) ≤ D':= (le_max_left ..).trans (le_max_right ..); refine ⟨D',(le_max_right ..).trans (le_max_right ..),fun x u=> (t ⟨x,u,rfl⟩).trans (le_max_left ..),fun x u y v=> ?_⟩; exact (by simpa only [←dist_eq_norm] using H.dist_le_mul x u y v :‖f x-f y‖ ≤ (C:ℝ)*‖x-y‖) |>.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) -- args
abbrev patchF (O:Cover)(R:ℝ) := R⁻¹ • scape O
lemma scouts {O: Cover}{R:ℝ} {D:ℝ}(b:patchF O R∈ plinth D)(g:0<R): R ≤ 2*rally O:=by
 let s:=scape O; let B:=‖s‖; have h:0≤rally O:=norm_nonneg _
 have he:scape O= R • patchF O R:=(smul_inv_smul₀ g.ne' _).symm
 calc R ≤ ‖scape O‖:=by rw [he,norm_smul,Real.norm_of_nonneg g.le]; exact le_mul_of_one_le_right g.le ((peak_iff ..).mp b).1
      _ ≤ _ := Onyx.moor_z .. -- dot
lemma shrink (x y:Gaia){R u A:ℝ} (p:2≤‖x‖)(q:‖x‖ ≤ A)(h: 1 ≤ R)(w:u ≤ R)(g:‖y-x‖ ≤ u/R): x ∈ plinth (A+1) ∧ y ∈ plinth (A+1):=by
 have hk:u/R ≤ 1:=(div_le_one (by linarith)).mpr w; have hq:=g.trans hk; rw [peak_iff,peak_iff]; have hx:=abs_norm_sub_norm_le y x; exact ⟨⟨by linarith,by linarith⟩,⟨by linarith only [(abs_le.mp (hx.trans hq)).1,p],by linarith only [(abs_le.mp (hx.trans hq)).2,q]⟩⟩
variable (Q μ:ℝ)(v:0≤μ)
include H v
lemma sharpDisp : ∃ C:ℝ,1≤C ∧ ∀ (R:ℝ)(h:1≤R)(e:μ ≤ R)(s:ℕ)(x:Cover)(d:Gaia)(a:2≤‖d‖)(y:‖d‖≤Q)(l:‖patchF x R -d‖ ≤ μ/R), ‖specter F D d‖ ≤ C ∧
    ‖(R:ℂ)^4*wObj (W s) F D x -specter F D d‖ ≤ C/R:=by
 obtain ⟨a0,h,a,t⟩:= housing F D (Q:=Q+1); obtain ⟨w,u,x⟩:= H.W_price F D []; let C:= a0*(μ+1) + 32*w; have hC:a0 ≤ C:=by unfold C; nlinarith only [u,mul_nonneg (zero_le_one.trans h) v]
 refine ⟨C,h.trans hC,fun R h e s X d p q v=>?_⟩ -- h shadow
 let Z:= patchF X R; obtain ⟨δ,r⟩:= shrink d Z p q h e v; have hz:0<R:=by linarith
 have he:0<‖Z‖:=by linarith only [((peak_iff ..).mp r).1]
 have b:=norm_pos_iff.mp he
 have hr:= scouts r hz; let φ:= rally X; have u0:0<φ:=by linarith
 have θ:X ≠ 0:=by contrapose! u0; subst X; exact le_of_eq (show ‖shaftX 0‖ = _ from by rw [show shaftX 0=0 from (by funext i; change ((0:ℤ):ℝ) = 0; simp), norm_zero])
 have hx: ‖wObj (W s) F D X -specter F D (scape X)‖≤ w/φ^5:=x s X θ
 have hx': (R:ℂ)^4*specter F D (scape X)=specter F D Z:=by rw [show scape X=R • Z from (smul_inv_smul₀ hz.ne' _).symm, homF F D hz b, ←mul_assoc,mul_inv_cancel₀ (by exact pow_ne_zero _ (by exact_mod_cast hz.ne')),one_mul]
 let L:=a0*μ; let E:=specter F D; let Z₁:=(R:ℂ)^4*wObj (W s) F D X; have hu:‖Z₁-E Z‖≤(32*w)/R:=by
    unfold Z₁ E; rw [←hx',←mul_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hz.le]; refine (mul_le_mul_of_nonneg_left hx (pow_nonneg hz.le 4)).trans ?_
    rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos u0 _) hz]; change R ≤2*φ at hr; nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz.le hr 5) u.le]
 have hw:‖E Z-E d‖≤L/R:= (t _ r _ δ).trans ((mul_le_mul_of_nonneg_left v ((zero_le_one.trans ‹1≤a0›))).trans_eq (by unfold L; ring))
 exact ⟨(a _ δ).trans hC, (norm_sub_le_norm_sub_add_norm_sub _ (E Z) _).trans ((add_le_add hu hw).trans (by unfold C L; rw [←add_div]; apply div_le_div_of_nonneg_right _ hz.le; linarith only [‹1≤a0›]))⟩
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
