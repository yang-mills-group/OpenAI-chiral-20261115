import YM.SatinExist.Lede
import YM.SatinExist.Stile
import YM.SatinExist.Cameo
import SatinThinBeam
import SatinThinMill
-- Raze sell at finite registration. Toward unpadding on MANY *Operators*.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open TopologicalSpace Germ Alliance
namespace Spine
open Aria Set TopologicalSpace Metric Casting
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j) (D:P.Apron)(n w:ℕ)
local notation "K"=> P.calibration
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> P.VMark
local notation "κ"=> P.laysM
local notation "ψ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "ω"=> P.colorZero j x
local notation "Φ"=> P.colorSpace j x
local notation "X"=>P.ColorHil j x
local notation "Χ"=>P.ManyF j x
local notation "υ" v:max=>P.voxTest j n v
local notation "φ₀" k:max p:max F:max q:max=>P.colorSpace j x (P.door j n k p F q)
local notation "u₁" v:max=> Apron.time_panel P j v D
local notation "v₁" v:max=> Apron.time_edge P j v D
local notation "W"=> P.cartage j x
local notation "B"=> P.pillar j x D
local notation "C"=> P.kiosk j x
local notation "ζ"=> (P.seasons j x)
local notation "H"=> P.ManyF j x
open SatinTails
-- topic sector full coherence incl shifted corners
lemma bigger_door(a b s t:ℝ)(p:Vantage)(v:a ≤ s)(d:t≤ b)(h:s≤u₁ p)(z:v₁ p≤t) : B a b p= (ζ).E (s-a).toNNReal*B s t p*(ζ).E (b-t).toNNReal:=by
 let α:=(P.tableau j x p (D.engine P j x)); let F(q:ℝ):= (ζ).E q.toNNReal
 let y:= u₁ p; let c:= v₁ p; have he(U V:ℝ)(p:0≤U)(h:0≤ V):F (U+V)= F U*F V:=by unfold F; rw [Real.toNNReal_add p h]; exact (ζ).time ..
 change F (y-a)*(α*F (b-c))= (F _)*(F _*(α*F _))*F _; rw [show y-a=s-a+(y-s) by ring, he _ _ (sub_nonneg.mpr v) (sub_nonneg.mpr h), show b-c=t-c+(b-t) by ring, he _ _ (sub_nonneg.mpr z) (sub_nonneg.mpr d)]; rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc] -- tune
lemma travels_door(a b:ℝ)(p q:Vantage): B (q j+a) (q j+b) (q+p)= W q*B a b p* W (-q):=by
 ext1 v; let A:=P.tableau j x; let V:=(D.engine P j x); let T:= (q+p); have hp:u₁ T=q j+u₁ p:=by unfold T Apron.time_panel; rw [Pi.add_apply]; ring
 have he:v₁ T=q j+v₁ p:=by unfold T Apron.time_edge; rw [Pi.add_apply]; ring
 let x1:= (u₁ p-a).toNNReal; let x2:= (b-v₁ p).toNNReal
 have hz₁:= congrArg Real.toNNReal (show u₁ T-(q j+a)=(u₁ p-a) from (by rw [hp]; ring))
 have hz₂:= congrArg Real.toNNReal (show (q j+b)-v₁ T=(b-v₁ p) from (by rw [he]; ring))
 change (ζ).E _ (A T V ((ζ).E _ v))= W q ((ζ).E x1 (A p V ((ζ).E x2 (W (-q) v))))
 rw [hz₁,hz₂]
 have hv: W q (W (-q) v)=v:=by rw [←ContinuousLinearMap.comp_apply, ←P.cart_paves,add_neg_cancel,P.cart_zero]; rfl
 unfold A T; rw [P.warm_drive, ← P.warm_drive j x q];
 change (ζ).E x1 _ = (ζ).E x1 (W q ((P.tableau j x p V) _))
 refine congrArg _ (Eq.trans ?_ (P.cart_independent j x q p V _))
 refine congrArg _ ?_; rw [←ContinuousLinearMap.comp_apply (W q), ←P.cart_paves, add_neg_cancel,P.cart_zero]; rfl -- v? need E x2
lemma gearBound {p:ℕ→ Vantage}{y:Vantage}(q:Tendsto p atTop (𝓝 y)):Brakes (fun i=> (P.cartage j x (p i))) (W y):=by
 have h:Brakes (fun i=> W (p i)) (W y):=by
    refine ⟨⟨1,Eventually.of_forall fun _=>P.cart_pay ..⟩,fun i=>((P.cart_cont j x i).continuousAt.tendsto.comp q),fun i=>?_⟩
    change Tendsto (fun k=> ContinuousLinearMap.adjoint (W (p k)) i) atTop (𝓝 (ContinuousLinearMap.adjoint (W y) i)); simp_rw [P.cart_reverses]; exact (P.cart_cont j x i).continuousAt.tendsto.comp q.neg
 exact h
lemma kioskL : ∃ U: (X).Op →L[ℂ] (Χ).Op, ∀ x':(X).Op,U x'=C x':=by
 let V: (X).Op →ₗ[ℂ] (Χ).Op:={toFun:= P.kiosk j x, map_add':=fun i z=> ContinuousLinearMap.ext (fun y=>by simp [kiosk]),map_smul':=fun i z=> ContinuousLinearMap.ext (fun y=> by simp [kiosk])}
 have hv(z:(X).Op):‖C z‖≤‖z‖:= by rw [show C z= P.tableau j x 0 z from (by unfold kiosk tableau; rw [neg_zero,P.cart_zero]; rfl)]; exact P.tableau_pay ..
 exact ⟨V.mkContinuous 1 (fun p=>by rw [one_mul]; exact hv p),fun _=> rfl⟩
lemma kiosk_s {A:ℕ→ (P.ColorHil j x).Op}{L:(X).Op}(a:Tendsto A atTop (𝓝 L)) : Tendsto (fun i=>C (A i)) atTop (𝓝 (C L)):=by obtain ⟨uR,p⟩:=P.kioskL j x; simp_rw [←p]; exact uR.continuous.continuousAt.tendsto.comp a
lemma kiosk_scale (A:(X).Op)(b:ℂ): C (b•A)=b•C A:=by obtain ⟨U,p⟩:= P.kioskL j x; simp_rw [←p]; exact map_smul ..
-- symmetric schedule reach arbitrary stricter.T compare; propagation on projected
section sorted
variable (Z:ℕ→ P.Apron)(b:ℕ → ℂ)
local notation "η" n:max=> Z n
local notation "Ξ" n:max a:max d:max r:max=> P.pillar j x (Z n) a d r
lemma nearer {p:ℕ→ Vantage}{V: (P.ManyF j x).Op}{t d:ℝ}{y:Vantage}
    (v:Tendsto p atTop (𝓝 y))(h:0<y j)(u:y j< d)(hw:∀ᶠ n:ℕ in atTop, 0 ≤ Apron.time_panel P j (p n) (Z n) ∧ Apron.time_edge P j (p n) (Z n) ≤ d)
    (c:Brakes (fun n=> b n • Ξ n 0 d (p n)) V)(a:d < t):
    let X':=(P.cartage j x (-y))*V*P.cartage j x y; Brakes (fun n=> b n • (Ξ n (-t) t 0)) ((ζ).E (t-y j).toNNReal* X' * (ζ).E (y j+t-d).toNNReal):=by
 intro W'; let Ta(n:ℕ):= (Ξ n 0 d (p n)); let f(n:ℕ):=(p n j); let V':=(gearBound P j x v); let U':=(gearBound P j x v.neg)
 have e(t:Vantage): -(-t)=t:= neg_neg _
 have F: Tendsto f atTop (𝓝 (y j)):= tendsto_pi_nhds.mp v j
 let l(n:ℕ):= t-f n; let r(n):= f n+t-d;
 have hT := continuous_real_toNNReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=t)).sub F); have hR:= continuous_real_toNNReal.continuousAt.tendsto.comp ((F.add (tendsto_const_nhds (x:=t))).sub (tendsto_const_nhds (x:=d)))
 refine ((((Brakes.heatT (ζ) hT).weave ((U'.weave c).weave V')).weave (Brakes.heatT (ζ) hR)).sameC ?_ rfl)
 filter_upwards [hw,F.eventually (gt_mem_nhds (lt_trans u a)),F.eventually (lt_mem_nhds h)] with n w h0 u0
 change (ζ).E (l n).toNNReal*(W (-p n)*(b n • Ta n)*W (p n)) *((ζ).E (r n).toNNReal)= _
 let t':= -f n; let y':= t'+d; let L:= Z n
 have he: P.pillar j x L t' y' 0= W (-p n)* Ta n * W (p n):=by
    have ht:=travels_door P j x L 0 d (p n) (-p n); rw [e,neg_add_cancel, Pi.neg_apply,add_zero] at ht; exact ht
 have hv:P.pillar j x L (-t) t 0= (ζ).E (l n).toNNReal * (P.pillar j x L t' y' 0) *((ζ).E (r n).toNNReal):=by
    obtain ⟨e,h⟩:=w; unfold Apron.time_panel at e; unfold Apron.time_edge at h
    change t> f n at h0; change f n > 0 at u0; change 0 ≤ f n-L.realWidth P j at e; change f n+L.realWidth P j ≤ d at h
    have hz':-t ≤ t' := neg_le_neg h0.le; have he': y'≤ t:=by unfold y' t'; linarith only [u0,a]; -- tactic newline
    have h:= P.bigger_door j x L (-t) t t' y' 0 hz' he' (by unfold t'; unfold Apron.time_panel; rw [Pi.zero_apply]; linarith only [e]) (by unfold y' t' Apron.time_edge; rw [Pi.zero_apply]; linarith only [h])
    rw [show t' - -t=l n from by unfold t' l; ring, show t-y'=r n from by unfold y' t' r; ring] at h; exact h -- parse inner by
 rw [he] at hv
 change _= b n • P.pillar j x L (-t) t 0
 rw [hv]; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
end sorted
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
