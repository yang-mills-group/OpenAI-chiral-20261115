import YM.SU5.LoomForce.AperturePay
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Jets
import SatinThinQuad
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Urn Salt
variable {p:BudgetPoint}{K:Scree.Loom N}{e:ℝ}{q:ℕ} (x:Site N)(z:Checked p K e d a k q)(E:Pattern P T r d a v)
local notation "A" => tangD N
local notation "F" => (E.A x)

-- the physically gauged seed price
noncomputable abbrev tax (K:Scree.Loom N)(p:BudgetPoint)(x:Site N)(k:ℕ)(E:Pattern P T r d a v)(U:Pane N):ℂ:= Matrix.trace (taxHat K p k x E U)
local notation "τ" => tax K p
include z
lemma tax_real (U:Pane N):star ((τ x k E U):ℂ)=τ x k E U:=by
 have h:=Pattern.hatted (z:=z) E x ((U,Classical.arbitrary _):Orbit N)
 exact (Matrix.trace_conjTranspose _).symm.trans (congrArg Matrix.trace h)

lemma tax_pose (s:Sweep N)(U:Pane N):
    τ (pose s x) k E (flashA s U)= if det_S s then -tax K p x k E U else tax K p x k E U:=by
 unfold tax taxHat; rw [E.rollTax z]; let f:=live K p k x F U
 have ht:= Sault.lune s.charge (det_S s) (γS s) f
 let T:=τ x k E U; rw [show cSignX _ _ = T from ?_] at ht
 swap
 · cases s.charge.xor (det_S s); exact rfl; exact tax_real x z E U
 change Matrix.trace (if det_S s then star (ech s f) else ech s f)=T at ht
 change Matrix.trace (Thera.jazz (det_S s) (ech s f))=_
 cases hz:det_S s <;> rw [hz] at ht
 · exact ht
 rw [show Thera.jazz true (ech s f)= -star (ech s f) from rfl, Matrix.trace_neg,(show Matrix.trace (star (ech s f))= T from ht)]
 rfl

lemma tax_idle : τ x k E 1=0:=by
 obtain ⟨g,h,-,p⟩:= QuadClock.poseAll (Signed.mirror 3) x x
 have ht: pose g x=x:= unaryN (by rw [pose_node, Equiv.symm_apply_eq]; exact p.symm)
 have hL:= tax_pose x z E g 1; rw [ht,show flashA g 1=1 from ?_,show det_S g=true from by change detX g.s=true; rw [h,det_t], if_pos rfl] at hL
 · by_contra hd; exact mul_ne_zero (by norm_num:(2:ℂ)≠0) hd (by rw [two_mul]; exact eq_neg_iff_add_eq_zero.mp hL)
 ext1 i; unfold flashA stir; simp only [Function.comp_apply,Lattice.pull,Step.read, Pi.one_apply]; simp

lemma tax_degree (U V:Pane N)(s:pingS p.threshold (offsetMask p.B x) U)(w:Guard V d)
    (t:Agrees (offsetMask k x) U V) : τ x k E U = untouched F k V:=by
 -- no Tag
 let A': Orbit N:=(U,Classical.arbitrary _)
 let W:Openc (More N) d:= ⟨profile V,⟨V,w,(show ‖profile V - profile V‖<d from by simpa using z.angle)⟩⟩
 change Matrix.trace (live K p k x F A'.1)=Matrix.trace (beforePing F k W.val)
 rw [noTag x F z (E.moorA x),if_pos (show pingS p.threshold _ _ from s)]; apply congrArg Matrix.trace
 exact runs x F z (E.moorA x) A' s V W rfl (fun D i j g h=> agrees_mono t (show (↑D:Set (Skye.Seat N))⊆offsetMask k x from reachesShort z x F (E.moorA x) _ _ _ g h))

lemma tax_invariant : GaugeInvariant (τ x k E):= by
 intro g U; unfold tax taxHat; rw [glyphMove x F z (E.moorA x), Fock.trace_twist]

lemma unhat_germ : (τ x k E) ∘ increment 1 =ᶠ[𝓝 (0:A)] untouched F k ∘ increment 1:=by
 let Φ:=increment (1:Pane N)
 obtain ⟨b,t,-,w⟩:= Chaff.toll_y z.angle
 have ht:= (show Continuous Φ from ?_).continuousAt (x:=(0:A))
 · filter_upwards [Metric.ball_mem_nhds _ t, ht.tendsto.eventually (ping_o.mem_nhds (show pingS p.threshold (offsetMask p.B x) (Φ 0) from by simp only [Φ,Work.G07.at_zero_increment]; exact ping_f p _))] with i h h'
   exact tax_degree x z E _ _ h' (w N 1 (guard0 le_rfl) i (mem_ball_zero_iff.mp h)) (fun _ _ _=>rfl)
 unfold Φ increment; fun_prop

open AnalyticBridge.VerifiedReset
local notation "S" => (τ x k E) ∘ increment 1
local notation "D" => untouched F k ∘ increment 1
include z
lemma unhat_smooth : ContDiffAt ℝ (↑(3:ℕ)) D 0:=by
 obtain ⟨c,b,H⟩:=cozy 3 z.angle; exact (occupied F (E.moorA x) z.hint z.angle H (guard0 (half_pos z.angle).le)).smooth

lemma tax_first : fderiv ℝ D 0 = 0:=by
 have ht:= unhat_germ x z E; rw [←ht.fderiv_eq (𝕜:=ℝ)]
 let R:= fderiv ℝ S 0
 let V:= S
 have hv:DifferentiableAt ℝ V 0:= ((unhat_smooth x z E).congr_of_eventuallyEq ht).differentiableAt (by decide)
 -- same proof as Jets.flat_critical. Need only one invariant scalar fully true
 have he (c:SU.group.El) : V ∘ colorMove c = V:= funext fun u=> by simpa only [Function.comp_apply, exp_move,V] using tax_invariant x z E (fun _=> c) (increment 1 u)
 have hI (c:SU.group.El)(u:A): R (colorMove c u)=R u:=by
    let f:=colorMove (n:=More N) c
    have hh:DifferentiableAt ℝ V (f 0):= f.map_zero.symm ▸ hv
    have hm:=(hh.hasFDerivAt.comp 0 f.hasFDerivAt).fderiv; rw [he c,f.map_zero] at hm; exact (congr($hm u)).symm
 let lane (e:Edge (Skye.Seat N)) : group.Color→ₗ[ℝ] A:= LinearMap.single ℝ (fun _ : Edge (Skye.Seat N)=> group.Color) e
 have hl (e:Edge (Skye.Seat N))(u:group.Color) : R (lane e u)=0:=by
    let L:= R.toLinearMap.comp (lane e)
    have hw(c:group.El): ∀ x,L (group.adjoint c x)=L x := by
       intro x; change R (lane e _)=_; rw [show (lane e (group.adjoint c x))=colorMove c (lane e x) from ?_,hI]; rfl
       funext i; change Pi.single (M:=fun _ => group.Color) e (group.adjoint c x) i= group.adjoint c (Pi.single (M:=fun _=>group.Color) e x i)
       by_cases h:i=e; · subst i; simp
       simp [Pi.single_eq_of_ne h]
    exact LinearMap.congr_fun (StressFlux.linear_invariant Thera.yet_one L hw) u
 ext1 U; have h:U =(∑ i:Edge (Skye.Seat N),lane i (U i)):=by
   funext j; simp [lane,Finset.sum_apply,Pi.single_apply]
 change R U=0; rw [h,map_sum]; simp only [hl,sum_const_zero]

abbrev donor (f:Pane N→ℂ): A→L[ℝ]A→L[ℝ]ℂ:=(2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ (f ∘ increment 1)) 0
abbrev taxpayer := donor (untouched F k)
#print taxpayer

lemma aperture_agrees : donor (τ x k E)= taxpayer x E (k:=k):=by
 unfold taxpayer donor; rw [unhat_germ x z E|>.fderiv (𝕜:=ℝ)|>.fderiv_eq (𝕜:=ℝ)]

omit z in
lemma aperture_doll (U:A): taxpayer x E (k:=k) U U=dollH (untouched F k) U:=rfl

lemma aperture_cost (Q:HopeT d b g 3) (U V:A): ‖taxpayer x E (k:=k) U V‖≤ (2:ℝ)⁻¹*occupancy a v g*(‖U‖*‖V‖):=by
 have ht:= ((occupied F (E.moorA x) z.hint z.angle (k:=k) Q (guard0 (half_pos z.angle).le)).norm_le 2 (by norm_num))
 -- use Multilinear
 let p := (![U,V]:Fin 2 → A)
 have hh: fderiv ℝ (fderiv ℝ D) 0 U V = (iteratedFDeriv ℝ 2 D 0) p:= (iteratedFDeriv_two_apply D 0 p).symm
 have hm: ∏ i:Fin 2, ‖p i‖= ‖U‖ * ‖V‖:= Fin.prod_univ_two (fun i=> ‖p i‖)
 change ‖(2:ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ D) 0 U V)‖≤ _; rw [hh,norm_smul,Real.norm_of_nonneg (by norm_num),mul_assoc]
 apply mul_le_mul_of_nonneg_left _ (by norm_num); refine ((iteratedFDeriv ℝ 2 D 0).le_opNorm p).trans ?_; rw [hm]; exact mul_le_mul_of_nonneg_right ht (by positivity)

structure TankSpot (d u:ℝ) : Prop where
 size : 0<u
 paid (m:Side)(i:tangD m): ‖i‖ ≤ u → Guard (increment 1 i) (d/2)

omit z in
lemma tanks_live (h:0<d):∃ u,TankSpot d u :=by
 obtain ⟨r,e,-,q⟩:=Chaff.toll_y (half_pos h); exact ⟨r/2,half_pos e,fun m i u=> q m _ (guard0 le_rfl) i (u.trans_lt (half_lt_self e))⟩

lemma aperture_taylor (W:TankSpot d u) (Q:HopeT d b g 3)(i:A)(h:‖i‖≤u):
    ‖untouched F k (increment 1 i)-taxpayer (k:=k) x E i i‖ ≤ occupancy a v g*‖i‖^3:=by
 have he:= uniform_roll (untouched F k) u W.size (fun X s=>occupied F (E.moorA x) z.hint z.angle Q (W.paid _ _ s)) (tax_first x z E) i h
 rw [show untouched F k 1=0 from ?_,sub_zero,←aperture_doll x E i] at he
 · exact he
 have hf: S 0=D 0:= (unhat_germ x z E).self_of_nhds; simpa [Function.comp, tax_idle x z E] using hf.symm

#print axioms aperture_taylor
end YM.CF.LitCurrent.Surplus
