import GaugeFieldConstruction.GlintH
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace ModuleB
open scoped ComplexOrder
variable (M:Male)
abbrev sectorJ (Q:Op (Single n))(M:Male)(o:Skye.Seat n)(h:ℝ) := (winJ o M h Q).1
lemma seat_b (Q:Op (Single n)): sectorJ Q M o h= baseF false * streamF o Q h 0 * baseF true:=by
 rw [sectorJ, ← (tab M Q).point]; let X:=baseF false; let Y:=baseF true
 change _ * (fellP M false _* (streamF o Q h 0*(fellP M true _ *Y)))= _
 rw [show fellP M false 0=X from binBase M false,show fellP M true 0=Y from binBase M true, (bladeSeal true).1.eq, ←mul_assoc,(bladeSeal false).1.eq, mul_assoc] -- tune
lemma stack_g (g:SU.E)(Q:Op (Single n))(o:Skye.Seat n)(h:ℝ)(R:Op (Single n))(p:∀ x y:Site n, matPH R x y* KinX g= KinX g*matPH Q x y): sectorJ R M o h * KinX g = KinX g * sectorJ Q M o h:=by
 let u:=KinX g; let P:=streamF o Q h 0; let Z:=streamF o R h 0; let A:=baseF false; let B:=baseF true; have hx:Z*u=u*P:=by
    unfold Z P; rw [streamS,streamS]; simp_rw [Matrix.sum_mul,Matrix.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [Matrix.smul_mul, Matrix.mul_smul, show matPH R i j * u=u*matPH Q i j from p _ _]
 rw [seat_b,seat_b]; change A*Z*B*u=u*(A*P*B); rw [mul_assoc (A*Z), (stake_M g true).eq, ← mul_assoc, mul_assoc A, hx, ←mul_assoc, (stake_M g false).eq, mul_assoc u,mul_assoc u] -- tune
local notation "γo"=> X.val.1
-- derivative pencil via block majorization
abbrev portE (Q:InkD n)(x y:Single n)(i:tangD n): ℂ:= orbitPH (Q (increment 1 i)) x y
private lemma scale_left {F:tangD n→ℂ}(h:Signs p o F c)(i:ℂ)(hy:‖i‖=1): Signs p o (fun v=>i*F v) c:=by
 let L:ℂ →L[ℝ] ℂ:= i • ContinuousLinearMap.id ℝ ℂ
 refine ⟨h.grade,L.contDiff.contDiffAt.comp 0 h.paid,fun j hj y w=>?_⟩
 change ‖iteratedFDeriv ℝ j (L ∘ F) 0 y‖≤_; rw [L.iteratedFDeriv_comp_left (f:=F) h.paid (Nat.cast_le.mpr hj)]; change ‖i* iteratedFDeriv ℝ j F 0 y‖ ≤ _; rw [norm_mul,hy,one_mul]; exact h.token _ hj _ w
lemma PGr (k:Finset (Dwell n)→ℝ)(w:BedP p 1 Q X k)(x y:Single n) : Signs p X.val.1 (portE Q x y) (k (Haro.tray x y)):=by
 let b:Dwell n:= (true,x); let a:Dwell n:= (false,y); let V:= Fock.parity b {a} -- tune namespace
 have he:b≠a:=by simp [b,a]
 have hx(i): portE Q x y i= V * Pastry.crumb (Q (increment 1 i)).val (Haro.tray x y):= by unfold portE orbitPH; rw [Matrix.of_apply,Prism.port_eq,if_neg he]
 rw [funext hx]; exact scale_left (w (Scree.ping_f p X.val.2) _) _ (by simp [V,Fock.parity]) -- tune or direct scalar chain via Iter derivative.
variable (P:PressB p X Q h c)
local notation "Kul" n:max=> Op (Single n)
def Paint (Q:InkD n)(x:tangD n): Kul n:= Matrix.of fun i j=> fderiv ℝ (portE Q i j) 0 x
include P
open Haro
lemma painted (x:tangD n):HasDerivAt (fun t:ℝ=> orbitPH (Q (increment 1 (t • x)))) (Paint Q x) 0:=by
 obtain ⟨k,h,v,y⟩:=P.worth; apply op_deriv.mpr; intro i j; exact Push.side _ ((PGr k (v 1) i j).paid.differentiableAt (by exact_mod_cast (show p.order ≠ 0 from (Nat.zero_lt_of_lt p.order_ge).ne'))) x
-- constant gauge at flat. any argument. use MAT elementary expansion on each i. Copy Rune
set_option maxHeartbeats 80000 in
lemma misery (g:SU.E)(i j:Site n)(U:Pane n): matPH (orbitPH (Q (gauge (fun _=>g) U))) i j *KinX g= KinX g*matPH (orbitPH (Q U)) i j:=by
 let f(x y:SpinIdx):=CharM Q (i,x) (j,y) U; let v(x y:SpinIdx):=CharM Q (i,x) (j,y) (gauge (fun _=>g) U); let T:=matPH (orbitPH (Q U)) i j; let V:=matPH (orbitPH (Q (gauge (fun _=>g) U))) i j
 have hv(x y:SpinIdx): v x y* Haro.mater g= Haro.mater g*f x y:=by
    rw [show v x y= Haro.mater g*f x y * star (Haro.mater g) from char_g X Q P U (r:=(i,x)) (s:=(j,y)) (fun _=>g)]; rw [mul_assoc,show star (Haro.mater g)* Haro.mater g=1 from (SU.matter _).property.1, mul_one]
 let H:=KinX g; ext ⟨x,a⟩ ⟨y,b⟩; change (V *H) (x,a) (y,b) = (H*T) _ _; rw [Matrix.mul_apply, Matrix.mul_apply]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (fun l:SpinIdx × SU.Slot=> H (x,a) l*T l (y,b))]; rw [sum_eq_single y,sum_eq_single x]
 · unfold H; simp only [KinX,Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul]; exact Matrix.ext_iff.mpr (hv x y) a b
 · intro i _ k; simp [H,KinX,Matrix.one_apply,k,Ne.symm k]
 · simp
 · intro i _ k; simp [H,KinX,Matrix.one_apply,k,Ne.symm k]
 simp
omit P
private def slotShow (x y:Site n): Kul n →L[ℝ] Pal:= by
 refine LinearMap.toContinuousLinearMap ⟨⟨(fun i=>matPH i x y),?_⟩,?_⟩
 · intro i j; ext a b; rfl
 intro i j; ext a b; rfl
include P
lemma mercy (g:SU.E)(x y:Site n)(T:tangD n): matPH (Paint Q (colorMove g T)) x y* KinX g= KinX g*matPH (Paint Q T) x y:=by
 let X:= fun (p:tangD n)=> orbitPH (Q (increment 1 p)); let K:=slotShow x y; let H(P):=K (X P); let L(t:ℝ):= H (t • colorMove g T); let U(t:ℝ):= H (t • T)
 have h: (fun z=> L z *KinX g)= (fun z=> KinX g * U z):=by funext z; unfold L U H X; rw [← map_smul, exp_move]; exact misery P ..
 have ht(Z:tangD n): HasDerivAt (fun i:ℝ=>H (i • Z)) (K (Paint Q Z)) 0:= K.hasFDerivAt.comp_hasDerivAt 0 (painted P Z)
 apply ((ht (colorMove g T)).mul_const (KinX g)).unique; rw [show (fun x=> L x*_ ) =_ from h]; exact (ht T).const_mul _
omit P
def panLinear (Q:InkD n): tangD n→L[ℝ](Op (Single n)):=by
 refine LinearMap.toContinuousLinearMap ⟨⟨Paint Q,?_⟩,?_⟩
 · intro i j; ext x y; change fderiv ℝ _ _ (i+j)= _; rw [map_add]; rfl
 intro i j; ext x y; change fderiv ℝ _ _ (i • j)= _; rw [map_smul]; rfl
-- inspections
lemma sector_add (V U:Kul n):sectorJ (V+U) M o h=sectorJ V M o h + sectorJ U M o h:=by
 let A:=streamF o U h 0; let B:=streamF o V h 0
 rw [seat_b,seat_b,seat_b]; rw [show streamF o (V+U) h 0=B+A from ?_,mul_add,add_mul]; -- tune
 unfold streamF B A; simp only [streamF,hill_Z,Matrix.add_apply,mul_add,map_add, sum_add_distrib]
lemma sector_scale (V:Kul n)(a:ℂ):sectorJ (a • V) M o h= a • sectorJ V M o h:=by
 rw [seat_b,seat_b]; rw [show streamF o (a • V) h 0=a • streamF o V h 0 from ?_,Matrix.mul_smul, Matrix.smul_mul]; unfold streamF; rw [smul_sum]; apply sum_congr rfl; intro i _; unfold hill_Z; rw [Matrix.smul_apply, smul_eq_mul]; let W:=a
 rw [show ∀ b c d:ℂ,b*(c*(a*d))=a*(b*(c*d)) from fun _ _ _=>by ring]; let k:=portB i.1; let l:=portB i.2; exact (Matrix.smul_single (R:=ℂ) (α:=ℂ) a k l _).symm
lemma sector_real(V:Kul n)(a:ℝ):sectorJ (a • V) M o h=a • sectorJ V M o h:=by rw [← Complex.coe_smul, sector_scale, Complex.coe_smul]
def αxp (M:Male)(o:Skye.Seat n)(h:ℝ) : Kul n→L[ℝ] Pal:=LinearMap.toContinuousLinearMap (show Kul n→ₗ[ℝ] Pal from ⟨⟨fun i=>sectorJ i M o h, fun i j=>sector_add M i j ⟩, fun i v=>sector_real M v i⟩)
def landA (M:Male)(o:Skye.Seat n)(Q:InkD n)(p:BudgetPoint)(h:ℝ): ComG→L[ℝ]Pal:= (αxp M o h).comp (panLinear Q|>.comp (gateC o p.threshold))
lemma base_s (T: Kul n): baseF false* sectorJ T M o h * baseF true=sectorJ T M o h:=by unfold sectorJ; rw [← (tab (h:=h) (o:=o) M T).point]; exact soak_X M T _
structure ViewsM (x: ComG→L[ℝ]Pal):Prop where
 binned (v): baseF false*x v*baseF true=x v
 main(g:SU.E)(a:Gem)(v:SU.group.Color): x (coneC a (SU.group.adjoint g v))* KinX g= KinX g * x (coneC a v)
include P
lemma portalG : ViewsM (landA M o Q p h):=by
 constructor; · intro v; exact base_s M _
 intro g a v; change sectorJ (Paint Q (gateC o p.threshold (coneC a (SU.group.adjoint g v)))) M o h * KinX g=KinX g * sectorJ (Paint Q (gateC o p.threshold (coneC a v))) M o h
 rw [tintWing]; apply stack_g; exact fun i j=> mercy P _ i j _
omit P
lemma odeG {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](x:Ole E F): ‖x.1‖ ≤ CostOle x:= le_max_left ..
include P
set_option maxHeartbeats 85000 in
lemma roof_T (v:0≤h): tautF (landA M γo Q p h) ≤ ( (1/50:ℝ)⁻¹ * mintPay (caboose*16))*c:=by
 let S:=X.val.1; let t:ℝ:=1/50; let C:=mintPay (caboose*16); let r:=landA M S Q p h;
 have he:0≤ C*c:= le_trans (Ole_non _) (winκ M P v); rw [mul_assoc]; refine (show _ from Flot.price_desk r (by norm_num : 0<t) he (fun i pI=>?_))
 let k:= Paint Q (gateC S p.threshold i); change ‖sectorJ k M S h‖ ≤ _; apply le_trans (odeG (winJ S M h k)); apply le_trans (costmint _ _ _ (c:= (caboose*16)*c) ?_); · unfold mintPay; exact le_of_eq (by ring)
 obtain ⟨a,E,Y,V⟩:= P.worth; refine upper_far k a E v V fun j d=>?_ ; let x:=gateC S p.threshold i
 have hy:p.dirBound S x:= formC_life i S p pI -- typo
 have hf: ‖iteratedFDeriv ℝ 1 (portE Q j d) 0 (fun _=> x)‖≤ a (tray j d):=(PGr a (Y _) j d).token 1 ((by decide:1≤6).trans p.order_ge) _ (fun _=>hy)
 rw [iteratedFDeriv_one_apply] at hf; exact hf
lemma landR (x:ComG) : let v:= gateC o p.threshold x
 HasDerivAt (fun t:ℝ=> sectorJ (orbitPH (Q (increment 1 (t • v)))) M o h) (landA M o Q p h x) 0:= (αxp M o h).hasFDerivAt.comp_hasDerivAt 0 (painted P _)

end ModuleB
end Lenten
end YM.CF.TableF
end
