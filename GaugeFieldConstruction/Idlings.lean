import GaugeFieldConstruction.Larking
import YM.CF.Moto.Road
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
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
omit o in
lemma lift_PV {Q: InkD n}{r:ℝ}(hv:PressB p X Q h c)(v:c ≤ r): PressB p X Q h r:=by -- conflict binder r and h tune
 obtain ⟨a,b,d,e,f,k,l,m⟩:=hv; exact ⟨a,b,d,e,f,k,l,m.trans v⟩
variable {q:InkD n}{b a v r:ℝ}
lemma lifeSum {J:Type}(T:Finset J)(F:J → InkD n): lifeH (∑ i∈T,F i)= ∑ i∈T, lifeH (F i):=by
 funext i; rw [Finset.sum_apply]; change panHom _ ((∑ i'∈T,F i') i )= _; rw [Finset.sum_apply, map_sum]; rfl
lemma plainZero :orbitPH (0:Cipher n)=0:=by ext i j; unfold orbitPH; rw [Matrix.of_apply,Prism.port_eq]; split; rfl; change _*(0:ℂ)=0; rw [mul_zero]
lemma plainPlus(X Y:Cipher n): orbitPH (X+Y)=orbitPH X+orbitPH Y:=eq_add_of_sub_eq (show _ from (tail_K (X+Y) Y).symm.trans (congrArg orbitPH (add_sub_cancel_right X Y))) -- tune
lemma patch_p {F G:InkD n}: (fun x=>orbitPH ((F+G) x))=(fun x=>orbitPH (F x))+(fun x=>orbitPH (G x)):=funext fun i=> plainPlus ..
lemma plains {J:Type}(T:Finset J)(F:J→ Cipher n):orbitPH (∑ i∈T,F i)= ∑ i∈T,orbitPH (F i):=by
 classical
 induction T using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty,plainZero]
 | @insert i T h ih=> rw [sum_insert h,sum_insert h,plainPlus,ih]
variable {o} (M:Tulip.Male)
lemma landPlus(P:PressB p X Q h c)(U:PressB p X q h b) : landA M o (Q+q) p h= landA M o Q p h+landA M o q p h:=by
 apply ContinuousLinearMap.ext; intro i; let x:=landR M (o:=o) (Larch.prop_add _ _ P U) i
 let K(z:tangD n):=increment 1 z; let w(t:ℝ):= K (t • gateC o p.threshold i); let V(f:InkD n)(x:ℝ):=sectorJ (orbitPH (f (w x))) M o h
 have hv: V (Q+q)=V Q+V q:=funext fun x=> by unfold V; rw [Pi.add_apply,plainPlus, sector_add]; rfl
 exact (show HasDerivAt (V (Q+q)) _ 0 from x).unique (hv.symm ▸ (show HasDerivAt (V Q+V q) _ 0 from (landR M (o:=o) P i).add (landR M (o:=o) U i))) -- tune
lemma landS {J:Type}(T:Finset J)(F:J→InkD n)(C:J→ℝ)(he:∀ i∈T,PressB p X (F i) h (C i)):
 landA M o (∑ i∈T,F i) p h=∑ i∈T, landA M o (F i) p h:=by
 classical
 induction T using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; apply ContinuousLinearMap.ext; intro i; let x:=gateC o p.threshold i;
           have hf: sectorJ (0:Op (Single n)) M o h=0:= map_zero (αxp M o h); have hp:Paint (0: InkD n) x=0:=by ext i j; simp only [Paint,Matrix.of_apply]; rw [show portE (0:InkD n) i j=(fun _=>0) from funext (fun _=> Matrix.ext_iff.mpr plainZero i j)]; simp
           change sectorJ (Paint (0:InkD n) x) M o h=0; rw [hp,hf] -- tune
 | @insert i T k ih=> let ht:=fun i (h:i∈T)=>he i (mem_insert_of_mem h); rw [sum_insert k,sum_insert k,landPlus (o:=o) M (he _ (mem_insert_self ..)) (Larch.prop_sum T F C p h X ht),ih ht]
abbrev orbC (o:Skye.Seat n)(h:ℝ): Pal→L[ℝ]Pal:= -- dummy remove
 ContinuousLinearMap.id ..
lemma seasonH {x y:Site n}(P:Pal)(r: h≠0) : sectorJ (modelK o x y h P) M o h= baseF false * P * baseF true:=by rw [seat_b,pounce o x y P r,pay_zero,one_smul]
-- Sharp derivative of beam through wall. price of positive orders at flat scales with threshold at all these short points. No ∆^* weight loss.
omit M
def DLinx (v:Cover)(o:Skye.Seat n)(x:tangD n):Pal:= fderiv ℝ (LedgeK v o ∘ increment 1) 0 x
lemma allowX {v:Cover}(p:lateral v ≤4): Push.Uniform.Allows 1 (LedgeK v o ∘ increment 1) 0 (Kin_1 1 12).choose:=(Kin_1 1 12).choose_spec.2 (More n) o 1 _ ((PathS _).choose_spec.1.trans (spot_price _ _ p))
lemma edgeZ (x:Cover)(t:lateral x ≤4)(v:tangD n): HasDerivAt (fun y:ℝ=>LedgeK x o (increment 1 (y • v))) (DLinx x o v) 0:= Push.side _ ((allowX (o:=o) t).analytic.differentiableAt (by norm_num)) _
abbrev edgeRate:= (Kin_1 1 12).choose*25^3
lemma hat_Ω (x:Cover)(t:lateral x ≤4)(v:tangD n)(P:p.dirBound o v)(u:p.power ≤3) : ‖DLinx x o v‖ ≤ edgeRate*p.threshold:=by
 let F:=LedgeK x o; let C:=(Kin_1 1 12).choose; let L:= p.threshold*25^3; have h(i: Edge (Skye.Seat n))(s:fitsSpan (Pax o) i): ‖v i‖ ≤ L:=by
    apply (P i).trans; apply mul_le_mul_of_nonneg_left _ p.threshold_pos.le; have he: separation i.1 o ≤24:=by
       obtain ⟨j,k,h⟩:= halo_spec.mp s.1; rw [separation_comm]; rw [←mem_singleton.mp k]; exact h
    apply (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity) : 1 ≤ 1+(separation i.1 o:ℝ)) u).trans; gcongr; exact (show (1:ℝ)+(separation i.1 o:ℝ)≤25 from by exact_mod_cast (show 1+separation i.1 o ≤25 from by omega)) -- tune
 have ht:0≤L:=mul_nonneg p.threshold_pos.le (by positivity)
 have he:= hatchC (allowX (o:=o) t) (Ledge_o x t)  le_rfl (fun i:Fin 1=>v) (fun _=>L) (fun _=>ht) (fun i=>h) -- wrong binder k
 rw [iteratedFDeriv_one_apply,Finset.prod_const,card_univ,Fintype.card_fin,pow_one] at he; apply he.trans_eq; unfold L edgeRate; ring
lemma ledge_w (x:Cover)(o:Skye.Seat n): LedgeK x o 1 = 1:= (congrArg KinX (TarOne (o:=o) x)).trans KinId
lemma Beam_ep(h:ℝ)(o:Skye.Seat n)(x y:Site n):∃ L:Pal→L[ℝ]Op (Single n),∀ i,L i=modelK o x y h i:=by
 let p(P):= modelK o x y h P; refine ⟨LinearMap.toContinuousLinearMap (show Pal→ₗ[ℝ] _ from ⟨⟨p,?_⟩,?_⟩),fun i=>rfl⟩
 · intro a b; ext i j; simp only [p,modelK,Moto.seed_k, Matrix.of_apply,Matrix.add_apply]; split; · simp [mul_add]
   rw [zero_add]
 intro a b; ext i j; simp only [p,modelK,Moto.seed_k,Matrix.of_apply,Matrix.smul_apply,RingHom.id_apply]; split; · rw [smul_comm]
 rw [smul_zero]
variable (k:lotV)
abbrev pulseI (A B C: Pal)(o:Skye.Seat n)(v:tangD n):Pal:= star (DLinx (shoreX k) o v)* A+B+C*DLinx (shoreY k) o v
lemma Beam_V(A:Pane n→Pal)(B: Pal)(v:tangD n)(p':HasDerivAt (fun y:ℝ=> A (increment 1 (y • v))) B 0): HasDerivAt (fun t:ℝ=>beamer o k A h (increment 1 (t • v))) (modelK o (landX o k) (landY o k) h (pulseI k (A 1) B (A 1) o v)) 0:=by
 obtain ⟨i,j⟩:= knot_rad k; let x:=shoreX k; let y:=shoreY k; let F(s:ℝ):= increment 1 (s • v); let X(t:ℝ):= LedgeK x o (F t); let Y(t:ℝ):=LedgeK y o (F t); have hF:F 0=1:=by unfold F; rw [zero_smul,at_zero]
 have hx:X 0=1:=by unfold X; rw [hF]; exact ledge_w ..
 have hy:Y 0=1:=by unfold Y; rw [hF]; exact ledge_w ..
 have he: HasDerivAt X (DLinx x o v) 0:= edgeZ x i v; have hp: HasDerivAt Y (DLinx y o v) 0:= edgeZ y j v; let Z(t):= carryU o k (F t) (A (F t));
 have ht:HasDerivAt Z (pulseI k (A 1) B (A 1) o v) 0:=by
    let K:Pal→L[ℝ] Pal:= LinearMap.toContinuousLinearMap ({toFun:=star,map_add':=star_add,map_smul':=fun i j=>by rw [star_smul,star_trivial]; rfl}); let P:ℝ→Pal:=fun i=> A (F i); have hP:HasDerivAt P B 0:=p'
    apply ((((K.hasFDerivAt.comp_hasDerivAt 0 he).mul hP).mul hp)).congr_deriv
    simp only [Pi.mul_apply,Function.comp_apply,hx,hy,P,hF,show K 1=1 from star_one _,one_mul,mul_one]; try rfl
 obtain ⟨L,E⟩:= Beam_ep h o (landX o k) (landY o k); unfold beamer; simp_rw [← E]; exact L.hasFDerivAt.comp_hasDerivAt 0 ht
include M
lemma land_1 (A:Pane n→ Pal)(x:ComG)(H:PressB p X (viewW o k A h) h c)(V:Pal)(t:h≠0)(s:HasDerivAt (fun i:ℝ=> A (increment 1 (i • gateC o p.threshold x))) V 0) : landA M o (viewW o k A h) p h x=baseF false*pulseI k (A 1) V (A 1) o (gateC o p.threshold x)*baseF true:=by
 let W:=gateC o p.threshold x; let F:=viewW o k A h; let S(t:ℝ):=increment 1 (t • W); let U(t:ℝ):=beamer o k A h (S t); have he: (fun i=> orbitPH (F (S i)))= U:=funext fun i=> ph_caps ..
 have hp: Paint F W=modelK o (landX o k) (landY o k) h (pulseI k (A 1) V (A 1) o W):= (painted H W).unique ((he.symm ▸ (Beam_V (o:=o) (h:=h) k A V W s))) -- tune let
 change sectorJ (Paint F W) M o h=_; rw [hp, seasonH M _ t]
end Layout
end Lenten
end YM.CF.TableF
end
