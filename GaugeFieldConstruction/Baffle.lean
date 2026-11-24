import GaugeFieldConstruction.Vales
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
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
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
open Rush
-- anchor costs on this chart.
open QuadClock Vault
variable {w b t q p': Bool}{U: UNI SpinIdx}{f:Op (Single n)}
-- projection step. for general binned departures. EVENTUAL for costs
private lemma Karn(M: Male)(b':Bool) (x:Plane) : binor M b' x= Fir.bent b' 4 M.val (angle x) ⊗ₖ (1:Op SU.Slot):=by
 cases b'; swap; · rfl
 unfold binor; simp only [Fir.bent,Bool.false_eq_true,ite_false]; rw [sub_eq_add_neg (1:Op SpinIdx),Matrix.add_kronecker,op_kron_neg,Matrix.one_kronecker_one]; rfl -- name tune
lemma ballTP (M:Tulip.Male)(p:JetS R b t U): ∀ᶠ x in 𝓝 (0:Plane), ∀ k: Bool, sings b (twoU U b) (binor M k (κcad R b x))= binor M (t.xor k) x:=by
 filter_upwards [buoy_l] with x h; intro k; rw [Karn,angle_κ R b x,wingK,Scroll.bent_s p M.val M.property _ h]; rw [Karn]; congr 1; rw [singT,win_i,map_one] -- tune namespace
set_option maxHeartbeats 150000 in
lemma StreamCull (A:Op (Single n))(P:∀ i j:Site n, matPH A i j≠0 →10*separation (node i) o <(More n).val∧ 10*separation (node j) o <(More n).val)(l:100<n.val) (x:Views): streamF (sh s o) (sings s.charge (siteU (castX s) s.charge U n) A) h x= sings s.charge (twoU U s.charge) (streamF o A h (candT s.s s.charge x)):=by
 let w:= s.charge; let V:=siteU (castX s) s.charge U n; let π:Pal→ Pal:= fun f=> sings s.charge (twoU U s.charge) f; let U':=twoU U s.charge; let a:=castX s;
 rw [streamS,streamS,singT (p:=s.charge) (twoU U s.charge)]; simp_rw [win_sum,map_sum]
 refine Fintype.sum_equiv (Tofu a n) _ _ fun i=> Fintype.sum_equiv (Tofu a n) _ _ fun j=>?_
 let X:=a.mills n i; let Y:=a.mills n j; let B:=matPH A X Y;
 let T:=κviews (sh s o) i j; let S:=κviews o X Y; let z:= candT s.s s.charge x; let p:= PayS T x; let e:=Caller (sh s o) i; let d:= Caller (sh s o) j
 have hw:matPH (sings w V A) i j=(a.payA i*a.payA j) • π B:= QuadClock.payR .. -- tune
 change (p*(h:ℂ)^2*e*d) • matPH (sings w V A) i j=π ((PayS S z *(h:ℂ)^2 * Caller o X *Caller o Y) • B)
 rw [hw]; by_cases b':B=0
 · rw [b']; unfold π; simp [singT,win_z]
 let r:= P X Y b'; have hr: PayS S z=cSignX w p:= PhaseV s _ _ r.1 r.2 x w; have hx:Caller o X * Caller o Y= _:=fee_c _ s i j r.1 r.2 l -- tune
 let K(h:ℂ)(s x y): h*(s:ℂ) * x * y= h*s*(x*y):=mul_assoc ..
 rw [hr,K (cSignX w p),hx]; unfold π; rw [singT (A:= (_ • B)), win_c, twist_scalar]; unfold sings -- tune
 -- cSign parity signs and smuls coefficient equality. No extra square phase (pair factors π scaled!)
 let b:ℂ:= a.payA i*a.payA j; have hb:star b=b:=by unfold b; rw [star_mul,a.real_payA,a.real_payA,mul_comm]; -- tune star_mul
 have he:star e=e:=fee_real _; have hd:star d=d:=fee_real _
 rw [smul_smul]; congr 1; -- handle scalar
 change p*(h:ℂ)^2*e*d*b=cSignX w (cSignX w p*(h:ℂ)^2 *(b*(e*d)))
 cases w
 · change _=p*_*_; ring
 change _= (starRingEnd ℂ) ((starRingEnd ℂ) p*(h:ℂ)^2*(b*(e*d))) -- tune
 simp only [map_mul,starRingEnd_self_apply,show (starRingEnd ℂ) b=b from hb,show (starRingEnd ℂ) e=e from he,show (starRingEnd ℂ) d=d from hd, map_pow,Complex.conj_ofReal]; ring
lemma antic_K(i j: Site n)(x:Views)(o:Skye.Seat n): PayS (κviews o i j) x= star (PayS (κviews o j i) x.swap):=by
 unfold PayS; let L:= (pointF o i) x.1; let P:= (pointF o j) x.2; change Complex.exp (Complex.I*↑(-L+P))=(starRingEnd ℂ) (Complex.exp _); rw [← Complex.exp_conj,map_mul, Complex.conj_I]; change _=Complex.exp (-Complex.I*((starRingEnd ℂ) (↑(-P+L):ℂ))); rw [Complex.conj_ofReal]; congr 1; push_cast; ring
set_option maxHeartbeats 150000 in
lemma zenK (A:Op (Single n))(x:Views) : streamF o (-star A) h x= -star (streamF o A h x.swap):=by
 rw [streamS,streamS]; rw [sum_comm]; simp_rw [star_sum,← sum_neg_distrib]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [show matPH (-star A) _ _= -star (matPH A i j) from rfl, antic_K j i x o, smul_neg, star_smul, star_mul,star_mul,star_mul]; congr 2; rw [show star (Caller o i)= Caller o i from fee_real _,show star (Caller o j)=Caller o j from fee_real _, star_pow]; rw [show star (↑h:ℂ)=(↑h:ℂ) from Complex.conj_ofReal h]; ring
abbrev moveP (R:Signed)(b:Bool): Views→L[ℝ]Views := (candT R b).comp (if Spire.detX R then (ContinuousLinearEquiv.prodComm ..).toContinuousLinearMap else ContinuousLinearMap.id ℝ Views) -- tune
abbrev loom_P (s:Sweep n)(A:Op (Single n)):= Thera.jazz (detX s.s) (sings s.charge (siteU (castX s) s.charge (spinU s.charge s.s) n) A)
def ΔPal (R:Signed)(b:Bool)(A:Pal) := Thera.jazz (detX R) (sings b (twoU (spinU b R) b) A)
def LitF (F:Op (Single n))(o:Skye.Seat n) : Prop:=∀ i j, matPH F i j ≠0→10*separation (node i) o <(More n).val∧10*separation (node j) o<(More n).val
variable (M: Male)
def ℳPAL (R:Signed)(b:Bool): Pal→L[ℝ]Pal:=by
 let F:= ΔPal R b; refine LinearMap.toContinuousLinearMap ⟨⟨F,?_⟩,?_⟩
 · intro i j; unfold F ΔPal Thera.jazz; rw [singT,win_a,map_add]; split <;> simp only [star_add,neg_add, singT] <;> first| exact add_comm .. | rfl
 intro a i; change F (a • i)=a • F i; unfold F ΔPal Thera.jazz; rw [singT,win_r,map_smul]; split <;>simp [singT] -- tune
set_option maxHeartbeats 110000 in
lemma raysETF (H:LitF f o)(p:100<n.val): (TabX (sh s o) M h (loom_P s f))=ᶠ[𝓝 0] (fun i=> ΔPal s.s s.charge (TabX o M h f (moveP s.s s.charge i))):=by
 let R:=s.s; let q':=s.charge; let t:= detX R; let U:=spinU q' R; have hv:JetS R q' t U:=spinZ ..; let L:Pal→ Pal:= fun x=> sings q' (twoU U q') x; let P:=TabX o M h f
 let A:= baseF false; let B:=baseF true; let C:=binor M false; let D:=binor M true; have ht:=ballTP R M hv;
 filter_upwards [(show ∀ᶠ i:Views in 𝓝 0, i.1∈{i | (∀ k:Bool, L (binor M k (κcad R q' i))=binor M (t.xor k) i)} from continuous_fst.tendsto (0:Views)|>.eventually ht), (show ∀ᶠ i:Views in 𝓝 0, (∀ k:Bool, L (binor M k (κcad R q' i.2))=binor M (t.xor k) i.2) from continuous_snd.tendsto (0:Views)|>.eventually ht), (show ∀ᶠ i:Views in 𝓝 0, IsStarProjection (C i.1) from (continuous_fst.tendsto (0:Views)).eventually (palP M false)),(show ∀ᶠ i:Views in 𝓝 0, IsStarProjection (D i.2) from (continuous_snd.tendsto (0:Views)).eventually (palP M true))] with i x y c d
 have he(k:Bool): L (baseF k)=baseF (t.xor k):=QuadClock.step_Base hv _
 let F: Op (Single n):= sings q' (siteU (castX s) q' U n) f; have hz(x: Views): streamF (sh s o) F h x = L (streamF o f h (candT R q' x)):= StreamCull s f H p x -- tune
 have hp:F= F:=rfl
 have hmul (x y:Pal): L (x*y)=L x *L y:=by unfold L; simp only [singT,win_m,map_mul]; -- tune
 let Z:=moveP R q' i; have hA:star A=A:=(bladeSeal _).isSelfAdjoint -- tune field
 have hB:star B=B:= (bladeSeal _).2.star_eq
 change TabX _ _ _ _ i=ΔPal R q' (P Z)
 by_cases w:t
 · have hw: Z=candT R q' i.swap:=by unfold Z moveP; rw [if_pos w]; rfl
   let X:= C i.1; let Y:=D i.2; let v:= streamF o f h Z
   have hm: L A=B:=by unfold A; rw [he,w]; rfl
   have hb: L B=A:=by unfold B; rw [he,w]; rfl
   have hr: loom_P s f = -star F:= if_pos w
   have hc: L (C Z.1) = Y:=by rw [hw]; apply Eq.trans _ (show binor M (t.xor false) i.2=Y from (by rw [w]; rfl)); exact y _
   have hd: L (D Z.2)= X:=by rw [hw]; apply Eq.trans _ (show binor M (t.xor true) i.1=X from (by rw [w]; rfl)); exact (show ∀ k, L (binor M k (κcad R q' i.1))=binor M (t.xor k) i.1 from x) _
   have he: ΔPal R q' (P Z)= -star (L A*(L (C Z.1)*(L v*(L (D Z.2)*L B)))):=by
       change Thera.jazz t _ = _; rw [Thera.jazz,if_pos w]; simp_rw [←hmul]; try rfl
   rw [hr,he,hm,hc,hd,hb]; unfold TabX; rw [zenK,hz]; change A*(X*((-star (L (streamF o f h (candT R q' i.swap))))*(Y*B)))= -star (B*(Y*(L v*(X*A))))
   rw [←hw]; change A*(X*((-star (L v))*(Y*B)))= _; simp only [neg_mul,mul_neg,star_mul,hA,hB, show star X= X from c.2.star_eq, show star Y=Y from d.2.star_eq,mul_assoc] -- tune
 have hw: Z=candT R q' i:=by unfold Z moveP; rw [if_neg w]; rfl
 rw [hw]; let V:=candT R q' i; let v:=streamF o f h V; have he:ΔPal R q' (P V)=L A*(L (C V.1)*(L v*(L (D V.2)*L B))):=by change Thera.jazz t _=_; rw [Thera.jazz,if_neg w]; simp_rw [← hmul]; try rfl
 have hc:L (C V.1)= C i.1:=by
    apply Eq.trans _ (show binor M (t.xor false) i.1=C i.1 from (by cases h:t; rfl; contradiction)); exact (show ∀ k, L (binor M k (κcad R q' i.1))=binor M (t.xor k) i.1 from x) _
 have hd:L (D V.2)=D i.2:=by apply Eq.trans _ (show binor M (t.xor true) i.2=D i.2 from (by cases h:t; rfl; contradiction)); exact y _
 have hm(k:Bool): L (baseF k)=baseF k:=by unfold L; rw [QuadClock.step_Base hv]; cases h:t; simp; contradiction -- tune unfolding
 change TabX (sh s o) _ _ _ _=ΔPal R q' (P V); rw [he, hc, hd, show L B=B from hm _,show L A=A from hm _,show loom_P s f=F from if_neg w]; unfold TabX; rw [hz]; try rfl
-- κ orientations no-n data.
lemma moveJ0 (H:LitF f o)(p:100<n.val) : let P:= winJ o M h f
 winJ (sh s o) M h (loom_P s f)=postF (pre P (moveP s.s s.charge)) (ℳPAL s.s s.charge):=by
 intro P; symm; exact (((tab (o:=o) (h:=h) M f|>.preC (moveP s.s s.charge)).geomF (ℳPAL s.s s.charge)).equal (raysETF (h:=h) s M H p|>.symm)).unique (tab M _)
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
