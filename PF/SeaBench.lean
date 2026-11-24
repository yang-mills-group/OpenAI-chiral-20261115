import PF.Pose
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.Stars
open Dial Pastry Set
-- fixed-universe I supports Single n, ok.
variable {I:Type} [LinearOrder I][Fintype I][Nonempty I]{A B:Op I}
lemma quant_lift (A:Op I) : exp (dg A)=quant (exp A):=by
 let Q(t:ℝ):= exp (t • A)
 let X:=dg A; let W(t:ℝ):= exp (-t • X)
 have ht(t:ℝ):HasDerivAt Q (A * Q t) t:=by rw [((Commute.refl A).smul_right t|>.exp_right).eq]; exact hasDerivAt_exp_smul_const A _
 have hz(t:ℝ):HasDerivAt W (-(W t * X)) t:=by
    have he:= (hasDerivAt_exp_smul_const X (-t:ℝ)).scomp t ((hasDerivAt_id' t).neg)
    simpa only [W,Function.comp_def,neg_smul,one_smul] using he
 let V(t:ℝ):= quant (Q t)
 letI : NormedAlgebra ℚ (FC I):= NormedAlgebra.restrictScalars ℚ ℂ _
 have hf : W 1 * V 1 = 1:=by
    apply op_columns; intro s
    let e:= (basisKet s:Wave I); let F(t:ℝ):=acts (W t) (acts (V t) e)
    have hh (t:ℝ): HasDerivAt F 0 t:=by
      have he:=BPress.Pf.Rotate.d_mult (hz t) (BPress.Pf.Rotate.d_quant (ht t) e)
      apply he.congr_deriv; change acts (-(W t*X)) _+acts (W t) (acts X _)=0; rw [act_neg,act_mul,neg_add_cancel]
    have hw : F 1=F 0:=by
       apply sub_eq_zero.mp; exact Eq.trans (intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (fun x _=> hh x) (by simp)).symm (by simp)
    rw [act_mul]; change F 1=acts 1 e; simpa only [F,V,Q,W,neg_zero,zero_smul,exp_zero,quant_one,act_one] using hw
 rw [show W 1 = exp (-X) by unfold W; rw [neg_smul,one_smul],show V 1=quant (exp A) by unfold V Q; rw [one_smul]] at hf
 rw [show exp (dg A) = exp X * 1 by rw [mul_one],←hf,←mul_assoc,←exp_add_of_commute ((Commute.refl _).neg_right),add_neg_cancel,exp_zero,one_mul]

-- scalar phase is pulled back *by* Γ(U) since y_Z is in image. linear in shifted Y.

def pay (U: UNI I)(x y:Wave I):ℂ:=inner ℂ (acts (quant U.val) x) y
lemma phase_act (U:UNI I)(h:IsStarProjection A)(e: twist U A=B) {x y: Wave I}(v:Fock.Sea A x)(t:Fock.Sea B y): y=pay U x y • acts (quant U.val) x ∧ ‖pay U x y‖=1 :=by
 let Z:= (quantU U).val; let m:= acts Z x; have hx:‖m‖=1:=(act_unit_norm (quantU U) x).trans v.2
 have hg: acts (lineOp B) y=y:=t.1
 have hs : acts (lineOp A) (acts (star Z) y)=inner ℂ x (acts (star Z) y) • x := Fock.Sea.scalar h v _
 have ht: y= acts Z (acts (lineOp A) (acts (star Z) y)):=by
   rw [←act_mul Z,←act_mul,←twist_formula,←line_twist U A,e,hg]
 rw [hs, map_smul] at ht; unfold pay
 have hd : ⟪x,acts (star Z) y⟫_ℂ=⟪m,y⟫_ℂ:=by simpa only [star_star,m] using (act_inner (star Z) x y).symm
 rw [hd] at ht
 refine ⟨ht,?_⟩
 have hr:=congrArg norm ht; change ‖y‖= ‖(inner ℂ m y) • m‖ at hr; rw [norm_smul,hx,mul_one,t.2] at hr; exact hr.symm
-- paintS and tank convention on proper orientation link transport. Pass also through odd generators directly by twist_create/remove; the exterior `ribbon` use is even in actual Lean.
lemma tank_motion {U: UNI I}(h:IsStarProjection A)(q:IsStarProjection B)(e:U.val*A=B*U.val)(F:Pastry.ribbon I):
  let V:=quant U.val; star V * tank B F * V=tank A (paintR false false (star U) F) :=by
 let V:=quant U.val
 have ht : star U.val*B*U.val=A:=by rw [mul_assoc,←e,←mul_assoc,show star U.val*U.val=1 from U.property.1,one_mul]
 have hp:sings false (star U) B=swapX false A:=by change twist (star U) B=A; rw [twist_formula]; change star U.val*B*star (star U.val)=_; rwa [star_star]
 intro V'; rw [tank_eq _ _ h,tank_eq _ _ q,←appleT q h false false (star U) hp]; change _=twist (quantU (star U)) _; rw [twist_formula]; simp only [quantU_star, show (↑(star (quantU U)):FC I)=_ from rfl]; change _=star V * _ *star (star V); rw [star_star]; rfl

lemma improper {U g:UNI I}{L:Op I}(h:star L= -L)(t:Matrix.trace L=0)(e:U.val=exp L): theta g (quant U.val)=quant (twist g U.val):=by
 rw [e, ←quant_lift,← Buffered.Heat.theta_exp,theta_dg,t,star_zero,zero_smul,zero_sub,h,map_neg,dg_neg,neg_neg,quant_lift, breeze_exp]

-- LZ.6 exact algebra. scalar phase convenience lp; L log inputs $W$. orientation unitaries. CK. σ from LP.6 unscaled. 
private lemma cancels {A:Op I}(h:A*A=0) : (1-A)*(1+A)=1 ∧ (1+A)*(1-A)=1:=by
 constructor <;> noncomm_ring [h]
lemma phase_recipe (U:UNI I) (x y:Wave I)(C D K:Op I)(op: FC I)
    (h:Fock.Sea A x)(hc:C*C=0)(hd:D*D=0) (hw:1+K=star U.val*(1-D)*(1+C))(p:‖K‖<1)
    (v: acts op (acts (quant (1+C)) x)=acts (quant (1+D)) y):
    pay U x y=inner ℂ x (acts (exp (dg (Branch.pencil K)))
      (acts (quant (1-C)) (acts op (acts (quant (1+C)) x)))):=by
  unfold pay; nth_rw 1 [← star_star (quant U.val)]; rw [act_inner, ← quant_star,v,quant_lift,Near.pencil_exp K p,hw]
  rw [←act_mul (quant (1-C)),←act_mul,←quant_mul,←quant_mul]
  congr; rw [mul_assoc (star U.val*(1-D)),←mul_assoc (1+C), (cancels hc).2,one_mul,mul_assoc,(cancels hd).1,mul_one]
-- Complete algebra bank on that same Arc in project P.Papal.
variable {n:Side}(R:Cascade.Interest n)(ω:ℕ)
local notation "S" => Single n
local notation "W"=>Pane n
open Pose.Products Pose
private lemma colour_sq (V:Pane n)(h:IsStarProjection (rolled R ω V)):curt R ω V * curt R ω V=0 :=by
 let P:=rolled R ω V; let T:=R.P.den V; have he:P*(1-P)=0:=by rw [mul_sub,mul_one,show P*P=P from h.isIdempotentElem.eq,sub_self]
 change ( _* _*P)*((1-P)*_*_)=0; simp_rw [mul_assoc]; rw [←mul_assoc P,he]; simp

/-- Input transfer, orientation receipt and phase formula. On `read v B R L Kck` EXACT operations before Gate. Crunch includes Vista simple issuance H3 below when bought. -/
lemma algebraic {c C z d e:ℝ}(h:Products.License n R ω z d e c C) (i:gaugeLink n)(β:Bool)(x:Pose.Test n d z) :
    let P:=rolled R ω x.1.val; let V:=after i β x; let Q:=rolled R ω V;
    ∃ U:UNI S,U.val= rotation R ω x.1.val V ∧ U.val*P=Q*U.val ∧
    exp (dg (arcLog R ω x.1.val V))=quant U.val ∧ Matrix.trace (arcLog R ω x.1.val V)=0 ∧
    (∀ g:UNI S,theta g (quant U.val)=quant (twist g U.val)) ∧
    (∀ f:Pastry.ribbon S, star (quant U.val)*tank Q f*quant U.val=tank P (paintR false false (star U) f)) ∧
    ∀ y y':Wave S, Fock.Sea P y → Fock.Sea Q y' →
    y' = pay U y y' • acts (quant U.val) y ∧ ‖pay U y y'‖=1 ∧
    let C':=curt R ω x.1.val; let D':=curt R ω V;
    ∀ F:FC S,acts F (acts (quant (1+C')) y)=acts (quant (1+D')) y' →
    pay U y y'=inner ℂ y (acts (exp (dg (sheet R ω .LK x.1.val V)))
      (acts (quant (1-C')) (acts F (acts (quant (1+C')) y)))):=by
 intro P V Q
 obtain ⟨_,p,g,v,q⟩:= h.fit i β x
 obtain ⟨t,_,s,u,_,j,k⟩:= Near.ribbon P Q p g v
 let L:=arcLog R ω x.1.val V; let T:=rotation R ω x.1.val V; let U: UNI S:= ⟨T,u⟩
 refine ⟨U,rfl,j,quant_lift L,s,fun d=> improper (L:=L) t s (show U.val=_ from rfl),fun f=>tank_motion (U:=U) p g j f,fun y y' a b=>?_⟩
 obtain ⟨ha,hb⟩:=phase_act U p (show twist U P=Q from by rw [twist_formula,show U.val*P= _ from j,mul_assoc,show Near.sling P Q= U.val from rfl,U.property.2,mul_one]) a b
 refine ⟨ha,hb,fun f l=> phase_recipe U y y' _ _ (correction R ω x.1.val V) f a (colour_sq R ω _ p) (colour_sq R ω V g) ?_ (q.trans_lt (by norm_num)) l⟩ -- let fun f binder? after 2 tuple result adds C' D'. fun coerced after reducing let, whnf q
 unfold correction; change 1+(star T* _ *_-1)=_; abel

-- uses same Papal choices; expose tuple incl P, actual Sea phase change_{m,P} kept, after all physical orientations.
variable (P:Spine)
local notation "Λ" =>P.par
local notation "Y"=>P.run
local notation "cA" =>(P.par.d+P.par.J.roomX)/2
local notation "Ns" i:max s:max => Papal.count (Y) s i
set_option quotPrecheck false
local notation "Φ" s:max i:max k:max =>(Papal.gram (Y) s i k).J
local notation "roomA" s:max i:max=>Papal.room (Y) s i
local notation "personify" s:max i:max k:max => (fun (V:Pane (Ns i s))=>changeM (m:=mesh ((Y).ir i) P.par.R.L s) P.par.U V (Φ s i k).M)
/-- Pose-local ruler and exact material phases/Gram/tank transmission, matching on
    every actual single-toggle reading (LZ.1,LZ.3–4,LP.4,all kernel matrices of LZ.5 including incidence); no assumption of already proving the CCR nor omitting the Ψ phase. -/
theorem loaned (h:Solstitial (Λ)):∃ z c C:ℝ,0<z∧0<c∧0<C∧
    ∀ s:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s≤ (Y).uv k →
    Products.License (Ns i s) (Φ s i k) (Λ).K.j z cA (Λ).d c C ∧
    (∀ t:Orbit (Ns i s),Guard ((roomA s i) t) cA) ∧
    ∀ (p:gaugeLink (Ns i s))(b:Bool)(x:Pose.Test (Ns i s) cA z),
    let V:Pane (Ns i s):=x.1.val; let W':=after p b x;
    let A:=rolled (Φ s i k) (Λ).K.j V; let B:=rolled (Φ s i k) (Λ).K.j W';
    let t:= (personify s i k) V; let y:= (personify s i k) W';
    let T:= curt (Φ s i k) (Λ).K.j;
    let L:=arcLog (Φ s i k) (Λ).K.j V W';
    ∃ U: UNI (Single (Ns i s)), U.val=exp L ∧ U.val*A=B*U.val ∧ quant U.val=exp (dg L) ∧ Matrix.trace L=0 ∧
    (∀ g:UNI (Single (Ns i s)), theta g (quant U.val)=quant (twist g U.val)) ∧
    (∀ F:Pastry.ribbon (Single (Ns i s)),star (quant U.val)*tank B F*quant U.val=tank A (paintR false false (star U) F)) ∧
    y = pay U t y • acts (quant U.val) t ∧ ‖pay U t y‖=1 ∧
    ∀ F:FC (Single (Ns i s)),acts F (acts (quant (1+T V)) t)=acts (quant (1+T W')) y→
    pay U t y=inner ℂ t (acts (exp (dg (sheet (Φ s i k) (Λ).K.j .LK V W'))) (acts (quant (1-T V)) (acts F (acts (quant (1+T V)) t)))):=by
 obtain ⟨z,c,C,l,e,t,H⟩:=assigned_rulers P h; refine ⟨z,c,C,l,e,t,fun s=>?_⟩
 filter_upwards [H s] with i p k g; obtain ⟨hV,hW,hK⟩:= p k g
 have hz:0 ≤ (Λ).d:= (Λ).dpos.le; have hu:(Λ).J.roomX ≤ cA :=by linarith only [(Λ).J.hr]
 have hg:cA ≤ (Λ).d:=by linarith only [(Λ).J.hr]
 refine ⟨hV,fun t=>Cube.Guard.shrink (hW t) hu,?_⟩
 intro e b x V W' A B m r S' F
 have hp:= algebraic (Φ s i k) (Λ).K.j hV e b x; obtain ⟨U,hw,h,r1,r2,E,z',H'⟩:=hp
 obtain ⟨q,_,-,v,n⟩:=hV.fit e b x
 obtain ⟨g,G,K⟩:=H' m r (sea_g hK V (x.1.property.shrink hg) _) (sea_g hK W' q _)
 exact ⟨U,hw,h,r1.symm,r2,E,z',g,G,K⟩
end PureForce.Stars
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
