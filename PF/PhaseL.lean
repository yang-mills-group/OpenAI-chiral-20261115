import PF.Folding
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
namespace PureForce
namespace CakeL
open Branch Hake Hive Pose Products WickLabels Bill Material Third Vessel Stars Set
variable {D O N:Type}[Fintype O][DecidableEq O][Fintype N][LinearOrder N][Nonempty N][TopologicalSpace D]{H:Host O N D}{ν:D→ℝ}
variable {a w B c r:ℝ}{S:Seal O}{X Y T:D→Op N}{F:D→ FC N}{q:D→Wave N}
private def xt (t:ℝ):= Real.exp t-1
private def exp_fee (r w:ℝ):= ∑' n:ℕ, (↑((n+1).factorial):ℝ)⁻¹*r*(w*r)^n
lemma after_exp (w':0 < w)(hv:∀ x,0≤ν x ∧ ν x ≤ w)(p:∀ x,IsStarProjection (X x))(t:∀ x,(Fock.Sea) (X x) (q x))(g:Shot H (fun _=>1) ∅ a B X)(d:0 ≤ a)
    (S':S.Nonempty)(eS:Grove H.space S)(hF:Docket H ν S a (Real.exp a+B) F c)(hD:Docket H ν S a (Real.exp a+B) (dg ∘ Y) r):
    let K:=(exp_fee r w)+c * (1+exp_fee r w*w); -- define below depends w! choose w≤1 or exp_fee r w w.
    Cred H ν S a (fun x=> (inner ℂ (q x) (acts (exp (dg (Y x))) (acts (1+F x) (q x))))-1) K:=by
 intro K
 let h0:=Real.exp a+B; have h1:1 ≤ h0:= (Real.one_le_exp d).trans (le_add_of_nonneg_right g.cost_pos)
 have hr':0≤r:= hD.nn (zero_le_one.trans h1)
 let G: D→FC N:= dg ∘ Y; let W(i:ℕ)(x:D):=((i+1).factorial:ℂ)⁻¹ • G x^(i+1); let Z(n:ℕ):ℝ:= (↑((n+1).factorial):ℝ)⁻¹*r*(w*r)^n
 have hz(n): Docket H ν S a h0 (W n) (Z n):= by
    have hu:= (hD.powers S' d (zero_le_one.trans h1) (fun x=>(hv x).1) w'.le (fun x=>(hv x).2) n).scale (((n+1).factorial:ℂ)⁻¹); apply hu.up; rw [norm_inv, Complex.norm_natCast]; unfold Z; rw [mul_assoc]
 have ho:Summable Z:=by
    have ht := ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial (w*r))).mul_right (1/w)
    apply ht.congr; intro n; unfold Z; rw [pow_succ',div_eq_mul_inv]; field_simp
 let f(x:D)(A:FC N):= inner ℂ (q x) (acts A (q x))
 let L(i:ℕ)(x:D):=f x (W i x)+ f x (W i x*F x)
 have hb(n):Cred H ν S a (L n) (Z n+Z n*c*w):=by
    have he:=Docket.cashier p t g d (hz n) S'; refine he.plus ?_
    have ht:= ((hz n).product hF S' (zero_le_one.trans h1) d).blur w'.le (Δ:=ν) (fun x=>mul_le_mul_of_nonneg_right (hv x).2 (hv x).1)
    exact Docket.cashier p t g d (ht.up (le_of_eq (mul_comm ..))) S'
 have hs:= Cred.infinite hb (ho.add ((ho.mul_right c).mul_right w)) d w w'.le hv
 let Μ(x:D):= exp (G x)
 have hX x: HasSum (fun n=>W n x) (Μ x-1):=by
    have v:= NormedSpace.expSeries_summable' (𝕂:=ℂ) (G x)
    unfold Μ; rw [exp_eq_tsum ℂ]; dsimp only; rw [←v.sum_add_tsum_nat_add 1,sum_range_one]; simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,add_sub_cancel_left]; exact ((summable_nat_add_iff 1).mpr v).hasSum
 have hli x :∃ V:FC N→L[ℂ]ℂ, (V:FC N→ℂ) = f x:=by
    exact ⟨(show FC N→ₗ[ℂ] ℂ from {
         toFun:=f x
         map_add' y z:= by unfold f; rw [act_add,inner_add_right]
         map_smul' y z:= by change f x (y • z)=y*f x z; unfold f; rw [act_smul,inner_smul_right]}).toContinuousLinearMap, rfl⟩
 have hQ(x:D): (inner ℂ (q x) (acts (exp (dg (Y x))) (acts (1+F x) (q x))))-1 = f x (F x) + ∑' n,L n x:=by
    obtain ⟨j,h⟩:=hli x; have hu:=hX x; have hm:=HasSum.add (hu.mapL j) ((hu.mul_right (F x)).mapL j) -- mapL
    have h0(j'):j j'=f x j':=congrFun h _
    simp only [h0] at hm
    rw [←act_mul]; change f x (Μ x*(1+F x))-1=_; rw [show (∑' n,L n x)=_ from hm.tsum_eq]
    have h1:f x 1=1:=by unfold f; rw [act_one,inner_self_eq_norm_sq_to_K,(t x).2]; simp
    rw [←h0 1] at h1; rw [←h0,←h0,←h0,←h0,show ((Μ x-1) * F x)= Μ x * F x-F x by rw [_root_.sub_mul,one_mul]]; simp only [mul_add,map_add, map_sub, mul_one,h1]; abel
 simp_rw [hQ]; refine ((Docket.cashier p t g d hF S').plus hs).up ?_; rw [ho.tsum_add ((ho.mul_right c).mul_right w), tsum_mul_right,tsum_mul_right]; change c+((exp_fee r w)+(exp_fee r w)*c*w) ≤ _; unfold K; exact le_of_eq (by ring)
-- simulator field CU etc. small license from studio.Lambda. Need send dg LK toll all ends, reach A. ν≤z strictly tested. Crop license. κ_rs formula.
variable (P: Spine)(s i k:ℕ)
set_option quotPrecheck false
local notation "Λ" =>P.par
local notation "Γ" =>P.run
local notation "cA" => ((Λ).d+(Λ).J.roomX)/2
local notation "m1" => Vale.mesh ((Γ).ir i) (Λ).R.L s
local notation "B1" => (Λ).block
local notation "NS"=> Papal.count (Γ) s i
local notation "I'"=> Single NS
local notation "φ"=> (Papal.gram (Γ) s i k).J
local notation "who" V:max =>changeM (m:=m1) (Λ).U V (φ).M

variable (n:Side)
-- use license at domain exactly same geometry, shift path only certified at radius rad.
local notation "Xn" => Single n
variable (e:gaugeLink n)(b:Bool)(R:Cascade.Interest n)(ω:ℕ){cA1 d z C a:ℝ}
local notation "D0" => Pose.Test n cA1 z
local notation "μ"=>tollZ (n:=n) cA1 z
local notation "H0"=>Pose.H n cA1 z
local notation "pad"=> Skye.ends e
-- not ξ dependent orientations here
lemma shift_dg (p:Products.RollKit n R ω cA1 z a C)(ha:0 ≤ a)(kind:Kind)(h:ℝ): Docket H0 μ pad a h (dg ∘ Products.read e b R ω kind) (C*h^2):=by
 obtain ⟨M,W,t⟩:= p (fun _=>b) kind
 have v: ∑ a':Xn,∑ b':Xn, saleM a (W e) a' b' ≤ C:=by rw [show a=2*a/2 by ring] ; exact t.all e
 exact Docket.distribute _ _ (t.shapes e) (t.total e) v ha

-- peers on twice radius, evaluated into today's host. cost at twice rate of roll enrollment.
lemma halve {d:ℝ}(p:Products.Peers n R ω d (2*z) (2*a) C)(hz:0≤z)(ha:0 ≤ a): Products.Peers n R ω d z a C:=by
 intro v b t Q h -- whnf one binder less? from Cred2
 let F:=Pose.Test n d z; let G:=Pose.Test n d (2*z)
 let k(x:F):G:= (x.1, ⟨x.2.val,x.2.property.trans (by linarith only [hz])⟩)
 have ht:Continuous k:=continuous_fst.prodMk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _)
 have hr u (h:Material.Shot (Pose.H n d (2*z)) (fun _=>1) ∅ (2*a) C u) : Material.Shot (Pose.H n d z) (fun _=>1) ∅ a C (u ∘ k):=by
    obtain ⟨Y,M,L,H,W⟩:= h.lower (show a ≤2*a by linarith)
    refine ⟨fun S=>Y S ∘ k,M,fun S=>⟨fun i j=> let Q:=(L S).block i j; ⟨Q.pos,Q.stake,fun _=>Q.load _, ?_,Q.listens.comp ht⟩⟩,H,fun x=>W _⟩
    intro x y b; unfold Function.comp; let v:=(L S).block i j; apply v.inputs; exact ⟨b.1, Subtype.ext (congrArg (fun x:{X:SU.group.Color // ‖X‖≤z}=> x.val) b.2)⟩
 obtain ⟨x,y⟩:= p v b Q h
 exact ⟨hr _ x,hr _ y⟩
-- packet for (1 + C) and both star companions.
def Qfee (t C:ℝ):=2*((Real.exp t + C)*C)*2*C
include e b
private lemma pre_P {d:ℝ}(p:Products.Peers n R ω d z a C)(ha:0≤a) :
    let V (x:Pose.Test n d z) := x.1.val;
    let y'(x):=1-curt R ω (V x); let m(x):=star (1+curt R ω (V x));
    Shot (Pose.H n d z) (fun _=>1) ∅ a (Real.exp a+ C) y' ∧ Shot (Pose.H n d z) (fun _=>1) ∅ a (Real.exp a+C) m:=by
 intro V y' m; have h:= (p e b (curt R ω) (by simp)).1; exact ⟨Shot.one.sub h,(Shot.one.plus h).starP⟩ -- tac e,b not include!
omit e b
section
variable {m B':Side}{L:Side}{j:ℕ}{o:Odd L.val}{Y':Paige.Pricing j L o (Vault.Thread j)}{δ:ℝ}(p':Paige.Grasp Y' B' δ)(J:Cascade.Interest (CSide m B')) (v:gaugeLink (CSide m B'))(b':Bool){d' z a C cd:ℝ}
local notation "M₀"=> CSide m B'
local notation "DO"=> Pose.Test M₀ d' z
local notation "V1"=> fun x:DO=>x.1.val
local notation "V'"=> after v b' (d:=d') (ε:=z)
local notation "q₁" x:max => changeM (m:=m) p' ((V1) x) J.M
local notation "Φe"=> fun x:DO=> Products.sheet J j .L ((V1) x) ((V') x)
local notation "spinL"=> fun x:DO=> Products.sheet J j .LK ((V1) x) ((V') x)
local notation "phaseE"=>fun x:DO=>inner ℂ (acts (quant (exp ((Φe) x))) (q₁ x)) (changeM (m:=m) p' ((V') x) J.M)

def phasef (z d:ℝ)(x:Pose.Test M₀ d z):ℂ := inner ℂ (acts (quant (exp (sheet J j .L x.1.val (after v b' x)))) (changeM (m:=m) p' x.1.val J.M)) (changeM (m:=m) p' (after v b' x) J.M)

local notation "cFee" => (Real.exp a + C)

private lemma port (w:License M₀ J j (2*z) d' δ a C)(hz:0<z)(hρ:0<a){K:ℝ}{I:Type}[Fintype I]{T:I→_}{F:I→_}{X:I→Pose.Test M₀ d' z→ℂ}{A:I→ℝ}(p:VistaDelta m B' p' J v b' d' z (cFee^2) cd K I T F X A)(hk:a≤ cd)
    (he:∀ x:DO,IsStarProjection (rolled J j x.1.val)):
    let C'(x:DO):=curt J j x.1.val;
    let V(x:DO):=1-C' x; let T'(x:DO):=1+C' x;
    let Ψ(x:DO):=(quant (V x)) * ((∑ i,X i x • Hive.drum (F i))) * quant (T' x);
    Docket (Pose.H M₀ d' z) (tollZ d' z) (Skye.ends v) a cFee Ψ K :=by
 intro C' V T' Ψ
 have hP:= halve M₀ J j w.extension hz.le hρ.le
 obtain ⟨hx,hy⟩:= pre_P M₀ v b' J j hP hρ.le
 have h0:0 ≤ C := ((hP v b' (rolled J j) (by simp)).1).cost_pos
 have hu:1 ≤ cFee := (Real.one_le_exp hρ.le).trans (le_add_of_nonneg_right h0)
 let Q:= Pose.H M₀ d' z
 let G(i:I)(x:DO):= X i x • (quant (V x)* Hive.drum (F i)*quant (T' x))
 let w'(i:I):=Branch.rent cd (T i)*((cFee^2)^(F i).length)*A i
 have hb(x:DO): C' x*C' x=0 :=by
    let Z:=rolled J j x.1.val; let W:=J.P.den x.1.val; have he: Z*(1-Z)=0:=by rw [_root_.mul_sub,mul_one,show Z*Z=Z from (he x).isIdempotentElem.eq,_root_.sub_self]
    change ( _*_*Z)*((1-Z)*W*Z)=0; rw [mul_assoc,←mul_assoc Z,←mul_assoc Z,he,zero_mul,zero_mul,mul_zero]
 have hp(x:DO):V x * T' x=1 ∧ T' x*V x=1:=by unfold V T'; constructor <;> noncomm_ring [hb x]
 have h(i:I) : Docket Q (tollZ d' z) (Skye.ends v) a cFee (G i) (w' i):=by
    obtain ⟨u,hG,_,l⟩:= p.shape i; let S:=Skye.ends v; have hn:S.Nonempty:=by unfold S Skye.ends; exact ⟨v.1, mem_insert_self ..⟩
    have ht:= Docket.torn V T' hx (by simpa only [star_star] using hy.starP) (fun x=>(hp x).1) (fun x=>(hp x).2) hρ.le (zero_le_one.trans hu) (F i) _ hG (hn.mono u) l -- T' unstar
    -- Tag including X all supports, cont
    have h':Bill.Tag Q (tollZ d' z) S (T i) (X i) (A i):= ⟨(p.price i).1,(p.price i).2,p.cont _,fun _ _ v=>p.reads i _ _ v.1 v.2,fun _=>⟨u,hG⟩⟩
    -- convert prefix left
    have hw:= Docket.gifted u h' hρ.le (zero_le_one.trans hu) ht
    have he:Branch.rent a (T i\ S) ≤Branch.rent cd (T i):=by unfold Branch.rent; have hh:= hρ.trans_le hk; gcongr; exact Finset.sdiff_subset
    refine hw.up ?_
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (p.price i).1) (by positivity)).trans_eq (by unfold w'; rw [pow_two]; ring)
 convert (Docket.summers univ G w' (fun i _=>h i)).up p.hire using 1
 funext x; unfold Ψ G; rw [mul_sum,sum_mul]; exact sum_congr rfl fun i _=> by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma bigCharge (w:License M₀ J j (2*z) d' δ a C)(hz:0<z)(hρ:0<a){K:ℝ}{I:Type}[Fintype I]{T:I→_}{F:I→_}{X:I→Pose.Test M₀ d' z→ℂ}{A:I→ℝ}
    (p:VistaDelta m B' p' J v b' d' z (cFee^2) cd K I T F X A)(hk:a≤ cd)(hU:p'.roundZ ≤ (M₀).val)(he:d'≤ δ):
    let r:= C * cFee^2; Cred (Pose.H _ d' z) (tollZ d' z) (Skye.ends v) a (fun x=>(phaseE) x - 1) (exp_fee r z + K * (1+exp_fee r z*z)):=by
 intro r
 let P(x:DO):Op (Single M₀):= rolled J j ((V1) x)
 let S:=Skye.ends v; let Z:=Pose.H M₀ d' z
 let γ(x:DO):= q₁ x
 let TL(x:DO):= curt J j x.1.val; let Y(x:DO):= quant (1-TL x); let Γk(x:DO):= quant (1+TL x)
 let Ψ(x:DO):= Y x*(∑ i,X i x • Hive.drum (F i))*Γk x
 let xₐ (x:DO):Pose.Test M₀ d' (2*z):=(x.1,⟨x.2.val,x.2.property.trans (by linarith only [hz])⟩)
 have hP(x): IsStarProjection (P x):=(w.fit v b' (xₐ x)).2.1
 have hΨ:= port p' J v b' w hz hρ p hk hP
 have rKit:= Products.repath J j (show z≤2*z by linarith only [hz]) w.inv
 have hd:= shift_dg M₀ v b' J j rKit hρ.le Kind.LK cFee
 have hγ(x:DO):(Fock.Sea) (P x) (γ x):= Spire.sea_g hU _ (x.1.property.shrink he) _
 have hp:= after_exp (ν:=tollZ d' z) hz (fun x:DO=> ⟨norm_nonneg (x.2.val),x.2.property⟩) hP hγ (show Shot Z (fun _=>1) ∅ a C P from ?P) hρ.le
    (show S.Nonempty from ⟨v.1,by unfold S Skye.ends; simp⟩) (show Grove (Tenant.terr _) S from ?G) (show Docket Z (tollZ d' z) S a cFee Ψ K from hΨ) hd
 convert hp using 1; funext x
 let q:= γ x; let y':= (V') x
 let k':=changeM (m:=m) p' y' J.M
 have hr:= algebraic J j w v b' (xₐ x); obtain ⟨t,tR,H1,H2,H3,H4,H5,H6⟩:=hr
 obtain ⟨_,_,H6⟩:= H6 q k' (hγ x) (Spire.sea_g hU y' ((w.fit v b' (xₐ x)).1) J.M); let M:= ∑ i,X i x • Hive.drum (F i)
 let C':=curt J j (x.1.val); let K':=curt J j y'; let Φ:=exp ((Φe) x)
 change t.val=Φ at tR
 let L(z:Pane M₀):=changeM (m:=m) p' z J.M
 have c_cut{z:Pane M₀}(X:IsStarProjection (rolled J j z)) : (curt J j z)*(curt J j z)=0:=by
    let U:=rolled J j z; have he:U*(1-U)=0:=by rw [_root_.mul_sub,mul_one,show U*U=U from X.isIdempotentElem.eq,_root_.sub_self]
    change (_*_*U)*((1-U)*_*U)=0; rw [mul_assoc,←mul_assoc U,←mul_assoc U,he,zero_mul,zero_mul,mul_zero]
 have nest_is{z:Pane M₀}(X:IsStarProjection (rolled J j z)): Hive.nest p' J.P J.M z=acts (quant (1+curt J j z)) (L z):= congrArg (fun w:FC (Single M₀)=> acts w (L z)) (Fock.tallied (curt J j z) (c_cut X))
 have hA: acts (1+M) (acts (quant (1+C')) q)=acts (quant (1+K')) k':=by
    have hv:= p.valuation x
    change acts (1+M) (Hive.nest p' J.P J.M _) = Hive.nest _ _ _ _ at hv
    rw [nest_is (hP x), nest_is (z:=after v b' x) (w.fit v b' (xₐ x)).2.2.1] at hv; exact hv
 have hs:=H6 _ hA
 change Stars.pay t q k'= _ at hs; unfold Stars.pay at hs; rw [tR] at hs
 change inner ℂ (acts (quant Φ) q) k' - 1 = _; rw [hs,←act_mul (1+M),←act_mul (quant _)]
 change inner ℂ q (acts (exp (dg ((spinL) x))) (acts (quant (1-C')*((1+M)*quant (1+C'))) q))-1=inner ℂ q (acts (exp (dg ((spinL) x))) (acts (1+Ψ x) q))-1
 rw [add_mul,one_mul,mul_add,←quant_mul, show Ψ x=quant (1-C')*M*quant (1+C') from rfl,mul_assoc (quant _),show (1-C')*(1+C')=1 by noncomm_ring [show C'*C'=0 from c_cut (hP x)],quant_one]
 case P=> exact ((halve M₀ J j w.extension hz.le hρ.le) v b' (rolled J j) (Or.inl rfl)).1
 case G=> unfold S Skye.ends; exact Grove.join (y:=v.1+step v.2) (.single _) (mem_singleton_self _) (Lat.oneTouch ..)
end
private lemma discount {n:Side}{R:Cascade.Interest n}{d z δ a C t:ℝ}{j:ℕ}(h:License n R j z d δ a C)(v:t ≤ a):License n R j z d δ t C:=by
 refine ⟨ Products.Cheap_roll R j v le_rfl h.inv, ?_, h.fit⟩
 intro u b Z f p; obtain ⟨k,l⟩:= h.extension u b f p; exact ⟨k.lower (by linarith),l.lower (by linarith)⟩

variable (h:Solstitial P.par)(p:Fountain P.par)
include h p
-- public with attachments. $H'$ named APR. Recover LP.7 $s,i,k$ oriented full Gate etc, still no gauge average for zero derivative. 
local notation "nnB" s:max i:max=> Papal.count (Γ) s i
local notation "fB" s:max i:max k:max=> (Papal.gram (Γ) s i k).J
lemma endowment :∃ z a C:ℝ, 0<z∧0<a∧0<C∧∀ s:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s≤ (Γ).uv k→
    -- termwise list priced card, no relative instead of absolute. across all e individually not demanding sum_e c. Same receipt if wanting use on any ordered pulls etc use separately assigned terms.
    (Pose.Products.License (nnB s i) (fB s i k) (Λ).K.j (2*z) cA (Λ).d a C) ∧
    (∀ x:Orbit (nnB s i), Cube.Guard (Papal.room (Γ) s i x) cA) ∧
    ∀ (e:gaugeLink (nnB s i))(b:Bool),∃ (Y:Seal (Seat (nnB s i))→ Pose.Test (nnB s i) cA z→ℂ)(D:Seal (Seat (nnB s i))→ℝ),
      (∀ S:Seal (Seat (nnB s i)),Bill.Tag (Pose.H (nnB s i) cA z) (tollZ cA z) (Skye.ends e) S (Y S) (D S)) ∧
      (∑ S:Seal (Seat (nnB s i)),Branch.rent a S *D S)≤C ∧
      ∀ x,phasef (m:=Vale.mesh ((Γ).ir i) P.par.R.L s) (Λ).U (fB s i k) e b z cA x = 1+∑ S,Y S x:=by
 obtain ⟨z,c,C,r,vZ,vC,gC,t,hZ⟩:= studio P h p; let a:=min c r; have ha:0<a:=lt_min vC t; let K:= Real.exp a+C
 have hk:1 ≤ K:= (Real.one_le_exp ha.le).trans (le_add_of_nonneg_right gC.le)
 obtain ⟨κ,w,W⟩:=hZ (K^2) (one_le_pow₀ hk)
 let L:=exp_fee (C*K^2) z + κ*(1+exp_fee (C*K^2) z*z)
 let D:=max C (Real.exp (a*2)*L)
 refine ⟨z,a,D,vZ,ha,gC.trans_le (le_max_left ..), fun s=> (W s).mono (fun i x k q=> ?_)⟩
 let m:=Vale.mesh ((Γ).ir i) P.par.R.L s; let N:=nnB s i; let J:= fB s i k
 obtain ⟨hw,hG,hN,hs⟩:= x k q; let Q:= discount hw (show a≤c from min_le_left ..); have hi:C≤ D:=le_max_left ..
 have hEd: License N J (Λ).K.j (2*z) cA (Λ).d a D:=by
    refine ⟨Products.Cheap_roll J (Λ).K.j le_rfl hi Q.inv,?_,Q.fit⟩
    intro T b V f h; obtain ⟨s,u⟩:=Q.extension T b f h; exact ⟨s.relax hi,u.relax hi⟩
 refine ⟨hEd,hG,fun e b=>?_⟩
 obtain ⟨I,tI,T,F,B,A,R⟩:= hs e b; letI:=tI
 let S:= Skye.ends e; let M:=Pose.H N cA z; let p:=phasef (m:=m) (Λ).U J e b z cA
 have hp:Cred M (tollZ cA z) S a (fun v=> p v-1) L := bigCharge (m:=m) (Λ).U J e b Q vZ ha R (show a ≤ r from min_le_right ..) hN (by linarith only [(Λ).J.hr])
 obtain ⟨Y,Q',o,k,H⟩:=Cred.compress hp
 refine ⟨Y,Q',o,le_trans ?_ (le_max_right ..),fun i=>?_⟩
 · refine le_trans (b:=Real.exp (a*2)*(∑ s:Seal (Seat N),Branch.rent a (s\S)*Q' s)) ?_ (mul_le_mul_of_nonneg_left k (Real.exp_pos _).le)
   rw [mul_sum]; apply sum_le_sum; intro X _; by_cases he:Q' X=0; simp [he]
   let V:=(o X).resource he; have hx:= Finset.card_sdiff_add_card_eq_card V.1; have hv:S.card≤2:= by unfold S Skye.ends; exact (card_insert_le ..).trans (by simp)
   rw [←mul_assoc]; unfold Branch.rent; rw [←Real.exp_add]; gcongr; · exact (o X).pos
   have hh: (X.card:ℝ) ≤ 2+((X\S).card:ℝ):=by exact_mod_cast (show X.card ≤2+(X\S).card by omega)
   nlinarith [mul_le_mul_of_nonneg_left hh ha.le]
 have he:p i-1=_:=H i; change p i=_; rw [←he]; abel
end CakeL
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
