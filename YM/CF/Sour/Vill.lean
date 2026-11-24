import YM.CF.Sour.Age
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
def flit(x:↥(Openc (More n) a)): ↥(Openc (More n) a):=⟨ice x.val,ice_o x.val a x.property⟩
def glaze(F:Raw ↥Ω JS)(x:↥Ω): Op JS:=star (F (flit a x))
lemma bits(Z:Toll JS)(S: SO)(F:Raw ↥Ω JS)(p:Suite (badge _) (bail n a) (bail n a) S Z F):Suite (badge _) (bail n a) (bail n a) S (Function.swap Z) (glaze a F):=by
 let K:=forum n a; let L:=bail n a; let f:=flit (n:=n) a
 have ht(g d):f (K.drive g d)=K.drive g (f d):=Subtype.ext (icy_g ..)
 have hv(X:Toll JS)(d e:↥Ω):K.eval S (f d) (f e)=K.eval S d e:=by change fare S (ice d.val) (ice e.val) / _ = _; rw [ice_f]; rfl
 have he:Ticket L L S Z (fun x=>F (f x)):=⟨fun g x=>by rw [ht]; exact p.frame ..,fun i j=> ⟨(p.expo i j).positive,(p.expo i j).triggered,fun x=>(p.expo i j).bounded _,fun d e=>(p.expo i j|>.variation (f d) (f e)).trans_eq (by rw [hv Z]), (p.expo i j).connected.comp (Continuous.subtype_mk (burnOut.comp continuous_subtype_val) _)⟩⟩
 refine ⟨he.starT,fun i j=>?_⟩; exact realigns (p.fuel j i) f (fun V e γ g=> snowy e (fun z=>(γ z).val) g)
-- P where orientation True intercept star or -star
abbrev det_S(s:Sweep n):=detX s.s
abbrev cutR (k:Bool)(X: Op JS):Op JS:= if k then -X else X
def trackV (s:Sweep n)(b:Bool)(a:ℝ)(F:Raw (Openc (More n) a) (Single n))(x: Openc (More n) a):=if det_S s then cutR b (glaze a (Mx s a F) x) else Mx s a F x
def testV(s:Sweep n)(b:Bool)(F:Support (More n)→Toll JS)(x:Support (More n)):=if det_S s then Function.swap (tagR s F x) else tagR s F x
lemma seeS(S: SO):actY s⁻¹ (actY s S)=S:=by ext; simp [actY,sitU]
variable {κ:Type}[TopologicalSpace κ]{Q:Support (More n)→ κ→ Raw (Openc (More n) a) (Single n)}(F:Support (More n)→Toll (Single n))(b:Bool)(p:∀ x,pendB (badge _) (bail n a) (bail n a) (Q x) x (F x))
include p
lemma veil(S:SO):pendB (badge _) (bail n a) (bail n a) (fun i=>trackV s b a (Q (actY s S) i)) S (testV s b F S):=by
 let Y:=actY s S; let Cv(x y):Op JS:= Mx s a (Q Y x) y
 have h(x:κ): Suite (badge _) (bail n a) (bail n a) S (tagR s F S) (Cv x):=by
    have hv:= mini s a _ (F Y) (p Y|>.1 x); rw [show actY s⁻¹ Y=S from seeS ..] at hv; exact hv
 have hx(y:↥Ω):Continuous fun i=>Cv i y:= (show Continuous (ech s⁻¹) from (Fock.breeze _).comp (typ_l _)).comp ((p Y).2 _)
 unfold trackV testV; split_ifs with t; swap; · exact ⟨h,hx⟩
 let L(x y):Op JS:= star (Cv x (flit a y)); have he(y):Continuous fun i=>L i y:=(hx _).star
 have hz(x:κ):Suite (badge _) (bail n a) (bail n a) S (Function.swap (tagR s F S)) (L x):=bits a _ S _ (h _)
 cases b; exact ⟨hz, he⟩; refine ⟨fun i=>?_ ,fun y=>(he _).neg⟩; change Suite _ _ _ _ _ (fun x=> -L i x); simpa using (hz i).accel (-1)
omit p
include p
lemma wardK [Nonempty κ]{a' c:ℝ}(h:Ledger a' F c):Ledger a' (testV s b F) (Tenant.quota^2*c):=by
 have he:= grainK s F (fun S=> (p S|>.1 (Classical.arbitrary κ)).nonn) h; unfold testV; split_ifs; exact he.flip; exact he
omit p
abbrev realR(s:Sweep n)(b:Bool)(F:Op JS): Op JS:= if b then bolt s F else foeL s F
lemma flag_det : det_S s⁻¹=det_S s:=by
 have he: ((det_S s).xor (det_S s⁻¹))=false:=by rw [det_S,det_S,←det_p]; rw [show s.s*(s⁻¹).s=(s*s⁻¹).s from rfl,mul_inv_cancel]; exact det_i -- tune
 cases x:det_S s⁻¹ <;> cases p:det_S s <;>simp [x,p] at he ⊢
lemma vale_d(s t:Sweep n)(b:Bool)(F:Op JS): realR t b (realR s b F)= realR (s*t) b F:=by
 have he:det_S (s*t)=(det_S s).xor (det_S t):=det_p ..
 let f(r e:Bool)(U:Op JS):= if r then cutR e (star U) else U
 have ht(s:Sweep n)(U:Op JS):realR s b U=f (det_S s) b (ech s U):=by cases b <;>simp only [realR,ite_true,Bool.false_eq_true,ite_false,bolt,foeL,Sault.hitL,Sault.doveL,Thera.jazz]; rfl; rfl
 have hp(r:Bool)(U:Op JS):ech t (f r b U)=f r b (ech t U):=by unfold f cutR ech; cases r <;> cases b<;>simp [map_star]
 rw [ht,ht,ht, hp,paceK,he]; cases ht:det_S s <;> cases hs:det_S t <;> cases b <;> simp [f,cutR]
lemma real_i (X:Op JS): realR 1 b X=X:=by
 have hp:det_S (1:Sweep n)=false:=det_i; unfold realR; split; exact (show Thera.jazz (det_S _) (ech _ X)=_ from by rw [hp,beat_x]; rfl); rw [foeL,doveL,show detX _=false from hp,show sings _ _ X=X from beat_x ..]; rfl
lemma tiles (x:↥Ω)(U:Pane n)(t:x.val=Tulip.profile U)(F:Raw (Openc (More n) a) (Single n)): trackV s b a F x= realR s⁻¹ b (F (fog s a x)):=by
 unfold trackV; split
 next h=> have he:flit a x=x:= by apply Subtype.ext; change ice x.val= x.val; rw [t,ice_pr]
          have hp: detX (s⁻¹).s=true:= (flag_det s).trans h
          cases b <;> simp [cutR,realR,bolt,foeL,Sault.hitL,Sault.doveL,Thera.jazz, hp,glaze,he,Mx] <;> rfl
 next h=> have hp:detX (s⁻¹).s=false:= (flag_det s).trans (by simpa using h)
          cases b <;>simp only [realR,bolt,foeL,Sault.hitL,Sault.doveL,Thera.jazz,hp,ite_false,Bool.false_eq_true,ite_true] <;> rfl
end YM.CF.Sour
