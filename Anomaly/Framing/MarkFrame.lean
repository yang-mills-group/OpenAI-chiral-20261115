import Anomaly.Framing.Moray
import Anomaly.Framing.Convoy
import YM.CF.Buffered.RiseReflect
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered
open Function Fock NormedSpace SU Lat Lattice Finset Cube Spire MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Sour Ione Ione.Clock Turning Hake Hive Levier Salt Swell Vow
variable {n:Side}(s:Sweep n) (S:Support (More n))
local notation "T"=>actY s S
local notation "Xω"=>γS s

def flyMark (s:Sweep n)(F:Mark n) : Mark n :=fun x=> Hive.teen s (F (flashA s⁻¹ x.1,flashA s⁻¹ x.2))
lemma fliesTransport (F:Mark n)(x y:Pane n) : flyMark s F (flashA s x,flashA s y)=Hive.teen s (F (x,y)):=by unfold flyMark; rw [revB,revB]
lemma fliesCombine (t:Sweep n){F:Mark n}(p:AtSupport false S F) : flyMark t (flyMark s F)=flyMark (s*t) F:=by
  funext x; unfold flyMark; rw [yetL s t _ (paritySale.checked (p.allV _).sector),lights,lights,mul_inv_rev] -- tune

variable {V:Mark n}
lemma whirl_step (h:s.charge=false)(p:AtSupport false S V) : AtSupport false T (flyMark s V):=by
 let K:=s⁻¹; let f(x:Fields n):= V (flashA K x.1,flashA K x.2); refine ⟨Girt.pole_w f (Hive.teen s) (Scree.tour_c .. ) (Env.along p.env (((revM K).measurable.comp measurable_fst).prodMk ((revM K).measurable.comp measurable_snd))),?_,fun x=> whirl_fine s _ h (p.allV _)⟩ -- namespace
 intro x y u w; have hx(g v:Pane n)(p:Agrees T g v): Agrees S (flashA K g) (flashA K v):=by
    have he: S.map (boxA K).toEmbedding=T:=by unfold K; rw [sitU]
    exact flashD K _ _ _ (he.symm ▸ p)
 exact congrArg (Hive.teen s) (p.dep _ _ (hx _ _ u) (hx _ _ w))
lemma fly_norm (h:s.charge=false)(x:FC (Single n)): ‖Hive.teen s x‖=‖x‖:=by
    let H:= Xω; change ‖Spire.tourP H s.charge (detX s.s) x‖=_; rw [h]; cases detX s.s
    · exact (twist_norm (quantU H) x)
    change ‖theta H x‖=_; rw [theta,twist_norm,norm_cc]
lemma spectral_mark (sW:s.charge=false){o o':Site n}{b:ℕ}{v:ℝ}(p:WindowTag V o b v)(h: (boxA s).symm (node o)=node o'):
    WindowTag (flyMark s V) o' b v := by
  let A:= offsetMask b o
  have ht:actY s A=offsetMask b o':=by unfold A actY offsetMask; rw [←sitU,←paysT,map_singleton, sitU, show (boxA s).symm.toEmbedding (node o)=_ from h]
  refine ⟨ht ▸ (whirl_step s A sW p.ticket),?_,?_,fun x y u=> ?_⟩ -- same.first
  · intro G x; let a:= s⁻¹; let y:Orbit n:=Classical.arbitrary _; let F:=tollPull a y G; let U:Fields n:=(flashA a x.1, flashA a x.2)
    change Hive.teen s (V (flashA a (Lattice.gauge G x.1),flashA a (Lattice.gauge G x.2)))= _
    rw [show (flashA a (Lattice.gauge G x.1),flashA a (Lattice.gauge G x.2))=simultaneous F U from Prod.ext (revG a x.1 G) (revG a x.2 G), p.rolls]
    have hv: tollPull s y F=G:=by have ht:=kind_R a y G; change tollPull s⁻¹⁻¹ y F=G at ht; rwa [inv_inv] at ht
    let K:= Hive.teen s
    have he: K (Gaze F (V U))= Gaze (tollPull s y F) (K (V U)):= Hive.yoT s F _ (paritySale.checked (p.ticket.allV _).sector)
    rw [hv] at he; exact he
  · intro x
    exact (show ‖_‖=_ from fly_norm s sW (V (flashA s⁻¹ x.1,flashA s⁻¹ x.2))).trans_le (p.price _)
  exact congrArg (Hive.teen s) (p.pane _ _ (congrArg (flashA s⁻¹) u))

namespace Advance
lemma with_tag_i(V:Pane n)(i:Axis)(u:ℤ) : flashA (tagMove i u n)⁻¹ V=fling i u n V:=by
 nth_rw 1 [←fling_invol i u V]; nth_rw 1 [←with_tag]; rw [revB]
lemma flies_theta (i:Axis)(u:ℤ){V:Mark n} (p:AtSupport false S V) : flyMark (tagMove i u n) V=reflMark i u V:=by
  let P:=plane i u; let s:=tagMove i u n
  have e: s=Levier.ray (N:=n) false P:=rfl
  funext x; change Hive.teen s (V _)=_; unfold tagMove at s
  let M:=V (fling i u n x.1, fling i u n x.2); let Q:= paritySale.checked (p.allV (fling i u n x.1,fling i u n x.2)).sector
  change Hive.teen (tagMove i u n) (V _)= theta (carR i u n) M
  rw [with_tag_i,with_tag_i] -- tune S explicit
  change yodel false (castX (Levier.ray (N:=n) false P)) M= _; rw [hono false P M Q]; unfold yodel
  rw [stag_s false P _ (Window.pinLift i) _ Q (spinZ ..) ?_, show detX P.s = true from det_t i]
  rfl
  rw [show detX P.s=true from det_t i]; exact mirrorX i
end Advance

lemma whirl_contact (K:Scree.Loom n){Y:Swell.phy n}(p:Contact K S V Y)(h:s.charge=false)(pv:∀ x y:Fields n,x.1=y.1→V x=V y) :
    Contact K T (flyMark s V) (cartPrice s Y):=by
  refine ⟨whirl_step s S h p.pitch,fun x=> Whirl_stay s S h (p.oscillator _),?_⟩
  intro x; obtain ⟨X,rfl⟩:=yspec s x
  let K':=yellA s X
  let Q:=arum Xω s.charge (detX s.s) (mateK _)
  have he:flyMark s V (K'.1,K K')=Hive.teen s (V (X.1,K X)):=by
    unfold flyMark; exact congrArg (Hive.teen s) (pv _ _ (revB ..))
  have hv(f:FC (Single n)): teen s (star f)=star (teen s f):=by
    let U:= Xω; let a:= s.charge; let r:=detX s.s; change Spire.tourP U a r _=star (Spire.tourP U a r _); cases r
    · change twist _ (windX _ _)=star (twist _ (windX _ f)); rw [win_s,map_star]
    change twist _ (cc (windX _ _))=star (twist _ (cc (windX _ _))); rw [win_s,cc_star,map_star] -- tune cc_star
  let H:= mateK n; have hh: Q H=H:= arum_self _ _ _ (Tset n) (touchP n ▸ tickB n) (tickR (castX s) (xtra s.charge) _ (spinZ ..) n)
  have ht:= congrArg Q (p.bra X); unfold Q at hh ht; unfold H at hh; rw [arum_act,arum_act,hh] at ht
  rw [he,cartPrice, show yellA s⁻¹ _=X from ?_,←hv,←hv]; exact ht
  exact Prod.ext (revB ..) (tuftT ..)
end YM.CF.Buffered
