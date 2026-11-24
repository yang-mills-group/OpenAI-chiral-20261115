import YM.SU5.SatinWard.Resolution.Motion
import Bay.C.Leather
import Bay.C.Sliding
import Anomaly.Framing.MarkFrame

--! charge-inclusive transport for origin mark sector and Birth programs. Extends ..Framing. Use Bay4's fully priced motion.

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


variable {V:Mark n}
lemma turnTagged(p:AtSupport false S V) : AtSupport false T (flyMark s V):=by
 let K:=s⁻¹; let f(x:Fields n):= V (flashA K x.1,flashA K x.2); refine ⟨Girt.pole_w f (Hive.teen s) (Scree.tour_c .. ) (Env.along p.env (((revM K).measurable.comp measurable_fst).prodMk ((revM K).measurable.comp measurable_snd))),?_,fun x=> Bay.C.fineTour s.charge _ (γS s) (tickR (castX s) (xtra s.charge) (spinU s.charge s.s) (spinZ ..) n) (prep_moves (castX s) _ _ _ (fun i=>Finset.mem_map_equiv)) (p.allV _)⟩ -- namespace
 intro x y u w; have hx(g v:Pane n)(p:Agrees T g v): Agrees S (flashA K g) (flashA K v):=by
    have he: S.map (boxA K).toEmbedding=T:=by unfold K; rw [sitU]
    exact flashD K _ _ _ (he.symm ▸ p)
 exact congrArg (Hive.teen s) (p.dep _ _ (hx _ _ u) (hx _ _ w))

lemma spectral_charge{o o':Site n}{b:ℕ}{v:ℝ}(p:WindowTag V o b v)(h: (boxA s).symm (node o)=node o'):
    WindowTag (flyMark s V) o' b v := by
  let A:= offsetMask b o
  have ht:actY s A=offsetMask b o':=by unfold A actY offsetMask; rw [←sitU,←paysT,map_singleton, sitU, show (boxA s).symm.toEmbedding (node o)=_ from h]
  refine ⟨ht ▸ (turnTagged s A p.ticket),?_,?_,fun x y u=> ?_⟩ -- same.first
  · intro G x; let a:= s⁻¹; let y:Orbit n:=Classical.arbitrary _; let F:=tollPull a y G; let U:Fields n:=(flashA a x.1, flashA a x.2)
    change Hive.teen s (V (flashA a (Lattice.gauge G x.1),flashA a (Lattice.gauge G x.2)))= _
    rw [show (flashA a (Lattice.gauge G x.1),flashA a (Lattice.gauge G x.2))=simultaneous F U from Prod.ext (revG a x.1 G) (revG a x.2 G), p.rolls]
    have hv: tollPull s y F=G:=by have ht:=kind_R a y G; change tollPull s⁻¹⁻¹ y F=G at ht; rwa [inv_inv] at ht
    let K:= Hive.teen s
    have he: K (Gaze F (V U))= Gaze (tollPull s y F) (K (V U)):= Hive.yoT s F _ (paritySale.checked (p.ticket.allV _).sector)
    rw [hv] at he; exact he
  · intro x
    exact (show ‖_‖=_ from Bay.C.normTour s.charge _ (γS s) (V (flashA s⁻¹ x.1,flashA s⁻¹ x.2))).trans_le (p.price _)
  exact congrArg (Hive.teen s) (p.pane _ _ (congrArg (flashA s⁻¹) u))


lemma charge_contact (K:Scree.Loom n){Y:Swell.phy n}(p:Contact K S V Y)(pv:∀ x y:Fields n,x.1=y.1→V x=V y) :
    Contact K T (flyMark s V) (cartPrice s Y):=by
  refine ⟨turnTagged s S p.pitch,fun x=> Bay.C.sceneTour s.charge _ (γS s) (prep_moves (castX s) _ _ _ (fun i=>Finset.mem_map_equiv)) (p.oscillator _),?_⟩
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

