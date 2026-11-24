import GaugeFieldConstruction.RankSail
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d e:ℕ}{k:Side}
abbrev Origin (s: Shape)(u:Cover): Cover:= s.s⁻¹.act (u-((2:ℕ) • s.t))
lemma rise_E (s:Shape)(u:Cover):s.motion (Origin s u)=u:=by simp [Shape.motion,Origin]
lemma rise_P (s:Shape)(u:Cover): Origin s (s.motion u)=u:=by simp [Origin,Shape.motion]
lemma motion_C (s:Shape)(u:Cover): s.motion u ∈ cartO (s.motion y) d ↔ u∈ cartO y d:=by
 rw [cart_spec,cart_spec]; have hp:s.motion u- s.motion y=s.s.act (u-y):=by unfold Shape.motion; simp -- tune
 have he(i:Axis):((s.motion u-s.motion y) (s.s.perm i)).natAbs= (u i - y i).natAbs:=by rw [hp,Signed.act_at]; cases hv:s.s.flip i <;> simp <;>omega
 exact ⟨fun h i=> (he i ▸ h (s.s.perm i)), fun h j=> by obtain ⟨i,rfl⟩:= s.s.perm.surjective j; change ((s.motion u-s.motion y) _).natAbs ≤ _; rw [he]; apply h⟩ -- tune eq rec
lemma flee_E(s:Shape) : Bijective s.flee:=by
 refine ⟨fun i j p=> node_cone.mp (Function.LeftInverse.injective (rise_P s) (a₁:=nodeC i) (a₂:=nodeC j) (by unfold nodeC; rw [Shape.mote,p,Shape.mote])),fun i=>?_⟩ -- tune
 let u:=s.s⁻¹.act (i - s.flee 0); refine ⟨u,?_⟩; calc
    s.flee u=s.flee (0+u):= congrArg _ (zero_add u).symm
    _=i:= by rw [Shape.flee_p]; unfold u; simp
lemma stay_d(s:Shape)(x:Cover): s.flee x∈ridge (s.motion y) d ↔ x∈ridge y d:=by rw [ridge_spec,ridge_spec, show nodeC (s.flee x)=s.motion (nodeC x) from (s.mote x).symm, motion_C]
def crestV (s:Shape) (d:ℕ)(y:Cover):ridge y d ≃ ridge (s.motion y) d:= Equiv.ofBijective (fun i:ridge y d=>(⟨s.flee i.val,(stay_d _ _).2 i.property⟩:ridge (s.motion y) d)) ⟨fun i j p=> Subtype.ext ((flee_E s).1 (congrArg Subtype.val p)),fun i=> by obtain ⟨j,h⟩:= (flee_E s).2 i.val; exact ⟨⟨j,(stay_d _ _).1 (h.symm ▸ i.property)⟩,Subtype.ext h⟩⟩ -- tune
lemma windling (s:Shape)(n:Side)(x:Cover) : Lifted.winding n (s.flee x)=s.payA (wrap n x)*Lifted.winding n x:= by
 let a:= natural (wrap n x); let t:=s.flee x; let Q:= Rush.periods n x; let R:=s.rent (wrap n x)
 have hp:= s.vibes (wrap n x); rw [Shape.mill] at hp
 suffices he:Rush.periods n t=R+s.s.act Q by unfold Lifted.winding; change fee (Rush.periods n t)=_; rw [he,Scroll.dues, dueShape]; rfl
 apply nsmul_right_injective (M:=Cover) n.property.ne'; change n.val • _=n.val • _; rw [smul_add, ←show (s.s).act (n.val • Q)= n.val • (s.s).act Q from map_nsmul ((s.s).actEquiv (R:=ℤ)) _ _]
 apply add_left_cancel (a:=natural (wrap n t)); rw [Rush.carrying]
 calc
    _ = s.flee (a+ n.val • Q) := congrArg _ (Rush.carrying n x).symm
    _ = _ := by rw [Shape.flee_p,←add_assoc]; change _=natural _+_+_; congr 1; exact hp.symm
variable (s:Shape) (p:Bool)
lemma preface (U:UNI SpinIdx)(p':Bool)(n: Side)(i:mort (s.motion x) d)(j:mort x d)(v: (crestV s d x) j.1=i.1): (siteU s p U n).val (hereF n j) (hereF n i)= s.payA (wrap n j.1.val)*(spinQ U (xtra p)).val j.2 i.2:=by
 let K:=xtra p; change (mealU s U K n).val (wrap n j.1.val,j.2) (wrap n i.1.val,i.2)=_; unfold mealU portX; dsimp only; rw [jump_apply]; have he: Tofu s n (wrap n j.1.val)=wrap n i.1.val:= Eq.trans (Shape.mill s j.1.val) (congrArg _ (congrArg Subtype.val v)); rw [if_pos he]; rfl
lemma surgeU (t:Bool)(U:UNI SpinIdx)(w:d<n.val)(k:Side):Ship (s.motion x) x d d t (siteU s p U n) (siteU s p U k):=by
 let g:= crestV s d x
 refine sailor t g.symm _ _ (fun i j H=>?_) (fun i z H=>?_) fun i j h=>?_
 · have he: s.mills n (wrap n j.1.val)=wrap n i.1.val:= Tenant.needle (Eq.trans (s.nodex _) (Tye.birth_l _ _ _ _ _ H)); rw [Equiv.symm_apply_eq]; symm; apply visits_wrap _ w; rw [show (g j.1).val=s.flee j.1.val from rfl, ← Shape.mill]; exact he
 · 
   have hp:= Tye.birth_l _ _ s U p H
   have he: s.mills k z.1.1=wrap k i.1.val:= Tenant.needle (Eq.trans (s.nodex _) hp); apply s.mills_b.1; rw [he, Shape.mill]; exact congrArg _ (congrArg Subtype.val (g.apply_symm_apply i.1))
 have hv:g j.1=i.1:= by rw [←h]; exact g.apply_symm_apply _
 rw [preface s p U t n i j hv,preface s p U t k i j hv]
 have hf(m:Side): Lifted.winding m i.1.val=s.payA (wrap m j.1.val)*Lifted.winding m j.1.val:=by rw [show i.1.val=s.flee j.1.val from congrArg Subtype.val hv|>.symm]; exact windling ..
 unfold billJ; rw [hf n,hf k]; let L:=s.payA (wrap n j.1.val); let Z:=s.payA (wrap k j.1.val); let D:=Lifted.winding n j.1.val*Lifted.winding k j.1.val; let Y:=(spinQ U (xtra p)).val j.2 i.2
 rw [mul_mul_mul_comm (s.payA (wrap n _)) _ (s.payA _)]; change D*(L*Y)= Z*Y*(L*Z*D); rw [show Z*Y*(L*Z*D)=Z*Z*(D*(L*Y)) by ring]; rw [show Z*Z=1 from s.reflex _,one_mul]
lemma ray_st (Z:ChartP n):steerZ (siteU s p (spinU p s.s) n) p (detX s.s) Z=steerZ (launchZ (Levier.ray p s)) p (detX s.s) Z:=by
 let c:= s.t; let F:= Lattice.lift (wrap n c); let z:= fee (Rush.periods n F-Rush.periods n c); symm; exact rayZ _ _ _ _ (utu n p (spinU p s.s) s.s F c (wrap_lift _)) ((pow_two _).trans (fee_one _)) (fee_real _) Z -- tune args
lemma box_origin (i:Cover) : boxA (Levier.ray (N:=n) p s) (wrap (More n) i)= wrap (More n) (s.motion i):=(stir_wrap _ _ _ _ (wrap_lift (wrap n s.t))).trans (s.anno i) -- tune
lemma sector_o(x:Cover):Layout.Fren.sh (Levier.ray (N:=n) p s) (wrap (More n) (s.motion x))=wrap (More n) x:=by unfold Layout.Fren.sh; rw [←box_origin s p,Equiv.symm_apply_apply]
lemma turn_CK (V:Pane n)(l:Lattice.Step)(j:Cover): l.read (onC n (flashA (Levier.ray p s) V)) j= polarT p ((l.rotate s.s).read (onC n V) (s.motion j)):=by
 have hf{V:Pane n}(l:Lattice.Step)(j:Cover): l.read (onC n V) j=l.read V (wrap (More n) j):=by have he:= travel_at 0 V j [l]; simp [travel] at he; exact he
 rw [hf,hf]; change l.read (stir _ _ _) _=_; rw [show stir _ _ _= _ from stir_e s p V]; rw [veil_x,Shape.anno]; rfl
lemma agree_CK (V:Pane n)(W:Pane k)(h:Agrees (cartO (s.motion x) d) (onC n V) (onC k W)):Agrees (cartO x d) (onC n (flashA (Levier.ray p s) V)) (onC k (flashA (Levier.ray p s) W)):=by
 rintro ⟨z,i⟩ u f; change (posDir i).read (onC n (flashA (Levier.ray p s) V)) z=(posDir i).read (onC k (flashA (Levier.ray p s) W)) z; rw [turn_CK,turn_CK]; apply congrArg
 let l:=(posDir i).rotate s.s; have he: s.motion (z+step i)=s.motion z+l.vec:=by rw [Shape.motion_v]; change _=s.motion z+ ((posDir i).rotate s.s).vec; rw [Step.vec_rotate,Step.vec_pos]; -- tune
 have hx:s.motion z∈ cartO (s.motion x) d:= (motion_C s z).2 u
 have hv: s.motion z+l.vec∈ cartO (s.motion x) d:= he ▸ (motion_C s _).2 f -- tune
 change l.read _ _=l.read _ _; rcases hh:l with ⟨i,b⟩; rw [hh] at hv; cases b
 · exact h (_,i) hx hv
 have hp: s.motion z-step i ∈ cartO (s.motion x) d:=by simpa only [show (⟨i,true⟩ : Lattice.Step)= negDir i from rfl, Lattice.Step.vec_neg,sub_eq_add_neg] using hv
 exact congrArg Inv.inv (h (s.motion z-step i,i) hp (by change _+step i ∈ _; rw [sub_add_cancel]; exact hx))
variable {F:Psu (Shape.motion s x) d}{G:Psu x d}
lemma aboard_k (w:d<n.val)(k:Side)(h:∀ i, LocalOn (cartO (s.motion x) d) (F i))(v:∀ i, LocalOn (cartO x d) (G i)) (P:pR n G=Barber (Levier.ray p s) (pR n F)) : pR k G=Barber (Levier.ray p s) (pR k F):=by
 let L:= Levier.ray (N:=k) p s; let V:= Levier.ray (N:=n) p s; let U:=spinU p s.s
 have he (W:Pane k):αLines (pR k G) (flashA L W)=αLines (Barber L (pR k F)) (flashA L W):=by
    let Q:Pane n:= snake (s.motion x) (onC k W); have hx:Agrees (cartO (s.motion x) d) (onC n Q) (onC k W):= fun i u t=> (cart_L w (onC k W) i u t).symm
    let T:= detX s.s; have hp:Dockers (s.motion x) x d d T Q (flashA V Q) W (flashA L W) (siteU s p U n) (siteU s p U k):=⟨surgeU s p T U w k,hx, agree_CK s p Q W hx⟩
    rw [boothK]; change _=steerZ (launchZ L) p T _; rw [←ray_st]; refine hp.passK w w h v ?_; rw [P,boothK,ray_st]; try rfl
 funext i Q; rw [←goS L Q]; exact congrFun (he _) _ -- tune
end ArtCart
end MastTin
end YM.CF.XGarden
end
