import Anomaly.Cover.Saloon
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke
open Swell Sonar StageQ Ione Vow Tapestry.StageW
namespace Spine
universe u
local notation "o0"=> nodeC (0:Cover)
variable (P:Spine)
local notation "kZ"=> P.calibration
variable {R S: Finset Cover} {Q:ℕ→ℕ}{B:Side}{V:Sweep B}
variable (s:Signed)
private abbrev sweepHome:= o0-s.act o0
private abbrev waypoint (x:Cover):= affine s (sweepHome s) x
abbrev prizeLinks (f:LinksC):LinksC:= (polarT (detX s)) ∘ Lattice.pull s (sweepHome s) f
lemma testHere (b:ℕ)(x:Cover)(p:x∈ liner {o0} b) : waypoint s x∈ liner {o0} b:=by
 obtain ⟨i,h,w⟩:=mem_biUnion.mp p; rw [mem_singleton] at h; obtain ⟨q,v,rfl⟩:=mem_image.mp w
 rw [h]; refine mem_biUnion.mpr ⟨_,mem_singleton_self _, mem_image.mpr ⟨s.act q,?_,?_⟩⟩
 · rw [← box_covariant b s]; exact mem_image_of_mem _ v
 unfold waypoint affine; rw [Signed.act_add]; unfold sweepHome; change _ = s.act q+s.act o0+(o0-s.act o0); abel
lemma tint_agree (b:ℕ)(f g:LinksC)(h:Agrees (liner {o0} b) f g): Agrees (liner {o0} b) (prizeLinks s f) (prizeLinks s g):=by
 let B:= liner {o0} b; rintro ⟨i,j⟩ t p; let V:= (posDir j).rotate s; let x:= waypoint s i
 have hx: x ∈ B:= testHere s b i t -- use explicit
 have he: x+V.vec ∈ B:=by
   rw [show x+V.vec=waypoint s (i+step j) from ?_]; exact testHere s b _ p
   unfold waypoint x; unfold waypoint; rw [Step.vec_rotate (posDir j),Step.vec_pos]; unfold affine; rw [Signed.act_add]; abel
 change (polarT _) (V.read f x)=_; apply congrArg (polarT (detX s)); change V.read f x=V.read g x; cases r:V with | mk a t=>
 rw [r] at he; cases t
 · exact h (x,a) hx he
 have hy:x-step a∈B:= by simpa only [show (⟨a,true⟩ : Lattice.Step)=negDir a from rfl,Lattice.Step.vec_neg,sub_eq_add_neg] using he
 exact congrArg Inv.inv (h (x-step a,a) hy (by change x-step a+step a∈ B; rw [sub_add_cancel]; exact hx))
lemma sweepHere (N:Side)(x:Pane N) : Lifted.onC _ (flashA (gridTulip s 0) x) =prizeLinks s (Lifted.onC _ x):=by
 let t:=gridTulip s (0:Site N); let p:= More N; let T:= wrap p; let b:= (assembly N).embed t.b
 have hx:t.s=s:=tieS ..; have hb:T o0=node 0:=by rw [←Lifted.node_of,map_zero]
 have hp:b=T (sweepHome s):=by
    have he: boxA t (node (0:Site N))=node (0:Site N):=by rw [←Ione.Clock.nodeA, tieA]
    rw [sitA,hx,affine,←hb] at he; unfold sweepHome; rw [map_sub,←wrap_signed]; exact eq_sub_of_add_eq' he -- tune
 funext e
 obtain ⟨i,j⟩:=e; let v:= (posDir j).rotate s; rw [Lifted.onC_spec, revoke,hx,tieC]
 change _=polarT _ (v.read (Lifted.onC N x) (waypoint s i)); apply congrArg (polarT (detX s))
 have ht:T (waypoint s i)=affine s b (T i):=by unfold waypoint affine; rw [map_add,wrap_signed,hp]
 change v.read x _= v.read _ _; have he:= Lifted.onC N x; have hm:= travel_at 0 x (waypoint s i) [v]; rw [ht] at hm; simp only [add_zero,Lattice.travel,mul_one] at hm; exact hm.symm
-- proof actual arena.Mean identity.A gauge projection at ONE Hosp.Local.Graft then all, not arbitrary Spin ratios presumed. Moted relationship retained on Family.
def Spherical (s:Signed) {n:Side}(f g:Mark n):Prop:= ∀ x:Fields n, g x=f (flashA (gridTulip s 0) x.1,flashA (gridTulip s 0) x.2)
private lemma universalPose {r:Side}{K:Calibration}{f g:Family K}(b:ℕ) (h:Licor (liner {nodeC 0} b) K f)(u:Licor (liner {nodeC 0} b) K g)(p:Roomy (liner {nodeC 0} b) (K.c r))(V:Spherical s (f r) (g r)) :∀ n,Spherical s (f n) (g n):=by
 obtain ⟨F,H,rfl⟩:=h; obtain ⟨G,A,rfl⟩:=u
 let N:= K.c r; let S:= liner {o0} b; have he(x:LinksC)(i:N = N): G x=F (prizeLinks s x):=by -- remove i
    let t:= graft S N x; have ht(V):= tacked S N (Roomy.seats p) V
    have hu (F:LinksC→ℂ) (h:Coeff true S (F∘Prod.fst)) (x y:LinksC)(p:Agrees S x y): F x=F y:= h.locus (x,1) (y,1) p (fun _ _ _=>rfl)
    have hp:= V ((t,1):Fields (K.c r)); unfold scalar at hp; dsimp only [Function.comp_apply] at hp
    rw [sweepHere, hu G A _ _ (ht x), hu F H _ _ (tint_agree s _ _ _ (ht x))] at hp
    exact smul_left_injective ℂ one_ne_zero hp -- tune
 intro n x; unfold scalar; simp only [Function.comp_apply,sweepHere,he _ rfl] -- tune binder
section
variable {d m:ℕ}{B t:ℕ→ℕ}{A:ℕ→Proscenium→Tapestry.Swatch (P.roomFox d m)}{G:Proscenium→Tapestry.Swatch (P.roomFox d m)}
variable {X:(j:ℕ)→ SOp (age P.run (P.nomadic (B j)) d)}{J:(j:ℕ)→ Axis→ SOp (age P.run (P.nomadic (B j)) d)} (u: OnTape P d m B X J t A G)
local notation "𝕊"=>roomFox P d m
include u
lemma issuedProbe (j:ℕ)(p:Roomy 𝕊 (age P.run (P.nomadic (B (t j))) d)) :∀ r,Spherical s (render 𝕊 kZ (A j .tick) r) (render 𝕊 kZ (A j (.gauge s)) r):=by
 let h:= u.localAt j .tick; let f:=u.localAt j (.gauge s); let i:=P.nomadic (B (t j)); let N:=momentm P.run i d; let U:= P.calibration.c N; let n:= side P.run i d; have hp:U=n:=terrain ..
 apply universalPose (r:=N) s _ (h.2 (Or.inl rfl)) (f.2 (Or.inr ⟨s,rfl⟩)) (by change Roomy 𝕊 U; rw [hp]; exact p); let H:= A j; refine sameFiber U n hp (appear 𝕊 kZ N (H .tick)) (appear 𝕊 kZ N (H (.gauge s))) (?_); change Spherical s (present P.run P.large d _ _ _) (present P.run P.large d _ _ _); unfold i H; rw [u.issued, u.issued]; exact fun x=>rfl
where sameFiber (n m:Side)(p:n=m)(x y:Mark n)(h:Spherical s (arrange _ _ p x) (arrange _ _ p y)):Spherical s x y:=by subst m; exact h
lemma poseVote (p:∀ j,Roomy 𝕊 (age P.run (P.nomadic (B (t j))) d)):∀ n,Spherical s ((render 𝕊 kZ (G .tick)) n) ((render 𝕊 kZ (G (.gauge s))) n):=by
 intro n x; refine tendsto_nhds_unique_of_eventuallyEq (carriesC (u.deckV (.gauge s)).2.1 n x) (carriesC (u.deckV .tick).2.1 n _) (Eventually.of_forall fun i=>issuedProbe P s u i (p i) n x)
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
