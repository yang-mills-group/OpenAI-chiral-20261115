import YM.SU5.Reconstruction.AllGrades.Caption
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
/-! # Whole regained: real ROOT/Character connectivity geometry from those doubling receipts. -/
local notation "sj"=> look a
local notation "X"=> T.aviator (look a)
variable (e: (T.aviator (look a))=⊤) (u:∀ (i:CF.Buffered.Afterglow.Tower.Trans a) (v:Γ)(t:ℝ≥0), ((T.crew i).play v).comp (K.E t)= (K.E t).comp ((T.crew i).play v)) (d:Dense (Γ:Set ℝ))
include u e d
-- already learned extension through entire H, not just through $T.aviator$, so supply whole at actual Replica H
noncomputable def launchHouse : OS.Semigroup H a where
 E:= K.E
 U x:= T.flight d (look a) (fun i => x.val i.val)
 eZero:=K.eZero
 time:=K.time
 shrinks:=K.shrinks
 sym:=K.sym
 uZero:=by
    ext1 v; rw [show (fun i:CF.Buffered.Afterglow.Tower.Trans a=> (0:Cross a).val i.val)=0 from rfl, T.start]; exact T.grounded (look a) (e.symm ▸ Submodule.mem_top)
 space p q:= by
    have h:(fun i:CF.Buffered.Afterglow.Tower.Trans a => (p+q).val (i:Axis))=(fun i:CF.Buffered.Afterglow.Tower.Trans a=> p.val (i:Axis)) + (fun i:CF.Buffered.Afterglow.Tower.Trans a=> q.val (i:Axis)):=rfl
    rw [h,T.travel]
 independent t x:= (Alliance.fluid T d (look a) _ (fun i _ v=> u i v t) _).symm
 continuousE:=K.continuousE
 unitary p v:=by
    let w:T.aviator (look a):= ⟨v, e.symm ▸ Submodule.mem_top⟩
    exact T.aviation_unit _ _ _ (show T.Realm (look a) from w)
 continuousU x:= Alliance.moves T d (look a) _ (fun i _=> show Continuous (fun s:Cross a=> s.val i.val) by fun_prop) _ continuous_const
local notation "G"=> launchHouse K T e u d
local notation "Dr"=> LinearIsometryEquiv.refl ℂ H.space
lemma tracks_h(i:CF.Buffered.Afterglow.Tower.Trans a)(v:Γ):(G).U ((v:ℝ) • cross a i.val i.property)= (T.crew i).play v:= by
    let x: Cross a := (v:ℝ) • cross a i.val i.property; let p:CF.Buffered.Afterglow.Tower.Trans a →Γ:= Function.update 0 i v
    ext1 t; have hx:(fun i:CF.Buffered.Afterglow.Tower.Trans a=> x.val i.val)=(fun j=>(p j:ℝ)):= by
       funext j; by_cases h:j=i
       · subst j; simp [x,p,cross]
       have hv:j.val≠ i.val:=fun w=>h (Subtype.ext w); simp [p,x,h,hv,cross]
    change T.flight d (look a) (fun i=>x.val i.val) _=_
    rw [hx,T.smooth_notch,ContinuousLinearMap.comp_apply,T.grounded (look a) (e.symm ▸ Submodule.mem_top), spotlight T _ (look_one a) (look_all _ i)] -- spot p def
lemma caption_real : Captions K T (G) Dr:= ⟨fun _ _=> rfl,fun i v x=> DFunLike.congr_fun (tracks_h K T e u d i v).symm x⟩
end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.caption_real
