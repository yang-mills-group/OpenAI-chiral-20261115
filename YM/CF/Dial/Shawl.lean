import YM.CF.Dial.Spur
import YM.CF.Sedge.Pause
import YM.CF.Lattice.Reference
/-! Orient full-line output plus and sea with synchronized high slots. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
-- plus
abbrev tickA (N:Side):Op (Single N):=portW (helix N).symm (cutM (upperP N))
def spotC (v:Site N→ Vect):= portW (helix N).symm (Cfield v)
def postC (X:Stun N): Op (Single N):= spotC (hook X ∘ node)
def mateK(N:Side):Wave (Single N):= cartsL (helix N).symm (linearB N)
lemma tickB(N:Side):Sea (tickA N) (mateK N):= by
  apply carts_sea _ (cutM_idp _); constructor
  · rw [linearB, map_smul,cutLine,cut_basis,if_pos (mem_singleton_self ..)]
  rw [linearB,norm_smul,unit_phase]; simp [basisKet]
lemma starC (v:Site N→Vect)(h:∀ i, ‖v i‖=1): (spotC v)ᵀ= -(spotC v):=by
  ext i j; exact Matrix.ext_iff.mpr (C_skew _ h) ((helix N) i) ((helix N) j)
lemma constB (v:Site N→Vect)(h:∀ i, ‖v i‖=1):filled (tickA N) (spotC v)=mateK N:=by
  unfold spotC tickA; rw [relabelF _ (C_skew v h) (cutM_idp _)]; unfold mateK; congr 1; rw [filled,cutLine,cut_oneAct]; unfold linearB; rw [←pf_free v h]; rfl
abbrev boots(Q:Op (Single P)):=portW (switchG G).symm Q
lemma lobe_t:lobe G true=foot G (tickA P):=by
  unfold lobe; rw [tickA,plane_diag, pilesV];
  ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩
  change _=(jump (Equiv.refl (Site P)) (fun _=>cutM plusHalf⊗ₖ (1:Op Slot))) (isle G (x,r),b,i) (isle G (y,t),c,j); rw [show cutM plusHalf= angle true from raising.trans Adef.symm];
  simp only [Matrix.kroneckerMap_apply, jump_apply,Equiv.refl_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq,sA,slashA,Fir.s_app, ite_mul]; rw [ite_and]; simp
lemma tick_hold(v:Op (Single P)):foot G v=boots G v:=rfl
lemma square_t(u:Bool)(X:Sew N P): ∃ v:Site P→ Vect, (∀ i, ‖v i‖=1)∧ squareD G u (post X)=foot G (spotC v):=by
  let v:Site P→Vect:=fun i=>if u then hook X.2.1 (node i) else hook X.2.2 (node ((isle G).symm i).1)
  refine ⟨v,fun i=>?_,?_⟩
  · cases u<;> exact hookN ..
  ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩
  change (jump (Equiv.refl _) _) ((x,r),b,i) ((y,t),c,j)= (Cfield v) (isle G (x,r),b,i) (isle G (y,t),c,j);
  unfold Cfield; rw [jump_apply,jump_apply]; simp only [v,Equiv.apply_eq_iff_eq,Equiv.refl_apply,Equiv.symm_apply_apply]; congr 1; cases u <;> rfl
lemma square_true(X:Sew N P): squareD G true (post X)= boots G (postC X.2.1):=by
  ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩
  change (jump (Equiv.refl _) _) ((x,r),b,i) ((y,t),c,j)=(Cfield _) (isle G (x,r),b,i) (isle G (y,t),c,j)
  rw [Cfield,jump_apply,jump_apply]; simp only [Equiv.refl_apply,Equiv.apply_eq_iff_eq]; rfl
lemma silentC(u:Bool)(X:Sew N P):Commute (cutM (lows (patchQ G))) (squareD G u (post X)):=by
  unfold Commute SemiconjBy; ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩
  rw [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]; simp only [←Peaks.land];
  change ((if r=0 then 1 else (0:ℂ)))*(jump (Equiv.refl _) _) ((x,r),b,i) ((y,t),c,j)=(jump (Equiv.refl _) _) ((x,r),b,i) ((y,t),c,j)*(if t=0 then 1 else 0)
  rw [jump_apply]; by_cases h:r=0 <;> by_cases e:t=0 <;> simp only [jump_apply,Equiv.refl_apply,ite_true,ite_false,h,e, Prod.mk.injEq,and_self,and_true,zero_mul,one_mul,mul_one,mul_zero] <;> grind
lemma summit_p(X:Sew N P):summit (patchQ G) (squareD G false (post X))=postC X.2.2:=by
  ext ⟨⟨x,b⟩,i⟩ ⟨⟨y,c⟩,j⟩; change (jump (Equiv.refl (Hand G)) _) ((x,0),b,i) ((y,0),c,j)=(Cfield _) (x,b,i) (y,c,j);
  unfold Cfield; simp only [jump_apply,Equiv.refl_apply, Prod.mk.injEq,and_self,and_true]; rfl
lemma whale_plus :lobe G true=addS (patchQ G) (reefS G true) (tickA N):=by
  unfold addS; rw [← goldLobe, mul_sub,mul_one]
  have he:lobe G true*hood G=desk (patchQ G) (tickA N):=by
    rw [shoulder,lobe,op_kron_mul,pilesP,one_mul,show (fun p:Momentum=>sA true G.count*peb G.count)=(fun _=> spike G.count (cutM plusHalf)) by
      funext i; rw [sA,slashA,peb, mul_spike,mul_one, raising]; exact congrArg _ Adef, low_pose, edgeDesk];
    rw [show tickA N=plates N (fun _=>cutM plusHalf)⊗ₖ (1:Op Slot) by
      ext ⟨⟨x,b⟩,i⟩ ⟨⟨y,c⟩,j⟩; rw [tickA,plane_diag,pilesV]; by_cases h:x=y<;>simp [h,portW,helix,Lat.spin,jump_apply],endorsement]
  rw [he,sub_add_cancel]
def oceanA:Wave (Iota G):= cartsL (switchG G).symm (mateK P)
lemma seaA : Sea (lobe G true) (oceanA G):=by
  rw [lobe_t,tick_hold]; exact carts_sea (switchG G).symm (carts_p _ (cutM_idp _)) (tickB P)
lemma constA (u:Bool)(x:Sew N P):filled (lobe G true) (squareD G u (post x))=oceanA G:=by
  obtain ⟨v,h,p⟩:=square_t G u x; rw [p,lobe_t,tick_hold,tick_hold]; unfold boots; rw [relabelF _ (starC v h) (carts_p _ (cutM_idp _)),constB v h]; rfl
lemma betaH(x:Sew N P): oceanA G=pf (squareD G false (post x)) (reefS G true) • hoist (patchQ G) (reefS G true) (mateK N):=by
  have ht: filled (tickA N) (postC x.2.2)=mateK N:= constB _ fun i=> hookN ..
  conv_lhs=> rw [←constA G false x, whale_plus,crane _ _ (reefS_deck ..) _ (skew_square ..) (silentC ..) (carts_p _ (cutM_idp _)),summit_p,ht]
def sect (x:Sew N P):ℂ:=pf (squareD G false (post x)) (reefS G true)
def sect0:ℂ:= sect G (1,vacuumW P,vacuumW N)
lemma sector_pin(x:Sew N P):sect G x=sect0 G:=by
  let T:= hoist (patchQ G) (reefS G true) (mateK N); have he:T≠0:= norm_pos_iff.mp (show 0<‖T‖ by rw [hoistN _ _ (reefS_deck ..), (tickB N).2]; norm_num)
  exact smul_left_injective ℂ he ((betaH G x).symm.trans (betaH G _))
lemma sec_phase:oceanA G=sect0 G • hoist (patchQ G) (reefS G true) (mateK N):= betaH G _
lemma sectorU : ‖sect0 G‖=1:=by
  have he:= (seaA G).2; rw [sec_phase,norm_smul,hoistN _ _ (reefS_deck ..), (tickB N).2,mul_one] at he; exact he
lemma sec_salary {B:Op (Single N)} (p:IsStarProjection B)(x:Sew N P): filled (addS (patchQ G) (reefS G true) B) (squareD G false (post x))= sect0 G • hoist (patchQ G) (reefS G true) (filled B (postC x.2.2)):=by rw [crane _ _ (reefS_deck ..) _ (skew_square ..) (silentC ..) p,summit_p,←sector_pin G x]; rfl
end YM.CF.Dial
