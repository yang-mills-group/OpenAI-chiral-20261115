import YM.SU5.Reconstruction.Oblique.RotorField
/-! # physical registered generator action on every rung. Pin lift & gauge geometry. The cover mark convention is the one paid in Selected -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
namespace Ramp
open Reed (Fine) -- local study
variable (P:Ramp)(N : Side)
local notation "T" => P.plan
abbrev coast (P:Ramp) (U:LinksC):LinksC:=pull P.s (2 • P.plan.t) U
def survey(S: Finset Cover) := S.image (P.plan.motion)
lemma course_stamp (U : Pane N): onC N (P.turnLink N U)=P.coast (onC N U):= by
  funext ⟨x,t⟩; rw [onC_spec]; change ((posDir t).rotate (T).s).read U ((T).anon N (wrap (More N) x)) = ((posDir t).rotate (T).s).read _ ((T).motion x); rw [Shape.anno]
  let d:=((posDir t).rotate (T).s); let X:=(T).motion x; have he:= travel_at 0 U X [d]; simpa [X,d,onC,travel] using he.symm
lemma coast_cont : Continuous P.coast := by apply continuous_pi; intro j; unfold coast Lattice.pull Step.read; split <;> fun_prop
variable {S:Finset Cover}
lemma moved_agree {X Y : LinksC} (p : Agrees (S.image (P.plan.motion)) X Y) :
    Agrees S (P.coast X) (P.coast Y) := by
  rintro ⟨x,j⟩ hx ht
  let d:=(posDir j).rotate ((T).s)
  have hh: (T).motion (x+step j)=(T).motion x+d.vec := by rw [Shape.motion_v]; rw [show (T).s.act (step j : Cover)=_ from (Step.vec_rotate (R:=ℤ) (posDir j) ((T).s)).symm]
  let S':=S.image ((T).motion)
  have ha : (T).motion x∈ S':= mem_image_of_mem ((T).motion) hx
  have he : (T).motion x+d.vec∈ S':= hh ▸ mem_image_of_mem ((T).motion) ht
  change d.read X _=d.read Y _; cases h:d with|mk a b=>
  rw [h] at he; cases b
  · exact p ((T).motion x,a) ha he
  have hv : (T).motion x-step a ∈ S' := by simpa only [show (⟨a,true⟩ : Lattice.Step)=negDir a from rfl, Lattice.Step.vec_neg,sub_eq_add_neg] using he
  exact congrArg Inv.inv (p ((T).motion x-step a,a) hv (by change _+step a ∈ S'; rw [sub_add_cancel]; exact ha))
lemma winding_move (x : Cover) : Lifted.winding N ((T).flee x)=(T).payA (wrap N x)*Lifted.winding N x := by
  let a:= natural (wrap N x); let t:=(T).flee x; let Q:= periods N x; let R:=(T).rent (wrap N x)
  have hp:= (T).vibes (wrap N x); rw [Shape.mill] at hp
  suffices he : periods N t=R+((T).s).act Q by unfold Lifted.winding; change fee (periods N t)=_; rw [he,dues, dueShape]; rfl
  apply nsmul_right_injective (M:=Cover) N.property.ne'; change N.val • _=N.val • _; rw [smul_add, ←show ((T).s).act (N.val • Q)= N.val • ((T).s).act Q from map_nsmul (((T).s).actEquiv (R:=ℤ)) _ _]
  apply add_left_cancel (a:=natural (wrap N t)); rw [Rush.carrying]
  calc
    _ = (T).flee (a+ N.val • Q) := congrArg ((T).flee) (Rush.carrying N x).symm
    _ = _ := by rw [Shape.flee_p,←add_assoc]; change _=natural _+_+_; congr 1; exact hp.symm
lemma winding_frame (x : Cover) : Lifted.winding N x * (T).payA (wrap N ((T).flee x))=Lifted.winding N ((T).flee x) := by
  nth_rw 1 [← Ramp.fend P x, winding_move P N ((T).flee x)]; rw [mul_right_comm,Shape.reflex, one_mul]

lemma acted_basisC (x : Cover) (a : SpinIdx) (b : SU.Slot) :
    acts (P.vehicle N).val (basisC N x a b) = ∑ j, P.imageP j a • basisC N ((T).flee x) j b := by
  apply PiLp.ext; rintro ⟨⟨y,j⟩,l⟩; simp_rw [basisC,map_smul,WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, basis_act,basis_apply]; let v:= wrap N ((T).flee x)
  have hp : Tofu T N v=wrap N x := by change (T).mills N v= _; rw [show v= _ from (Shape.mill T x).symm, P.fence _]
  have hv : (P.vehicle N).val ((y,j),l) (index N x a b) = if y=v then (T).payA y*(P.imageP j a * (1 : Op SU.Slot) l b) else 0 := by
    change jump (Tofu T N) (fun i'=>(milU T (P.reel) inert i').val) (y,j,l) ((wrap N x),a,b)= _; by_cases h:y=v <;> simp only [jump_apply]; rw [if_pos h, if_pos (show Tofu T N y=_ from h.symm ▸ hp)]; rfl
    rw [if_neg h, if_neg (fun e=> h ((Tofu T N).injective (e.trans hp.symm)))]
  change Lifted.winding N x • (P.vehicle N).val ((y,j),l) (Lifted.index N x a b) = _
  rw [hv]
  by_cases t:y=v; swap; · rw [if_neg t]; unfold v at t; simp [t,Lifted.index]
  rw [if_pos t]; by_cases p:l=b; swap; · simp [Lifted.index,p]
  subst y l; simp [Lifted.index,v,winding_frame, ← mul_assoc,mul_comm (a:=Lifted.winding N ((T).flee x))]
lemma flips_basisC (x : Cover) (a : SpinIdx) (b : SU.Slot) :
    Fock.theta (P.vehicle N) (create (basisC N x a b)) = (-Complex.I) • Fock.remove (∑ j, P.imageP j a • basisC N ((T).flee x) j b) ∧
    Fock.theta (P.vehicle N) (Fock.remove (basisC N x a b)) = Complex.I • create (∑ j, P.imageP j a • basisC N ((T).flee x) j b) := by rw [theta_upV,theta_downV, acted_basisC]; trivial

variable (J: Calibration) {g f : Family J}
noncomputable def cuspF (P:Ramp)(J:Calibration)(x:Family J):Family J:=fun m=>P.bill (x m)
lemma over_zero : P.cuspF J 0=0:= funext fun _=>funext fun _=>theta_zero ..
lemma over_id : P.cuspF J 1=1:= funext fun _=>funext fun _=>theta_one ..
lemma over_add : P.cuspF J (f+g)= P.cuspF J f+ P.cuspF J g:=funext fun _=>funext fun _=>theta_add ..
lemma over_z(c:ℂ): P.cuspF J (c • f)=star c • P.cuspF J f:=funext fun _=>funext fun _=>theta_smul ..
lemma over_sub : P.cuspF J (f-g)=P.cuspF J f-P.cuspF J g:=funext fun _=>funext fun _=>theta_sub ..
lemma over_times : P.cuspF J (f*g)= P.cuspF J f*P.cuspF J g:=funext fun _=>funext fun _=>theta_mul ..
variable {wide b:Bool}
lemma toll_plus (f : PairsC→ℂ)(p:Coeff wide S f):InTest J wide (P.survey S) false (P.cuspF J (scalar J f)):= by
 let u:= P.coast; let g(x:PairsC):=star (f (u x.1,u x.2)); have ht:P.cuspF J (scalar J f)=scalar J g:=by
      funext m x; unfold cuspF Buffered.scalar bill; rw [theta_smul,theta_one]; apply congrArg (fun u:ℂ=> u • (1:FC (Single _))); unfold g u; simp only [both,Prod.map_fst,Prod.map_snd,P.course_stamp]
 rw [ht]; refine .seed ⟨fun v=> ?_,Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map u u) p.env (P.coast_cont.prodMap P.coast_cont).measurable),fun x y c d=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (u x)),(h.comp P.coast_cont).star,?_⟩; rw [show g=fun x=>star (f (u x.1,u x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (u x.1,u x.2) (u y.1,u y.2) (P.moved_agree c) (P.moved_agree d))
lemma over_create(x:Cover)(i: SpinIdx)(b:SU.Slot):
    P.cuspF J (creation J x i b) = -Complex.I • ∑ j, star (P.imageP j i) • removal J ((T).flee x) j b:= by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold cuspF bill creation removal
 rw [(P.flips_basisC (J.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
lemma over_remove(x:Cover)(i:SpinIdx)(b:SU.Slot):
    P.cuspF J (removal J x i b)=Complex.I • ∑ j, P.imageP j i • creation J ((T).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold cuspF bill creation removal
 rw [(P.flips_basisC (J.c m) x i b).2]; simp only [map_sum,map_smul]
lemma turns_on: twist P.reel (cutM plusHalf)=cutM plusHalfᶜ:=by rw [dim_cut,raising,Fir.Adef.symm]; exact angleX P.jet true
lemma faces (x: InTest J wide S b f):InTest J wide (P.survey S) b (P.cuspF J f):=by
 induction x with
 | @creator t i b h v=>
    rw [over_create]; refine .smul _ (InTest.sum _ _ (fun j _=>?_)); by_cases e:j∉plusHalf
    · refine .smul _ (.remover b e (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
    rw [show P.imageP j i=0 from Fine.entry P.turns_on h (by simpa using not_not.mp e),star_zero,zero_smul]; exact .zero
 | @remover t i b h v=>
    rw [over_remove]; refine .smul _ (InTest.sum _ _ (fun j _=>?_)); by_cases e:j∈plusHalf
    · refine .smul _ (.creator b e (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
    have ht: twist P.reel (cutM plusHalfᶜ)=cutM plusHalf:=by rw [dim_cut,map_sub,map_one,P.turns_on,dim_cut]; abel
    rw [show P.imageP j i=0 from Fine.entry ht (by simpa only [mem_compl] using h) e, zero_smul]; exact .zero
 | seed p=> exact P.toll_plus J _ p
 | zero=> rw [Ramp.over_zero]; exact .zero
 | one=>rw [P.over_id]; exact .one
 | add _ _ i j=> rw [Ramp.over_add]; exact .add i j
 | mul _ _ i j=> rw [Ramp.over_times]; exact .mul i j
 | smul c _ ih=> rw [P.over_z]; exact .smul _ ih
lemma twice_over (x:InTest J wide S b f):P.cuspF J (P.cuspF J f)=f:=funext fun m=> P.term_twice (x.support m)
lemma keeps_color {f:Family J}(p:TestFamily J true f)(v:CovCover J f):CovCover J (P.cuspF J f):=fun m=> P.term_cov (p.paid.choose_spec.support m) (v m)
end Ramp
end YM.CF.Buffered.Afterglow.Tower.Tilted
