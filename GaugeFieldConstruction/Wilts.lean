import GaugeFieldConstruction.Bellcord
/-!
# Sector API. Linearized curvature. Use full polynomial potentials, exact criterion and radial section.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 35000
noncomputable section
namespace YM.FlightFlux
open Lattice Function Finset
open scoped Topology
variable {I:Type*} [DecidableEq I][Fintype I]
variable {E:Type*} [AddCommGroup E][Module ℝ E]
-- Flux model. use full closed jet axial property. 
local notation "CardP" => I → I→ E
local notation "Y" => Shape I
local notation "b₁" i:max=> Pi.single i (1:ℤ)
def fluxV (E I:Type*)[AddCommGroup E][Module ℝ E] : Submodule ℝ (I→I→E) where
 carrier:= {x|∀ i j,x i j+x j i=0} -- 2 torsion killed
 add_mem' p q i j:=by simp only [Pi.add_apply]; rw [add_add_add_comm,p i j,q i j,add_zero]
 smul_mem' a f p i j:= by simp only [Pi.smul_apply,← smul_add,p i j,smul_zero]
 zero_mem':= fun i j=>zero_add _
def fluxT (E I:Type*)[AddCommGroup E][Module ℝ E] :Submodule ℝ (I→I→I→E) where
 carrier := {f| (∀ i,f i∈fluxV E I) ∧ (∀ i j k,f i j k+f j k i+f k i j=0) }
 add_mem' := by
    intro i j p q; refine ⟨fun l=> (fluxV E I).add_mem (p.1 l) (q.1 l),fun a b c=>?_⟩; simp only [Pi.add_apply]; rw [add_add_add_comm (i a b c) (j a b c),add_add_add_comm (i a b c+_),p.2,q.2,add_zero] -- second add pattern tune
 smul_mem' := by intro a f p; refine ⟨fun l=> (fluxV E I).smul_mem _ (p.1 l),fun i j k=>?_⟩; simp only [Pi.smul_apply,← smul_add,p.2,smul_zero]
 zero_mem' := ⟨ fun i=>(fluxV E I).zero_mem,fun i j k=>by simp⟩
namespace Fluxim
-- note core orientation even charge inversion.
lemma paper_shift1 (f:I→E)(i:I) (x:Y): slope f (x+b₁ i) = slope f x+ f i :=by have he: slope f (x+b₁ i)-slope f x=f i:=congrFun (φ_step f i) x; rw [←he]; abel
variable (F: Wheel I E)
lemma flux_neg (u:fluxV E I) (i j:I) : u.val i j = -u.val j i:= eq_neg_of_add_eq_zero_left (u.property i j) -- simp causes loops remove
lemma fluxZ (u:fluxV E I)(i:I): u.val i i=0:=by
    apply (smul_eq_zero_iff_right (by norm_num:(2:ℝ)≠0)).1; rw [two_smul]; exact u.property i i
lemma F_neg(u:fluxT E I)(i j k:I): u.val i j k= -u.val i k j:=flux_neg ⟨_,u.property.1 i⟩ _ _
lemma F_slot0(u:fluxT E I)(i j:I): u.val i j j=0:=fluxZ ⟨_,u.property.1 i⟩ _
lemma curl_neg (i j:I)(x:Y): CurlMap F i j x+CurlMap F j i x=0:=by unfold CurlMap; simp
lemma cycle_d(i j k:I): advance i (CurlMap F j k)+advance j (CurlMap F k i)+advance k (CurlMap F i j)=0:=by
 unfold CurlMap; rw [advance_sub,advance_sub,advance_sub]; rw [show advance i (advance k (F j))=_ from advance_switch k i _,show advance k (advance j (F i))=_ from advance_switch j k _,show advance j (advance i (F k))=_ from advance_switch i j _]; abel
-- radial releases (on positive edge from x along i). Color not needed yet.
def formC (a:fluxV E I) : Wheel I E := fun i=> (1/2:ℝ) • slope (fun j=> a.val j i)
def lineS (x:Y)(j:I) := digit x j+1/2
abbrev lineSi (x:Y)(i j:I) := digit x j+ (hit j i)/2
abbrev lineP (x:Y)(i k j:I) := digit x j+(hit j i+hit j k)/2
def formT (a:fluxT E I) : Wheel I E:=fun i x=> (1/3:ℝ) • (∑ j,digit x j • (∑ k,lineSi x i k • a.val k j i))
def faceT (a:fluxT E I)(i j:I)(x:Y):E:= ∑ k,lineP x i j k • a.val k i j
lemma face_eval(a:fluxT E I)(i j:I)(x:Y): faceT a i j x= slope (fun k=> a.val k i j) x+(1/2:ℝ) • (a.val i i j+a.val j i j):=by
 unfold faceT slope; simp_rw [lineP, add_smul, sum_add_distrib]; congr 1
 simp_rw [add_div,add_smul, sum_add_distrib]; unfold hit; rw [smul_add]
 have ht(i:I)(f:I→E): (∑ k,((if k=i then 1 else 0)/2:ℝ) • f k)=(1/2:ℝ) • f i:=by
    rw [sum_eq_single i]; · rw [if_pos rfl]
    · intro j _ p; rw [if_neg p,zero_div,zero_smul]
    simp
 exact congrArg₂ _ (ht i _) (ht j _)
lemma face_stepT (a:fluxT E I)(i j k:I): advance k (faceT a i j)=fun _=> a.val k i j:=by funext x; unfold advance; rw [face_eval,face_eval,add_sub_add_right_eq_sub,paper_shift1,add_sub_cancel_left]
lemma formC_step (a:fluxV E I)(i j:I)(x:Y): advance i (formC a j) x=(1/2:ℝ) • a.val i j:=by unfold formC; rw [advance_smul,φ_step,Pi.smul_apply]
lemma formC_P (a:fluxV E I)(i:I): Paper 2 (formC a i):=(school I ℝ E 2).smul_mem _ (slope_paper _)
lemma formC_flux (a:fluxV E I)(i j:I): CurlMap (formC a) i j= fun _=> a.val i j:=by funext x; simp only [CurlMap,Pi.sub_apply,formC_step]; rw [flux_neg a j i, smul_neg]; module
private abbrev slender (v:I→E)(i:I)(x:Y): E:=∑ j,lineSi x i j • v j
lemma slender_out (v:I→E)(i:I)(x:Y): slender v i x=slope v x+(1/2:ℝ) • v i:=by
 unfold slender lineSi slope; simp_rw [add_smul,sum_add_distrib]; congr 1; rw [sum_eq_single i]; · simp [hit]
 · intro j _ p; simp [hit,p]
 simp
lemma formT_step (a:fluxT E I)(i j:I)(x:Y): advance i (formT a j) x=(1/3:ℝ) • (slope (a.val i · j) x+(slender (fun k=> a.val k i j) j x+a.val i i j)):=by
 unfold advance formT; rw [← smul_sub]; congr 1; -- caution parentheses in statement
 let S(k):= (a.val · k j)
 have hp(k): slender (S k) j (x+b₁ i)= slender (S k) j x + S k i:=by rw [slender_out,slender_out,paper_shift1]; abel
 change (∑ k,digit (x+_) k • slender (S k) j _) - (∑ k,digit x k • slender (S k) j x)= _; simp_rw [digit_step,hp, add_smul, smul_add, hit]; simp [slope,S,Finset.sum_add_distrib,add_assoc] -- tune
lemma formT_P (a:fluxT E I)(i:I): Paper 3 (formT a i):=by
 rw [paper_leg]; intro j; have he : advance j (formT a i) = (1/3:ℝ) • ( slope (a.val j · i) + ((slope (a.val · j i)+ fun _=> (1/2:ℝ) • a.val i j i)+ fun _=> a.val j j i)):=by funext x; rw [formT_step]; simp only [Pi.smul_apply,Pi.add_apply,slender_out] -- tune
 rw [he]; refine (school I ℝ E 2).smul_mem _ (paper_add (slope_paper _) ?_); exact paper_add (paper_add (slope_paper _) (paper_low (paper_const _) one_le_two)) (paper_low (paper_const _) one_le_two)
lemma formT_flux (a:fluxT E I)(i j:I): CurlMap (formT a) i j=faceT a i j:=by
 funext x; rw [CurlMap,Pi.sub_apply,formT_step,formT_step,face_eval,slender_out,slender_out];
 let E:=fun k=> a.val k i j; let J:=slope E x; let A:=slope (a.val i · j) x; let B:=slope (a.val j · i) x;
 -- check constant term via i i j = E i. and slope antic mod all
 have hx: slope (a.val · j i) x= -J:=by unfold J E slope; rw [←sum_neg_distrib]; apply sum_congr rfl; intro k _; dsimp only; rw [F_neg _ _ j i,smul_neg]
 have he(k): a.val i k j-a.val j k i= E k:=by -- Bianchi sign verify i,j,k cycle i j k + j k i + k i j=0 => i k j - j k i = k i j
    have hh:=a.property.2 i j k; rw [F_neg _ i j k] at hh; unfold E; rw [show a.val k i j=-(-(a.val i k j)+ a.val j k i) from eq_neg_of_add_eq_zero_right hh]; abel
 have hy:A-B=J:=by unfold A B J slope; rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; dsimp only; rw [←smul_sub,he]
 rw [hx,F_neg a i j i,F_neg a j j i]; change (1/3:ℝ) • (A+(J+_+ E i))- (1/3:ℝ) • (B+(-J+ (1/2:ℝ) • (-E i)+ -E j))= J+(1/2:ℝ) • (E i + E j); rw [←hy]; module

variable {F}
def mouthV (X:Wheel I E):fluxV E I:=⟨fun i j=> CurlMap X i j 0,(fun i j=> curl_neg ..)⟩
def mouthT (X:Wheel I E) : fluxT E I :=⟨fun i j k=> advance i (CurlMap X j k) 0, ⟨fun i j k=> by
    have he:CurlMap X j k + CurlMap X k j=0:= funext (fun x=> curl_neg ..); rw [← Pi.add_apply,← advance_add]; -- tune
    change advance i _ 0=_; rw [he,advance_zero]; rfl,
    fun i j k=> congrFun (cycle_d ..) _⟩⟩
abbrev rank0 (a:fluxT E I): fluxV E I:= by -- def coefficient shift
 refine ⟨fun i j=> faceT a i j 0,fun i j=>?_⟩; change faceT a i j 0+faceT a j i 0=0; rw [← formT_flux,← formT_flux]; apply curl_neg
def letterV (X:Wheel I E): fluxV E I:= mouthV X - rank0 (mouthT X)
lemma folded (p:∀ i,Paper 3 (F i))(i j:I): CurlMap F i j= CurlMap (formC (letterV F) + formT (mouthT F)) i j:=by
 let E:= CurlMap F i j
 have hp:Paper 2 E:=paper_dec (paper_leg.mp (p _) _) (paper_leg.mp (p _) _)
 funext x; calc
   CurlMap F i j x=dock E x := congrFun (dock_sewn E hp).symm x
   _=(letterV F).val i j + faceT (mouthT F) i j x:=by
      rw [face_eval]; change E 0+slope _ _=(E 0-faceT _ _ _ 0)+ _
      rw [face_eval, slope₀]; change (E 0)+(slope (fun k=> advance k E 0) _) = (E 0 - (0+_))+((slope (fun k=> advance k E 0) _)+_); abel
   _= _:=by rw [← show CurlMap (formC (letterV F)) i j x=_ from congrFun (formC_flux ..) x,← formT_flux]; apply (congrFun (f:=CurlMap (formC (letterV F)) i j+CurlMap (formT (mouthT F)) i j) _ x); simp only [CurlMap,Pi.add_apply,advance_add]; abel
lemma direction2 (p:∀ i,Paper 3 (F i)):∃ f:Y→E,Paper 4 f ∧ ∀ i, F i=formC (letterV F) i+formT (mouthT F) i+advance i f:=by
 let T:=formC (letterV F); let U:= formT (mouthT F); let E:= F-(T+U); have h(i j):CurlMap E i j=0:=by
    have hv:=folded p i j; change CurlMap F i j=CurlMap (T+U) i j at hv; rw [←sub_eq_zero] at hv; refine Eq.trans ?_ hv; unfold CurlMap; unfold E; simp only [Pi.sub_apply, advance_sub]; abel
 obtain ⟨X,p,uY⟩:=grain_shape E h (fun i=>paper_dec (p _) (paper_add (paper_low (formC_P _ _) (Nat.le_succ 2)) (formT_P _ _)))
 refine ⟨X,p,fun i=>?_⟩; rw [uY]; change F i=T i+U i+(F i-(T i+U i)); abel
lemma direction1 (p:∀ i,Paper 2 (F i)):∃ f:Y→E,Paper 3 f ∧ ∀ i, F i=formC (mouthV F) i+advance i f:=by
 let T:= formC (mouthV F); let E:=F-T; have h(i j):CurlMap E i j=0:=by
    obtain ⟨c,v⟩:= (paper_firm (CurlMap F i j)).1 (paper_dec (paper_leg.mp (p _) _) (paper_leg.mp (p _) _)); have hc:CurlMap T i j= CurlMap F i j:=by rw [formC_flux]; apply funext; intro x; change CurlMap F i j 0 =_; rw [v]
    refine Eq.trans ?_ (sub_eq_zero.mpr hc.symm); unfold CurlMap E; simp only [Pi.sub_apply, advance_sub]; abel
 obtain ⟨X,t,u⟩:= grain_shape E h fun i=> paper_dec (p _) (formC_P _ _)
 refine ⟨X,t,fun i=>?_⟩; rw [u]; change F i=T i+(F i-T i); abel
lemma direction0 (p:∀ i,Paper 1 (F i)):∃ f:Y→E,Paper 2 f ∧∀ i, F i=advance i f:=by obtain ⟨X,t,h⟩:= grain_shape F (fun i j=> sub_eq_zero.mp (show CurlMap F i j-0=0 from (by rw [sub_zero]; change advance i (F j)-advance j (F i)=_; rw [paper_start.mp (paper_leg.mp (p _) _),paper_start.mp (paper_leg.mp (p _) _),sub_zero]))) p; exact ⟨X,t,fun i=>(h i).symm⟩
end Fluxim
end YM.FlightFlux
end
