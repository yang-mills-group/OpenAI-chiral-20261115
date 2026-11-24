import YM.SU5.LoomForce.AbsenceA
import YM.SU5.SatinWard.Resolution.Laker
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open _root_.Zephyr.Chern
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
variable {p:BudgetPoint} {K:Scree.Loom N}{e:ℝ}{q:ℕ} (z:Checked p K e d a k q)(E:Pattern P T r d a v)
variable (bI:Chamber.Division)(x:Site N)(s:Sweep N)(B:ℕ) (h: 2*(B+1)<(More N).val)
local notation "ξ" => node x
variable (yQ:4*(B+separation (node x) 1+2)+1< N.val) (pS:s.charge=false)(vX:QuadClock.Earlier s x x)
open Next.Rank Next.Rank.Spindle
local notation "AΘ" => _root_.Zephyr.Chern.arc
local notation "U" => turntable N
local notation "Y" => (flashA s ∘ (turntable N))
noncomputable abbrev orientAx (s:Signed)(u:PlaqAxes):ℝ :=(if xor (s.flip u.val.1) (s.flip u.val.2) then (-1:ℝ) else 1)*polarShift (s.perm u.val.1) (s.perm u.val.2)
noncomputable abbrev orientF (s:Signed)(B:ℕ) : FrameA B:= fun i=> orientAx s i.val.2 • polarLie
private lemma travelP (t:ℝ)(x:Seat N)(i j:Axis)(v:separation x 1≤ B)(h:4*B+1<N.val):travel (U t) x (oriented (posDir i) (posDir j)) = AΘ (polarShift i j*t) :=by -- copied Absence
 unfold oriented; rw [Step.rev_pos, Step.rev_pos]; simp only [travel,Step.vec_pos,Step.vec_neg,Step.neg_read,Step.pos_read]
 unfold turntable _root_.Zephyr.Chern.petals; simp_rw [← arc_neg, ←arc_zero,←arc_add]; refine congrArg AΘ ?_
 rw [show x+step i+step j-step i=x+step j by abel,show x+step i+step j+-step i=x+step j by abel,add_sub_cancel_right]; rw [beamShift B x v h,beamShift B x v h]; rw [show polarShift j i= -polarShift i j from flux_switch ..]; ring
private lemma wander_clock (t:ℝ)(x:Seat N)(i j:Lattice.Step) : travel (U t) (x+i.vec) (oriented i.rev j) = (travel (U t) x (oriented i j))⁻¹:=by
 rw [oriented_swap j i.rev, oriented_next]; obtain ⟨b,hb⟩:= lives_range (t:=t) (N:=N) [i] x; obtain ⟨a,ha⟩:=lives_range (t:=t) (oriented i j) x; rw [travel,travel,mul_one] at hb; rw [ha,hb, ←arc_neg, ←arc_add, ←arc_add]; congr 2; abel
private lemma stroll_clock (t:ℝ)(x:Seat N)(i:Axis)(j:Lattice.Step)(v:ℝ) (p:travel (U t) (x-step i) (oriented (posDir i) j)=AΘ v): travel (U t) x (oriented (negDir i) j)= AΘ (-v) :=by
 have he:=wander_clock (N:=N) t (x-step i) (posDir i) j; rw [Step.vec_pos,sub_add_cancel, Step.rev_pos,p,←arc_neg] at he; exact he
private lemma sep_down (x:Seat N)(i:Axis): separation (x-step i) 1 ≤ separation x 1+1:=by
 have hp:=(Work.E01.sep_step_le (x-step i) i); rw [sub_add_cancel] at hp; exact (separation_triangle _ x _).trans (by omega)
private lemma spun_xy (t:ℝ)(x:Seat N)(i j:Lattice.Step)(p:separation x 1 + 2 ≤ B) (g:4*B+1<N.val) : travel (U t) x (oriented i j)= AΘ ((if xor i.neg j.neg then -1 else (1:ℝ))*polarShift i.dir j.dir*t):=by
 let β(y)(i j:Axis)(h:separation (y:Seat N) 1+1 ≤B) : travel (U t) y (oriented (negDir i) (posDir j))= AΘ (-(polarShift i j*t)):= stroll_clock t y i _ _ (travelP B t _ i j ((sep_down y i).trans h) g)
 have α(y)(i j:Axis)(h:separation (y:Seat N) 1+1 ≤ B): travel (U t) y (oriented (posDir i) (negDir j))= AΘ (-(polarShift i j*t)):=by rw [oriented_swap,β y j i h,show polarShift j i= -polarShift i j from flux_switch ..]; rw [neg_mul,neg_neg,←arc_neg]
 cases i with|mk i b=>
   cases j with|mk j c=>
    cases b <;> cases c
    · change travel _ _ _=AΘ ((1:ℝ)*_*_); rw [one_mul]; exact travelP B t _ i j (by omega) g
    · change travel _ _ _=AΘ ((-1:ℝ)*_*_); rw [neg_mul,one_mul,neg_mul]; exact α x i j (by omega)
    · change travel _ _ _=AΘ ((-1:ℝ)*_*_); rw [neg_mul,one_mul,neg_mul]; exact β x i j (by omega)
    · have ht:=stroll_clock t x i _ _ (α (x-step i) i j (by have e:=sep_down x i; omega)); rw [neg_neg] at ht; change travel _ _ _=AΘ ((1:ℝ)*_*_); rw [one_mul]; exact ht
include h yQ pS vX
local notation "M" => More N
private lemma berry_face (t:ℝ)(i:Turn B): registered B (Y t) ξ i=AΘ (t*orientAx s.s i.val.2):=by
 let F:=i.val.2; let T:=U t; let V:=Y t; let A:=(Cube.assembly N).embed s.b
 have ht:V= Lattice.pull s.s A T:=by change flashA s _= _; rw [revoke,pS]; rfl
 let f:=armFace B ξ i; rw [registering B _ h,spine,face_gauge]; change fingers V ξ f.1*faceValue V f *_= _
 obtain ⟨u,hu⟩:∃ w, fingers V ξ f.1=AΘ w:=by unfold fingers Spindle.leaves; rw [travel_at,ht,travel_pull]; exact lives_range ..
 rw [hu]; let a:=F.val.1; let b:=F.val.2
 have hZ:affine s.s A f.1= boxA s f.1 := (sitA ..).symm
 have H:faceValue V f=AΘ (t*orientAx s.s F):=by
    rw [ht, faceValue, travel_pull, hZ, show List.map _ _=oriented ((posDir a).rotate s.s) ((posDir b).rotate s.s) by change List.map _ (oriented (posDir a) (posDir b))=_; simp [oriented,←Step.rev_rotate]]
    have hz:separation (boxA s f.1) 1 ≤ B+separation ξ 1:=by apply (separation_triangle _ (boxA s ξ) _).trans; rw [sitT,show boxA s ξ=ξ from vX,separation_comm f.1]; exact Nat.add_le_add_right ((doors f.1).1 (village_le _ (faceOrigin i))) _
    have hs:=spun_xy (B+separation (node x) 1+2) t (boxA s f.1) ((posDir a).rotate s.s) ((posDir b).rotate s.s) (Nat.add_le_add_right hz 2) yQ; refine hs.trans (congrArg AΘ ?_); unfold orientAx; rw [mul_comm t _]; apply congrArg (· * t) <;> simp [posDir, Step.rotate,a,b,F] -- tune
 rw [H]; change AΘ u * AΘ _ * (fingers V ξ f.1)⁻¹=_; rw [hu, ←arc_neg, ← arc_add,←arc_add]; apply congrArg AΘ; unfold F; abel
noncomputable def bfSum (s:Signed)(B:ℕ)(W_:Word B):ℝ := (W_.map fun x=> (if x.2 then -1 else (1:ℝ))*orientAx s x.1.val.2).sum
lemma berry_played (L:Word B)(t:ℝ): played (registered B (Y t) ξ) L= group.lieExp (t • Spindle.stage L (orientF s.s B)):=by
 suffices a: played (registered B (Y t) ξ) L= AΘ (t*bfSum s.s B L) ∧ Spindle.stage L (orientF s.s B)=bfSum s.s B L • polarLie by rw [a.1,a.2,smul_smul,arc_lie]
 induction L with
 | nil=> simp [played,Spindle.stage,bfSum,arc_zero]
 | cons i L ih=>
    let f:= orientAx s.s i.1.val.2
    simp only [played,Spindle.stage, bfSum,List.map_cons,List.sum_cons,List.prod_cons] at *
    rw [ih.1,ih.2]; rw [berry_face x s B h yQ pS vX]
    cases q:i.2
    · refine ⟨?_,?_⟩
      simp only [Bool.false_eq_true,ite_false,one_mul]; rw [mul_add,arc_add]
      simp only [Bool.false_eq_true,ite_false,one_mul, orientF,add_smul]
    refine ⟨?_,?_⟩
    · simp only [ite_true,neg_mul,one_mul]; rw [←arc_neg,mul_add,mul_neg,arc_add]
    simp only [ite_true,neg_mul,one_mul,orientF,add_smul,neg_smul]
local notation "J" => install B ξ ∘L collectF B ξ h
lemma berry_guise (t:ℝ): Agrees (Spindle.patch B ξ) (spine (Y t) ξ) (increment 1 (t • J (orientF s.s B))) := by
 intro i a b; let y:Dim ξ B:=⟨i,mem_filter.mpr ⟨mem_univ _,a,b⟩⟩
 rw [show spine (Y t) ξ i = _ from spun (Y t) ξ h y, berry_played x s B h yQ pS vX]
 change _= group.lieExp (t • (if p:i∈_ then collectF B ξ h (orientF s.s B) ⟨i,p⟩ else 0)) *1
 rw [mul_one,dif_pos y.property]; rfl

