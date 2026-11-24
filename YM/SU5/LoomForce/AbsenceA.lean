import YM.SU5.LoomForce.FrameTaylor
import YM.SU5.LitCurrent.Bloom
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
section
open scoped Matrix.Norms.Frobenius Classical
variable (G:Gauge)
open SU
noncomputable def focalLie : group.Mat:= Matrix.diagonal fun i=>Complex.I*(dye.val i:ℂ)
lemma focal_has : focalLie ∈ group.lie:=by
 apply Thera.league.mpr; refine ⟨?_,?_⟩
 · ext i j; by_cases p:i=j <;> simp [focalLie,p,Ne.symm]
 change Matrix.trace (Matrix.diagonal fun i:Fin 5=> Complex.I * (dye.val i:ℂ))=0
 rw [Matrix.trace_diagonal,←Finset.mul_sum,← Complex.ofReal_sum,dye.property]; simp
noncomputable abbrev polarLie : group.Color:=group.projectColor focalLie
lemma arc_lie(t:ℝ) : _root_.Zephyr.Chern.arc t= group.lieExp (t • polarLie):=by
 apply group.mat_injective; rw [Gauge.mat_lieExp,map_smul,Gauge.colorMat_project_self _ focal_has]
 -- matrix proof
 change Matrix.diagonal (Kea.pw ∘ (diluted t).val)=NormedSpace.exp (t • focalLie)
 change Matrix.diagonal ((Kea.pw ∘ (diluted t).val) : SU.F→ℂ)=NormedSpace.exp (t • Matrix.diagonal (fun i:SU.F => Complex.I * (dye.val i:ℂ)))
 rw [←Matrix.diagonal_smul,Matrix.exp_diagonal]
 congr 1; funext i; simp [Kea.pw,BZ.phase,diluted,Complex.real_smul,Complex.exp_eq_exp_ℂ]; congr 1; ring
end 
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}

open Next.Rank Next.Rank.Spindle
variable (x:Site N)(B:ℕ)
local notation "W" => More N
local notation "G" => SU.group
local notation "AΘ" => _root_.Zephyr.Chern.arc
local notation "U" => turntable N

def polarShift (i j:Axis) := _root_.Zephyr.Chern.flux (step i) (step j)
def marker (F:PlaqAxes):group.Color:= polarShift F.val.1 F.val.2 • polarLie

lemma beamShift (x:Site (More N))(t:separation x 1≤B)(h:4*B+1<N.val)(i j:Axis):
   _root_.Zephyr.Chern.stream N (x+step i,j)=_root_.Zephyr.Chern.stream N (x,j)+polarShift i j/2:=by
 unfold _root_.Zephyr.Chern.stream twistAt; rw [show _root_.Zephyr.Chern.rel (x+step i)= _root_.Zephyr.Chern.rel x+step i from ?_, add_right_comm,flux_left,add_div]; rfl
 rw [←rel_add _ B (by rw [step_size]; exact h) _ t,wrap_step]
lemma faceShift (i:Face (Per (More N)))(t:separation i.1 1 ≤ B)(h:4*B+1<N.val)(g:ℝ) :
    faceValue (turntable N g) i = AΘ (polarShift i.2.val.1 i.2.val.2 * g) := by
 obtain ⟨x,⟨⟨i,j⟩,y⟩⟩:= i; change travel (turntable N g) x (square i j)= AΘ _
 unfold square; simp only [travel,Step.vec_pos,Step.vec_neg,Step.neg_read,Step.pos_read]
 unfold turntable _root_.Zephyr.Chern.petals; simp_rw [← arc_neg, ←arc_zero,←arc_add]; refine congrArg AΘ ?_
 rw [show x+step i+step j-step i=x+step j by abel,show x+step i+step j+-step i=x+step j by abel,add_sub_cancel_right]; rw [beamShift B x t h,beamShift B x t h]; rw [show polarShift j i= -polarShift i j from flux_switch ..]; ring

lemma lives_range (s:Lattice.Walk)(u:Seat N): ∃ b,travel (U t) u s=AΘ b:=by
 induction s generalizing u with
 | nil=> exact ⟨0,arc_zero.symm⟩
 | cons i p ih=>
   obtain ⟨x,h⟩:=ih (u+i.vec)
   suffices g:∃ b,i.read (U t) u=AΘ b by
     obtain ⟨b,h'⟩:=g; exact ⟨_,by rw [travel,h,h', ←arc_add]⟩ -- infer
   obtain ⟨i,tt|tt⟩:=i; exact ⟨_,rfl⟩; exact ⟨_,(arc_neg _).symm⟩
def Φmark : FrameA B := fun x=>marker x.val.2
variable (h: 2*(B+1)<(More N).val)(Uρ: 4*B+1 < N.val)
local notation "ξ" => node (0:Site N)
lemma focal_node (N:Side): node (0:Site N)=1:=by unfold node; rw [map_zero,zero_add]
include h Uρ
lemma magnetized (i:Turn B)(t:ℝ): registered B (turntable N t) ξ i = AΘ (t*polarShift i.val.2.val.1 i.val.2.val.2) := by
 let o:=wrap (More N) i.val.1+ξ; let f:= polarShift i.val.2.val.1 i.val.2.val.2; let P':= U t
 rw [registering B (U t) h,spine,face_gauge]; change fingers P' ξ o * faceValue P' (o,i.val.2) * _= AΘ (t*f)
 obtain ⟨b,hb⟩: ∃ b, fingers P' ξ o= AΘ b:= by
   unfold fingers Spindle.leaves P'; rw [travel_at]; exact lives_range ..
 rw [hb,faceShift B _ (show separation o 1 ≤B from ?_) Uρ t, ←arc_add,←arc_neg,←arc_add]; congr 1; unfold f; ring
 rw [separation_comm,←focal_node N]; apply (doors o).1 (village_le _ (faceOrigin i))

def fSum (W_:Word B):ℝ := (W_.map fun x=> (if x.2 then -1 else (1:ℝ))*polarShift x.1.val.2.val.1 x.1.val.2.val.2).sum
lemma played_focus (L:Word B)(t:ℝ): played (registered B (turntable N t) ξ) L= group.lieExp (t • Spindle.stage L (Φmark B)):=by
 suffices a: played (registered B (turntable N t) ξ) L= AΘ (t*fSum B L) ∧ Spindle.stage L (Φmark B)=fSum B L • polarLie by rw [a.1,a.2,smul_smul,arc_lie]
 induction L with
 | nil=> simp [played,Spindle.stage,fSum,arc_zero]
 | cons i L ih=>
    let s:=ξ; let f:= polarShift i.1.val.2.val.1 i.1.val.2.val.2
    simp only [played,Spindle.stage, fSum,List.map_cons,List.sum_cons,List.prod_cons] at *
    rw [ih.1,ih.2]; rw [magnetized B h Uρ]
    cases q:i.2
    · refine ⟨?_,?_⟩
      simp only [Bool.false_eq_true,ite_false,one_mul]; rw [mul_add,arc_add]
      simp only [Bool.false_eq_true,ite_false,one_mul, Φmark,marker,add_smul]
    refine ⟨?_,?_⟩
    · simp only [ite_true,neg_mul,one_mul]; rw [←arc_neg,mul_add,mul_neg,arc_add]
    simp only [ite_true,neg_mul,one_mul,Φmark,marker,add_smul,neg_smul]
local notation "J" => install B ξ ∘L collectF B ξ h
lemma guise (t:ℝ): Agrees (Spindle.patch B ξ) (spine (U t) ξ) (increment 1 (t • J (Φmark B))) := by
 intro i a b; let y:Dim ξ B:=⟨i,mem_filter.mpr ⟨mem_univ _,a,b⟩⟩
 rw [show spine (U t) ξ i = _ from spun (U t) ξ h y, played_focus B h Uρ]
 change _= group.lieExp (t • (if p:i∈_ then collectF B ξ h (Φmark B) ⟨i,p⟩ else 0)) *1
 rw [mul_one,dif_pos y.property]; rfl

lemma reading_focus {p:BudgetPoint}{K:Scree.Loom N}{e:ℝ}{q:ℕ} (z:Checked p K e d a k q)(E:Pattern P T r d a v)(t₀:B=p.B) : bud (compassLine E 0 K p k) 2= lapAsset (0:Site N) k B h E (Φmark B) :=by
 let X:= J (Φmark B); let f: tangD N→ℂ:=fun x=> untouched (E.A 0) k (increment 1 x)
 have he: compassLine E 0 K p k =ᶠ[𝓝 0] (fun q:ℝ=>f (q • X)):=by
   obtain ⟨v,s⟩:=tanks_live z.angle; have ht:∀ᶠ t:ℝ in 𝓝 0, ‖t • X‖≤v:= (show Continuous (fun t:ℝ=>‖t • X‖) by fun_prop).continuousAt.eventually (ge_mem_nhds (by simpa using s.size))
   filter_upwards [ht,petal_on p (offsetMask p.B (0:Site N)) (_root_.Zephyr.Chern.stream N)] with i ht hs
   let V:=increment 1 (i • X); let Q:=s.paid _ _ ht
   unfold compassLine; rw [map_zero]; change Surplus.tax K p 0 k E (U i)= _
   rw [← tax_invariant 0 z E (fingers (U i) ξ)]; refine tax_degree 0 z E _ V ((pingB ..).2 hs) ?_ (agrees_mono (guise B h Uρ i) (Corona.halo_mono (by have hp:=z.extra; omega : k≤B) (Subset.refl _)))
   exact ⟨fun x i j g=>(Q.1 x i j g).trans (half_le_self z.angle.le), fun x i j g=>(Q.2 x i j g).trans (half_le_self z.angle.le)⟩
 rw [bud_congr he]; change deriv (deriv fun q:ℝ=>f (q • X)) 0/2= (2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) 0 X X
 let F:=fun t:ℝ=>f (t • X)
 have h':=Spindle.upon X f 2 (show ContDiffAt ℝ (↑(2:ℕ)) _ _ from (unhat_smooth 0 z E).of_le (by norm_cast))
 rw [iteratedFDeriv_two_apply,iteratedDeriv_succ,iteratedDeriv_one] at h'; rw [h']; norm_num [Complex.real_smul]; ring
#print axioms reading_focus
end YM.CF.LitCurrent.Surplus
