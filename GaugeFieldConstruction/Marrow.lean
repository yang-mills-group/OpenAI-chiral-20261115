import GaugeFieldConstruction.Brill
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section

/-- Ledger of any pose; arbitrary mesh ends, permits sufficiently high
 shared integration height. Pay through this same Spine. -/
def HabitLevel (P:Spine)(j:Axis)(F:P.Test)(s:ℕ)(A B:P.meshPin)(X:P.Slabs j) (t:ℕ):Prop :=
 s ≤ t ∧ ∃ (a:ℤ)(v:ℕ), P.stampPin t a=A ∧ P.stampPin t v=B-A ∧
 P.BEntry j v (P.shifts j (-a) (P.conveying s (t-s) F)) ∧ X=P.HabBox j t v (P.shifts j (-a) (P.conveying s (t-s) F))

def Habitable (P:Spine)(j:Axis)(F:P.Test)(s:ℕ)(A B:P.meshPin)(X:P.Slabs j):Prop:= ∃ t:ℕ, P.HabitLevel j F s A B X t

variable {P:Spine} {j:Axis} {F G:P.Test}{S:Finset Cover}
variable {s t k v:ℕ} {A B D E:P.meshPin} {X Y:P.Slabs j} {a b:ℤ} {w:ℕ}
local notation "π"=>P.stampPin
local notation "M"=>timeMesh P.par
local notation "η₀"=>P.HabBox j
lemma HabitLevel.for_me (p:P.HabitLevel j F s A B X t)(q:π t a=A)(e:π t w=B-A):
 P.BEntry j w (P.shifts j (-a) (P.conveying s (t-s) F)) ∧ X= P.HabBox j t w (P.shifts j (-a) (P.conveying s (t-s) F)) :=by
 obtain ⟨_,u,g,u',v',h⟩:=p; obtain rfl:=notch_tight M t (u'.trans q.symm); have hx:=notch_tight M t (v'.trans e.symm); have :g=w:=by omega
 subst w; exact h
lemma HabitLevel.higher (p:P.HabitLevel j F s A B X t)(e:t≤k): P.HabitLevel j F s A B X k:=by
 obtain ⟨h,u,g,r₁,r₂,hT,m⟩:=p; let v:=P.par.R.L.val^(k-t)*g; let o:=castor M t k u
 have he: castor M t k (-u)=-o:=by unfold o castor; ring
 have hv: castor M t k g=(v:ℤ):=by unfold v castor; push_cast; rfl
 refine ⟨h.trans e,o,v,(notch_up M t k e u).trans r₁,by rw [←hv]; exact (notch_up M t k e _).trans r₂,?_⟩
 let x:=P.conveying s (t-s) F
 have hx:P.conveying t (k-t) (P.shifts j (-u) x)=P.shifts j (-o) (P.conveying s (k-s) F):=by rw[P.walk_rig,he];unfold x; rw[convey_higher F h e]
 rw [←hx]; exact ⟨hT.raise t k e, m.trans (HabBox_raise t hT k e).symm⟩
lemma HabitLevel.twins (p:P.HabitLevel j F s A B X t)(q:P.HabitLevel j F s A B Y t):X=Y:=by
 obtain ⟨_,a,v,r,k,u,rfl⟩:=p; exact (q.for_me r k).2.symm
lemma HabitLevel.pos (p:P.HabitLevel j F s A B X t): (A:ℝ)< (B:ℝ):=by
 obtain ⟨_,a,v,r,k,u,_⟩:=p
 have hv : 0< bell M t v:=by rw[natural_time]; exact when_pos M t v u.pos
 rw [show bell M t v= (π t v:ℝ) from rfl, k] at hv; exact sub_pos.mp hv

lemma Habitable.event (p:P.Habitable j F s A B X):∀ᶠ t:ℕ in atTop,P.HabitLevel j F s A B X t:=by
 obtain ⟨a,u⟩:=p; exact (eventually_ge_atTop a).mono fun _ h => u.higher h
lemma Habitable.from_event (p:∀ᶠ t in atTop,P.HabitLevel j F s A B X t):P.Habitable j F s A B X:=p.exists
lemma Habitable.same(p:P.Habitable j F s A B X)(q:P.Habitable j F s A B Y): X=Y:=by
 obtain ⟨t,h,k⟩:= (p.event.and q.event).exists; exact h.twins k
lemma Habitable.pos(p:P.Habitable j F s A B X):(A:ℝ)<(B:ℝ):=p.choose_spec.pos
lemma Habitable.direct (u:P.BEntry j w (P.shifts j (-a) F))(t:ℕ):P.Habitable j F t (π t a) (π t (a+w)) (η₀ t w (P.shifts j (-a) F)):=by
 refine ⟨t,le_rfl,a,w,rfl,?_ ,?_⟩
 · change _= notch _ _ _ - _; rw [notch_add]; abel -- tune
 rw [convey_start]; exact ⟨u,rfl⟩
lemma Habitable.forward(h:s ≤ t): P.Habitable j F s A B X ↔ P.Habitable j (P.conveying s (t-s) F) t A B X:=by
 suffices q:∀ k:ℕ,t≤k→ (P.HabitLevel j F s A B X k ↔ P.HabitLevel j (P.conveying s (t-s) F) t A B X k) by
    refine ⟨fun p=>?_,fun p=>?_⟩
    all_goals
      apply from_event
      filter_upwards [eventually_ge_atTop t,p.event] with k ht hp
      first | exact (q k ht).1 hp | exact (q k ht).2 hp
 intro k ht; unfold HabitLevel; rw [convey_higher F h ht,and_iff_right ht,and_iff_right (h.trans ht)]
lemma housed (u:F∈bay P.calibration S true)(p:(A:ℝ)<(B:ℝ))
 (q:P.Marrow j s (A:ℝ) (B:ℝ) S):∃ X:P.Slabs j,P.Habitable j F s A B X:=by
 obtain ⟨t,h₁,⟨a,r'⟩,v,hv⟩:= (((eventually_ge_atTop s).and ((minted_tall A).and (minted_le_sub p.le)))).exists -- tune
 have h':π t (a+v)=B:=by
   change notch _ _ _= _; rw[notch_add]; change π t a+ π t v=B; rw [r',hv]; abel
 let T:=volumeAround P.par P.width (t-s) S
 have e:P.conveying s (t-s) F∈bay P.calibration T true:= (proceeds _ _ P.history.circuit s (t-s) ((Tapestry.locates ..).mp u)).1
 have y:=q.refine h₁
 rw [←r',←h'] at y
 have hr:0<v:=by
   rw[←r',←h'] at p
   by_contra! t; have :v=0:=Nat.eq_zero_of_le_zero t
   simp [this] at p
 exact ⟨_,t,h₁,a,v,r',hv,BEntry.mesh_frame (P:=P) e hr y,rfl⟩
lemma Habitable.one (P:Spine){A B:P.meshPin}(j:Axis)(p:(A:ℝ)<(B:ℝ))(s:ℕ):P.Habitable j 1 s A B (P.Eucl j ((B:ℝ)-(A:ℝ)).toNNReal):=by
 obtain ⟨X,u⟩:= housed (j:=j) (S:=∅) (F:=1) (one_mem (bay P.calibration ∅ true)) p (s:=s) (fun i v=>by simp at v)
 obtain ⟨t,h,v,w,e,y,H,rfl⟩:=u
 let η:=P.HabBox j t w
 let Y:ℝ:=(B:ℝ)- (A:ℝ)
 let T:=timeMesh P.par
 have v':P.conveying s (t-s) 1=1:=Subtype.ext (woven_one P.run P.large P.history.circuit _ _)
 have ht:((whenly T t w:ℝ≥0):ℝ)=Y:=by rw [show ((whenly T t w:ℝ≥0):ℝ)=(P.stampPin t w:ℝ) from (natural_time ..).symm,y]; rfl
 refine ⟨t,h,v,w,e,y,H,?_⟩
 rw [v',map_one,HabBox_one _ P _ H.pos]
 rw [←show (whenly T t w) = Y.toNNReal from by rw [←ht, Real.toNNReal_coe]] -- may need change
local notation "χ"=>P.history.circuit
lemma conveying_both (F G:P.Test): P.conveying s k (F+G)=P.conveying s k F+P.conveying s k G:=Subtype.ext (woven_add P.run P.large χ _ _ F.property G.property)
lemma conveying_weight (F:P.Test)(z:ℂ):P.conveying s k (z•F)=z• P.conveying s k F:=Subtype.ext (woven_smul P.run P.large χ _ _ F.property z)
lemma Habitable.plus (p:P.Habitable j F s A B X)(q:P.Habitable j G s A B Y):P.Habitable j (F+G) s A B (X+Y):=by
 obtain ⟨t,he,hv⟩:= (p.event.and q.event).exists; obtain ⟨m,u,v,r,g,e,rfl⟩:=he; obtain ⟨d,rfl⟩:=hv.for_me r g
 refine ⟨t,m,u,v,r,g,?_⟩; rw [conveying_both,map_add,HabBox_add t e d]; exact ⟨e.add d,rfl⟩
lemma Habitable.scale (p:P.Habitable j F s A B X)(z:ℂ):P.Habitable j (z•F) s A B (z•X):=by
 obtain ⟨t,m,u,v,r,g,e,rfl⟩:=p
 refine ⟨t,m,u,v,r,g,?_⟩; rw [conveying_weight,map_smul,HabBox_smul t e z]; exact ⟨e.smul z,rfl⟩
lemma Habitable.minus (p:P.Habitable j F s A B X)(q:P.Habitable j G s A B Y):P.Habitable j (F-G) s A B (X-Y):=by
 simpa [sub_eq_add_neg] using p.plus (q.scale (-1))
lemma pin_time (p:π t w=B-A): ((B:ℝ)-(A:ℝ)).toNNReal=whenly M t w:=by
 have h:((whenly M t w:ℝ≥0):ℝ)=(B:ℝ)-(A:ℝ):=by rw [show ((whenly M t w:ℝ≥0):ℝ)=(π t w:ℝ) from (natural_time ..).symm,p]; rfl
 rw [←h,Real.toNNReal_coe]
lemma Habitable.pad (p:P.Habitable j F s A B X)(d:(D:ℝ)≤(A:ℝ))(e:(B:ℝ)≤(E:ℝ)):
 P.Habitable j F s D E ((P.Eucl j ((A:ℝ)-(D:ℝ)).toNNReal*X)*P.Eucl j ((E:ℝ)-(B:ℝ)).toNNReal):=by
 obtain ⟨t,v,⟨n,hn⟩,l,hl⟩:= (p.event.and ((minted_le_sub d).and (minted_le_sub e))).exists
 obtain ⟨h₁,a,w,r,g,w',rfl⟩:=v
 let η:=P.shifts j (-a) (P.conveying s (t-s) F)
 have H₀ : π t (a-n)=D:=by rw [minted_sub]; rw [hn,r]; abel
 have H₁ : π t (↑(n+w+l):ℤ)=E-D:=by
   push_cast; change notch _ _ _=_; rw [notch_add,notch_add]
   change π t (n:ℤ)+π t (w:ℤ)+π t (l:ℤ)=_
   rw[hn,hl,g]; abel
 have ht:=HabBox_left t w' n; have hx:P.shifts j n η=P.shifts j (-(a-n)) (P.conveying s (t-s) F):=by unfold η; rw[P.shifts_sum]; congr 2; ring
 refine ⟨t,h₁,a-n,n+w+l,H₀,H₁,?_⟩
 rw [←hx,pin_time hn,pin_time hl]
 refine ⟨w'.pad n l,?_⟩
 rw [←ht,HabBox_right t (w'.left n) l]

lemma convey_flips (F:P.Test):P.conveying s k (P.reflectTest j F)=P.reflectTest j (P.conveying s k F):=Subtype.ext (by
 have v:=stream_flipped P.run P.large χ s k j 0 F.property; rw [mul_zero] at v; exact v)
lemma pinch_back (G:P.Test)(w:ℕ):P.riposte j w G=P.shifts j w (P.reflectTest j G):=Subtype.ext (by
 have h:= mirror_cancel P.calibration j w 0 G.property; rw [sub_zero,gaugeT_zero] at h; exact h)
lemma Habitable.kissed(p:P.Habitable j F s A B X):P.Habitable j (P.reflectTest j F) s (-B) (-A) (star X):=by
 obtain ⟨t,h₁,a,w,r,g,H,rfl⟩:=p
 let K:= P.conveying s (t-s) F; let G:= P.shifts j (-a) K
 have u : π t (a+w)=B:=by
   change notch _ _ _=_; rw[notch_add]; change π t a+ π t w=_; rw [r,g]; abel
 have e: π t (-(a+w))=-B:= by rw [minted_neg,u]
 have y: P.shifts j (a+w) (P.reflectTest j K)=P.riposte j w G:=by
   rw [pinch_back, show P.reflectTest j G=P.shifts j (-(-a)) (P.reflectTest j K) from Subtype.ext (mirror_relocate P.calibration j _ _ K.property), P.shifts_sum]; rw [neg_neg,add_comm]
 refine ⟨t,h₁,-(a+w),w,e,(by rw[g]; abel),?_⟩
 rw [convey_flips,neg_neg]; change (P.BEntry j w (P.shifts j (a+w) (P.reflectTest j K))∧star (P.HabBox j t w G)=_); unfold K at *; rw [y]; exact ⟨H.riposte,HabBox_star t H⟩
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
