/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.LineUp.Aspect
import YM.SU5.Registration.Ink.Potential
import YM.Work.C28
/-!
 # Ink point scores, over R.Carriage
 Proof boosts W and momentum already, now integrate full Poincare costs even on G.
 Not rotations on G itself (vectors live in point station); merely W values & compatibility.
 Structure adapted C28 etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Filter MeasureTheory Measure Set Complex
open Boundary Probe Mink Mink.Poincare
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open HelioRoof Carton WView
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]{n:ℕ}
variable {B:Carton S V}
namespace InkPort
variable {F:InkWaves V}{W:WView V}{R:Courts V}(p:InkPort B F W) (h:R.Carriage F)
-- translation without orientation condition!
private lemma train_translation (z:Times n)(x:SpacePoints n)(v: Fin n→V)(s:ℝ≥0)(k b:ℂ)(a t:Space3) : B.trainZ s n (fun i=> z i+k) (fun i=>x i+t) v (b+k) (a+t) = B.trainZ s n z x v b a:= by
 induction n generalizing b a with
 | zero=> rfl
 | succ n ih=>
    rw [Carton.trainZ,Carton.trainZ]; simp only [add_sub_add_right_eq_sub]; exact congrArg (fun X:H=> Carton.ripZ S _ _ _ (B.bar s (v 0) X)) (ih (Fin.tail z) (Fin.tail x) (Fin.tail v) _ _)
private lemma matrix_translation (z:Times n)(x:SpacePoints n)(v:Fin n→V)(s:ℝ≥0)(k:ℂ)(t:Space3) : B.matrixZ s n (fun i=> z i+k) (fun i=>x i+t) v=B.matrixZ s n z x v:=by
 cases n with
 | zero=> rfl
 | succ n=> rw [Carton.matrixZ,Carton.matrixZ]; refine congrArg (fun X:H=>inner ℂ B.omega ((B.bar s (v 0)) X)) (?_); exact train_translation (Fin.tail z) (Fin.tail x) _ s _ _ _ _
include p
lemma same_time_plane (z:Times n)(g:z∈strict n)(x:SpacePoints n)(v:Fin n→V)(k:ℂ)(t:Space3) : F.F n (fun i=> z i+k) (fun i=> x i+t) v=F.F n z x v:=by
 obtain ⟨s,w⟩:= Work.C03.exists_lit g; have e: Small.lit (fun i=>z i+k) s:= by
   refine ⟨w.1,w.2.1,fun i j h=>?_⟩; simp only [add_im,add_sub_add_right_eq_sub]; exact w.2.2 i j h
 rw [p.strict_mat n _ (Work.C03.lit_strict e) s e,p.strict_mat n z g s w,matrix_translation]
lemma markup (p':Points n)(v:Fin n→V)(y:Heights n)(t:E4)(e:y∈east n) : F.restricted v y ((translation t).zusammen n p')=F.restricted v y p':=by
 let z:= Boundary.shift p' y; have h:z∈strict n:=by simpa [z] using on_profile p' y 1 (by norm_num) e
 unfold InkWaves.restricted; rw [← same_time_plane p z h (trace p') v (YM.time t:ℂ) (spatial t)]
 congr 2
 · ext1 i; simp [Boundary.shift, z, zusammen]; abel -- enough
lemma travels_world (v:Fin n→V)(f:Joint n)(x:E4) : W.W n v (Joint.gpush n (translation x) f)=W.W n v f:= WView.corner_maps p.level _ _ _ (fun i j a=> p.markup i v j x a) _
include h
lemma fades : W.SelfSpeaks R:= WView.real_rot (inkBoost p.region p.gap_cost p.path p.weighted p.lines h) p.region h p.level -- order notation?
lemma hue (v:Fin n→V)(f:Joint n)(x:Poincare): W.W n (fun i=> R.mi x.Λ (v i)) (Joint.gpush n x f)=W.W n v f:=by
 rw [Work.C28.gpush_split,p.travels_world]; exact (fades p h).rotation ..
-- Direction from HelioRaster to point sector rotations. Need partner commutation on THAT actual label store, from request label structure. Include separately.
end InkPort
namespace Courts
variable (R:Courts V)
def Parley (J:JMap V): Prop:= ∀ (r:Lorentz)(v:V), J (R.mi r v)=R.mi r (J v)
-- all boosts enough for locality later. charges adjoint also transform. Parley stays hypothesis.
noncomputable def foreign (p:Poincare)(s:MarkType V): MarkType V:= (R.mi p.Λ s.1,Joint.push p s.2)
noncomputable def exchanges (p:Poincare)(s:MarkWords V): MarkWords V:=s.map (R.foreign p)
lemma foreign_one (s:MarkType V) : foreign R 1 s=s:=by
 refine Prod.ext (R.mi1 _) (?_); change Joint.push 1 s.2=s.2; ext1 p; rw [Joint.push_at,inv_one,Poincare.sends_one]
lemma foreign_comp (s:MarkType V)(p q:Poincare) : R.foreign (p*q) s=R.foreign p (R.foreign q s):=by
  refine Prod.ext ?_ ?_
  · apply R.miMul --?
  change Joint.push (p*q) s.2 = Joint.push p _; ext1; rw [Joint.push_at,Joint.push_at]; change s.2 _ = Joint.push q s.2 _; rw [Joint.push_at,mul_inv_rev,Poincare.sends_mul]
lemma foreign_slide (u:E4) (p:MarkType V): R.foreign (translation u) p=(p.1,ahead u p.2):= by
 refine Prod.ext (R.mi1 _) ?_; change Joint.push (translation u) p.2=ahead u p.2; ext1 x; simp [translation]
lemma passport_pt (p:MarkWords V) : R.exchanges 1 p=p:=by simp [exchanges, show R.foreign 1=id from funext fun x=> R.foreign_one x]
lemma passport_comp (s:MarkWords V)(p q:Poincare) : R.exchanges (p*q) s=R.exchanges p (R.exchanges q s):=by simp [exchanges,show R.foreign (p*q)=R.foreign p ∘ R.foreign q from funext fun x=> R.foreign_comp x p q]
lemma stars_foreign (J:JMap V)(h:R.Parley J)(x:Poincare)(s:MarkType V):opTag J (R.foreign x s) = R.foreign x (opTag J s):=by
 refine Prod.ext (h x.Λ _) ?_; change Probe.bar (Joint.push x s.2)=Joint.push x (Probe.bar s.2); ext1; simp [opTag,foreign] -- tune
lemma stars_too (J:JMap V)(h:R.Parley J)(x:Poincare)(s:MarkWords V): wordRev J (R.exchanges x s) = R.exchanges x (wordRev J s):= by simp [wordRev,exchanges,show opTag J ∘ R.foreign x= R.foreign x ∘ opTag J from funext fun v=> stars_foreign R J h x v]
variable {W:WView V}{F:InkWaves V}(z:InkPort B F W)(h:R.Carriage F)
include z h
lemma operates (x:Poincare)(s:MarkWords V) : W.expect (R.exchanges x s)=W.expect s:=by
 rw [show R.exchanges x s=List.ofFn (R.foreign x ∘ s.get) from (by rw [← List.map_ofFn,List.ofFn_get]; rfl),W.expect_ofFn]
 let v := fun i => (s.get i).1; let f := fun i=> (s.get i).2
 change W.W s.length (fun i => R.mi x.Λ (v i)) (Joint.materialize _ (fun i => Joint.push x (f i))) = W.W s.length v (Joint.materialize _ f)
 rw [← Joint.tests]; exact z.hue h v _ x
lemma color_like (J:JMap V)(w:R.Parley J)(x:Poincare)(a b:MarkWords V): W.kernel J (R.exchanges x a) (R.exchanges x b)=W.kernel J a b:=by rw [WView.kernel,stars_too R J w]; refine Eq.trans ?_ (operates R z h x (wordRev J a ++ b)); simp only [exchanges,List.map_append]
omit z h
-- norm-continuity purchase for Action from W.Strong
lemma seen_actors {X:Type*}[TopologicalSpace X](W:WView V)(w:Fin n→MarkType V)(f:Fin n→X→Poincare)(p:∀ i,Continuous (f i)) : Continuous (fun x=> W.expect (List.ofFn (fun i=> R.foreign (f i x) (w i)))):=by
 simp_rw [WView.expect_ofFn]; apply continuous_iff_continuousAt.mpr; intro x'; let g(x:X)(i):= (R.mi (f i x).Λ) (w i).1; let u(x:X)(i):= Joint.push (f i x) (w i).2; have hv:Continuous u:=continuous_pi (fun i=> (Work.C28.continuous_push Work.C08.answer ((w i).2)).comp (p i)); let S x:= Joint.materialize n (u x); have hT:Continuous S:= (Joint.jointCont n).comp hv; refine GearContinuity.paid (v:=g) (T:=fun x=> W.askM (S x)) x' ?_ (fun i=> ((W.W n i).continuous.comp hT).continuousAt) -- binder notation err?
 intro j; obtain ⟨k,b,c,he,q⟩:= R.miC ((w j).1) (f j x').Λ; let K:= Poincare.Λ ∘ (f j); have hK:= (Poincare.continuousL.comp (p j)).continuousAt (x:=x'); exact ⟨k,b,fun i=>c i ∘ K,fun j=>  ContinuousAt.comp (x:=x') (g:=c j) (f:=K) (he j) hK,hK.eventually q⟩
lemma chambers_word (W:WView V)(J:JMap V)(i j:MarkWords V) : Continuous (fun p=> W.kernel J i (R.exchanges p j)) := by
  let l := wordRev J i
  let w := Fin.append l.get j.get
  let g : Fin (l.length+j.length) → Poincare → Poincare := Fin.append (fun _ : Fin l.length => fun _ => 1) (fun _ : Fin j.length => id)
  have hg (a) : Continuous (g a) := by
    refine Fin.addCases ?_ ?_ a
    · intro a; simp only [g, Fin.append_left]; exact continuous_const
    intro a; simp only [g, Fin.append_right]; exact continuous_id
  have hwords (p) : l ++ R.exchanges p j = List.ofFn (fun a => R.foreign (g a p) (w a)) := by
    rw [show (fun a => R.foreign (g a p) (w a)) = Fin.append l.get (R.foreign p ∘ j.get) from ?_,
      List.ofFn_fin_append, List.ofFn_get, ←List.map_ofFn,List.ofFn_get]; rfl
    funext a; refine Fin.addCases ?_ ?_ a
    · intro a; simp only [g,w,Fin.append_left]; exact R.foreign_one _
    intro a; simp only [g,w,Fin.append_right]; rfl
  change Continuous fun p=> W.expect (l ++ R.exchanges p j); simp_rw [hwords]; exact R.seen_actors W w g hg
end Courts
end YM.SatinWFixed
open YM.SatinWFixed
#print axioms InkPort.fades
#print axioms InkPort.hue
#print axioms Courts.color_like
#print axioms Courts.chambers_word
