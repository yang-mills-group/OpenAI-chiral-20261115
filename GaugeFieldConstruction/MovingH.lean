import GaugeFieldConstruction.Metope
import GaugeFieldConstruction.Canone
import GaugeFieldConstruction.Tropic
import GaugeFieldConstruction.Pliant
import GaugeFieldConstruction.Ethos
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
open Fock
variable (P:Spine)
open MeasureTheory
open Afterglow -- tune
local notation "Ω"=>P.floorVec
-- Alternative Porch gives linear itself for all tests fit BEntry.B.Q. Thus prove for any p.H3 and shift stamp.
variable {P}
open Papal Papal.FrameP
open CF.XGarden CF.XGarden.MastTin ArtCart
open RG Fock CF.Rush Vale Branch Fock.Flux Tapestry
open YM.Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open RG CF.Skye
open CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open scoped YM.CF.Mew
open CF.TableF TableF.Lenten TableF.Lenten.Layout Py
variable {P:Spine}{S:Finset Cover}{f:P.Test}{F:ℕ→Buffered.Family P.calibration}
open Jubilee CF.Hive CF.Scroll CF.Levier
variable {u: Shape} {b:Bool}{G:Family P.calibration}{g:P.Test}
open CF.Spire
lemma meetβ {F:ℕ→Family P.calibration}(p:P.LongQueue S F f)(m:Side)(x:Fields (P.calibration.c m)) : Tendsto (fun i=> F i m x) atTop (𝓝 (f.val m x)):=by
 apply Metric.tendsto_nhds.mpr; intro k v
 filter_upwards [p.saved _ (half_pos v)] with i h
 rw[dist_eq_norm]; exact lt_of_le_of_lt (h m x) (half_lt_self v)
lemma LiveTurn {F G:ℕ→ Family P.calibration}{S T:Finset Cover}(p:P.LongQueue S F f)(q:P.LongQueue T G g)
 (h:∀ᶠ i in atTop,Festive u b (F i) (G i)): Festive u b f.val g.val:=by
 intro m; let s:Sweep (P.calibration.c m):= ray b u
 refine ⟨fun x y=>?_⟩
 refine tendsto_nhds_unique_of_eventuallyEq (meetβ q m _) (?_:Tendsto (fun i=> Urn.lotB b (Typer s) (launchZ s) (F i m (x,y))) atTop _) (h.mono fun i u=> (u m).ride x y)
 have ht:Continuous (Urn.lotB b (Typer s) (launchZ s)):=Scree.tour_c ..
 exact ht.continuousAt.tendsto.comp (meetβ p m _)
abbrev cargoν (s:Shape)(v:Bool):Waves→Waves:= Fren.Mason (Levier.ray (N:=Reifier) v s) -- tune namespace
lemma Araw_ride (P:Spine)(s i:ℕ)(u:Shape)(v:Bool)(x:Cover)(a: Waves): Festive u v (P.Araw s (u.motion x) i a) (P.Araw s x i (cargoν u v a)):=by
 intro m; let T:=P.calibration.c m; let U:=ray (N:=T) v u
 refine ⟨fun A B=>?_⟩
 let p:=P.penIt s; let J:=P.par.h; let G:=P.MaleBook s i; let F:=BushRoot G p J (u.motion x) a; let W:=BushRoot G p J x (cargoν u v a)
 have h:P.Araw s (u.motion x) i a =John F P.calibration p.threshold:=rfl
 have g:P.Araw s x i (cargoν u v a)=John W P.calibration p.threshold:=rfl
 rw [g,h,show_V,show_V]; exact ShowSpin u v F W A (Μsend x G u v (zero_lt_one.trans_le P.par.height) (P.billStamp s).2 (P.billStamp s).1 a T) p.threshold
lemma Heritor.rideM (R:P.Heritor)(s:ℕ)(u:Shape)(v:Bool)(x:Cover)(A:Waves): Festive u v (R.M s (u.motion x) A).val (R.M s x (cargoν u v A)).val:= LiveTurn (R.earned _ _ _) (R.earned _ _ _) (Eventually.of_forall fun i=> P.Araw_ride s (R.path.subSeq i) u v x A)

variable (P) in
lemma FiledFest(p:Festive u b f.val g.val)(s i:ℕ):SweepTurn (count P.run s i) (Levier.ray b u) (filed P.run P.large s i f.val) (filed P.run P.large s i g.val) :=by
 let k:=momentm P.run i s
 let A(n:Side)(e:P.calibration.c k=n):Mark n:=e ▸ f.val k; let B(n:Side)(e:P.calibration.c k=n):Mark n:=e ▸ g.val k
 have h(n:Side)(e:P.calibration.c k=n):SweepTurn n (Levier.ray b u) (A n e) (B n e):=by subst n; exact p k
 exact h _ (terrain P.run P.large (P.run.ir i) s) -- P shadow hazard?
lemma E_frame (p:Festive u b f.val g.val)(s:ℕ): P.E s g.val=sailH u b (P.E s f.val):=by
 let R:=P.run; let H:=P.large
 have h(F: P.Test): Tendsto (fun n=> Journey.sharp R H s (P.gatePeriod n) (P.gateCut n) F.val) atTop (𝓝 (P.E s F.val)):=by
    obtain ⟨S,p⟩:=F.property.paid; obtain ⟨c,u,hx⟩:=P.history.implements s S
    obtain ⟨A,h⟩:=Journey.valuation P.run H p
    have hz: Tower.pay F.val A:= h; have hp: 0 ≤ A:= pay_nonneg hz
    apply Metric.tendsto_nhds.mpr; intro ε e; let d:=ε/(A+1); have hd:0< d:=div_pos e (by positivity)
    filter_upwards [hx d hd] with n z; have ht: d*A < ε:= by linarith only [show d*(A+1)=ε from div_mul_cancel₀ _ (by positivity),hd]
    rw[dist_eq_norm]; exact ((z F.val p A hz).2.2.2.2.1).trans_lt ht
 refine tendsto_nhds_unique_of_eventuallyEq (h g) (((sailH u b).toLinearMap.continuous_of_finiteDimensional).continuousAt.tendsto.comp (h f)) ?_
 filter_upwards [P.history.finance s] with i hv
 let N:= count P.run s (P.gatePeriod i)
 let V:= Levier.ray (N:=N) b u
 have he:=FiledFest P p s (P.gatePeriod i)
 have ht:=Booth P.run s (P.gatePeriod i) (P.gateCut i) hv.enters V _ (spinZ ..) _ _ he.1
 exact ht.trans (sail_val (N:=N) u b _)

lemma EraH (P:Spine)(j:Axis)(z:ℤ)(t:ℕ)(F:P.Test):P.E t (Tower.mirror P.calibration j z F.val)=star (P.E t F.val):=by
 obtain ⟨S,h⟩:=F.property.paid; let K:P.Test:=⟨_,aux_test (axial P.calibration j z h)⟩
 have p: Festive (plane j z) false F.val K.val:= mirrorFest h j z
 change P.E t K.val= _; rw [E_frame (f:=F) (g:=K) p]; unfold sailH; rw [show detX (plane j z).s=true from det_t _]; rfl

lemma rawMirror (P:Spine)(j:Axis)(i:ℤ)(s n:ℕ)(x y:Cover)(p:(plane j i).motion x=y)(A:Waves): Tower.mirror P.calibration j i (P.Araw s y n A)= P.Araw s x n (cargoν (plane j i) false A):=by
 obtain ⟨F,q,v,h⟩:= leafA P s y A n; apply Festive.same (mirrorFest (q ▸ h) j i); rw [← p]; exact P.Araw_ride s n (plane j i) false x A -- tune
lemma HueMirror (R:P.Heritor)(j:Axis)(i:ℤ)(s:ℕ)(x y:Cover)(p:(plane j i).motion x=y)(A:Waves): Tower.mirror P.calibration j i (R.M s y A).val= (R.M s x (cargoν (plane j i) false A)).val:=by
 apply Festive.same (mirrorFest (R.earned s y A).landing j i); rw [←p]; exact R.rideM s (plane j i) false x A
lemma lapper (a:Axis)(x:Cover) (v:ℤ):
   let S:Cover:= x+(2*v) • step a
   let T:Cover:=(plane a 0).motion x
   (plane a 0).motion T=x∧(plane a v).motion S=T:=by
 intro S T
 have H(j):T j=if a=j then -x j else x j:=by unfold T; rw[fling_move]; simp
 constructor <;> ext1 j <;> by_cases p:a=j <;> simp [fling_move,H,S,p,eq_comm (a:=j)] <;> try omega -- tune
-- both lifts energy norm comparisons exploit origin-ticks. even-pitch motion in Sharp.F.
lemma axis_ax (A:Waves)(b i:ℤ)(j:Axis): cargoν (plane j b) false (cargoν (plane j i) false A)=A:=by
 let x:Sweep Reifier:= Levier.ray false (plane j i); let y:Sweep Reifier:= Levier.ray false (plane j b)
 change Fren.Mason y (Fren.Mason x A)= A
 -- see pyth
 rw [Fren.lands_t x y A]; unfold Fren.Mason
 rw [show (x*y).s=1 from (by change Signed.mirror j*Signed.mirror j=1; nth_rw 1 [←Signed.mirror_inv j]; exact inv_mul_cancel _)]
 exact Fren.sheen_o A
lemma raw_evenPitch (P:Spine)(s n:ℕ)(j:Axis)(x:Cover)(b:ℤ)(A:Waves):
 Tower.chime P.calibration j b (P.Araw s x n A)= P.Araw s (x+(2*b) • step j) n A:=by
 obtain ⟨h,g⟩:=lapper j x b; unfold Tower.chime; rw [P.rawMirror _ _ _ _ _ _ h,P.rawMirror _ _ _ _ _ _ g,axis_ax]
lemma H_evenPitch (R:P.Heritor)(s:ℕ)(j:Axis)(x:Cover)(b:ℤ)(A:Waves):
 Tower.chime P.calibration j b (R.M s x A).val= (R.M s (x+(2*b) • step j) A).val:=by
 obtain ⟨h,g⟩:=lapper j x b; unfold Tower.chime; rw [HueMirror R _ _ _ _ _ h,HueMirror R _ _ _ _ _ g,axis_ax]
lemma H_seeking (R:P.Heritor)(s:ℕ)(j:Axis)(x:Cover)(b:ℤ)(A:Waves):P.shifts j b (R.M s x A)= R.M s (x+ (ruler P.calibration.B * b)• step j) A:=by
 apply Subtype.ext; change chime P.calibration j _ _=_; rw [H_evenPitch]; congr 4; rw [ruler_offset] -- tune

lemma stepPr (P:Spine)(p:Cover) : (Vacancy.ordinate.map (fun j:Axis=>(ruler P.calibration.B * p j) • (step j:Cover))).sum = ruler P.calibration.B • p:=by
 have h: Vacancy.ordinate.Perm [0,1,2,3]:= by
    unfold Vacancy.ordinate; apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup ..) (by decide)).mpr; intro i; fin_cases i <;> simp
 rw [(h.map (fun j:Axis=>(ruler P.calibration.B * p j) • (step j:Cover))).sum_eq]
 funext i; fin_cases i <;> simp [Vacancy.ordinate] -- ordinal sorted
lemma stampM (R:P.Heritor)(s:ℕ)(x:Cover)(b:Cover)(A:Waves): P.chartAll b (R.M s x A)= R.M s (x + ruler P.calibration.B • b) A:=by
 unfold chartAll; rw [←P.stepPr b]; generalize Vacancy.ordinate=l; induction l with
 | nil=>simp; rfl
 | cons i l ih=> rw [P.cruise_step,AlgHom.comp_apply,ih,H_seeking,List.map_cons,List.sum_cons]; congr 2 <;> abel
#print axioms LiveTurn
#print axioms E_frame
#print axioms stampM
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
