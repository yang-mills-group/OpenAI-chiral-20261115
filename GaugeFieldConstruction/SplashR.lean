import GaugeFieldConstruction.SluiceR
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
variable {I:Type}[Fintype I][DecidableEq I]{cost:ℕ→P.Test→ℂ}(C: ∀ j:Axis, Porch P cost j)
variable (σ:I→PermWallJ P)(x y:I→Axis→ℝ)(j:Axis)(L:List I)
variable (r B d:ℝ)
abbrev BuntR (r:ℝ)(j:Axis)(L:List I)(x:I→Axis→ℝ) := L.Pairwise (fun i k=>r≤ x k j-x i j)
abbrev HikeR (r:ℝ)(σ:I→PermWallJ P):Prop:=∀ i, StallJ P (σ i) ≤ r
lemma hikeπR (h:BuntR (4*r) j L x)(p:HikeR r σ)(A:I→P.Slabs j)(q:0 < r) : x∈ OpenR j σ L ∧ Cron_R (C j) σ A (2*r) none x L:=by
 let X:=StageR σ (C j) A; let V(i:I):= X.frontend (x i) i; let W(i:I):=X.endline (x i) i
 have he : L.Pairwise (fun i k=> 2*r ≤ V k-W i):=by
    refine (show L.Pairwise _ from h).imp (fun {i k} h'=>?_); change 4*r ≤ _ at h'; let b:=StallJ P (σ i); let c:=StallJ P (σ k); change 2*r≤ x k j-c-(x i j-b+(b+b)); linarith only [h',show b≤r from p i,show c≤ r from p k]
 refine ⟨?_,?_⟩
 · refine he.imp (fun {i k} u=>?_); let b:=StallJ P (σ i); change 2*r≤ x k j-StallJ P (σ k)-(x i j-b+(b+b)) at u; change x i j+b<x k j-_; linarith
 suffices hv: ∀ (l:List I), l.Pairwise (fun i k=>2*r≤V k-W i)→∀ a:Option ℝ,(∀ i∈ l,∀ y:ℝ,a=some y→2*r≤ V i-y)→ Cron_R (C j) σ A (2*r) a x l by exact hv L he none (fun _ _ _ t=>nomatch t) -- lambda
 intro l H a k; induction l generalizing a with
 | nil=> trivial
 | cons i l ih=> rw [List.pairwise_cons] at H; exact ⟨fun y v=>k _ (List.mem_cons_self ..) y v,ih H.2 _ (fun u g y w=>(Option.some.inj w) ▸ H.1 u g)⟩
lemma SmoothJigR (S:I→ScreensJ P)(A:∀ i,AttainedR 0 (S i))(h:BuntR (4*r) j L x)(e:BuntR (4*r) j L y)(u:PolesR L)(p:HikeR r σ)(hB:∀ i,‖S i j (σ i) (σ i)‖≤ B) (v:∀ i,|x i j-y i j|≤d)(q:0<r)(g:0≤ d) (s:∀ i k,k≠j→ x i k=y i k)(F:0≤B) : ‖SπR C S x-SπR C S y‖ ≤ Fintype.card I*(r⁻¹*(2*d))* B^Fintype.card I:=by
 let T:= BodyΘ P S j σ
 obtain ⟨a,w⟩:=hikeπR C σ x j L r h p T q; obtain ⟨a',w'⟩:= hikeπR C σ y j L r e p T q
 rw [ηTenderR C L S A j σ _ u a, ηTenderR C L S A j σ _ u a', ←(show L.length=Fintype.card I from ?_)]; exact CronΨR (C j) σ T x y L r B d hB F q g v s w w' -- tune implicit
 · rw [← List.toFinset_card_of_nodup u.1,show L.toFinset=univ from ?_,card_univ]; ext i; simp [u.2 i] -- card elaboration cast
lemma BuntPatchR (v:BuntR (6*r) j L x)(q:∀ i, |x i j-y i j|≤r): BuntR (4*r) j L y:=by
 refine (show L.Pairwise _ from v).imp (fun {i k} h=>?_); have ha:= (abs_le.mp (q i)).1; have hp:=(abs_le.mp (q k)).2; linarith
-- across transitions through hands.Bands. if y and all intermediate.points agree measures moves.IR
private def RectR (x y:I→Axis→ℝ)(l:List Axis) (i:I)(j:Axis):ℝ:= if j∈ l then y i j else x i j
lemma AllJigR (S:I→ScreensJ P)(A:∀ i,AttainedR 0 (S i))(L:Axis→List I) (h:∀ j:Axis, BuntR (6*r) j (L j) x)(u:∀ j:Axis,PolesR (L j))(p:HikeR r σ)(hB:∀ i j,‖S i j (σ i) (σ i)‖≤ B)(v:∀ i j, |x i j-y i j|≤ d)(q:0<r)(g:0≤d)(e:d≤r)(F:0≤B) : ‖SπR C S x-SπR C S y‖ ≤ 4*(Fintype.card I*(r⁻¹*(2*d))* B^Fintype.card I):=by
 let D(l:List Axis):= RectR x y l
 let V:= Fintype.card I*(r⁻¹*(2*d))*B^Fintype.card I
 let f:= SπR C S
 have h'(l:List Axis)(i:Axis) : BuntR (4*r) i (L i) (D l):=by
    apply BuntPatchR x (D l) i (L i) r (h i); intro k; unfold D RectR; split; exact (v ..).trans e; simp [q.le]
 have he(l:List Axis):‖f x-f (D l)‖≤ l.length*V:=by
   induction l with
   | nil=> rw [show D []=x from (by funext i j; simp [D,RectR])]; simp
   | cons i l ih=>
     let w:=D l; let w':= D (i::l); have ha: ∀ j,w' j i=y j i:=fun j=>if_pos (List.mem_cons_self ..)
     have hv: ‖f w-f w'‖≤V:=by
       refine SmoothJigR C σ w w' i (L i) r B d S A (h' ..) (h' ..) (u i) p (fun j=>hB j i) ?_ q g ?_ F
       · intro j; rw[ha]; unfold w D RectR; split; simp [g]; exact v ..
       intro a b p; simp only [w,w',D,RectR,List.mem_cons,p,false_or]
     rw[List.length_cons, Nat.cast_add,Nat.cast_one,add_mul,one_mul]; exact (norm_sub_le_norm_sub_add_norm_sub (f x) (f w) (f w')).trans (add_le_add ih hv) -- tune
 let l:List Axis:= [0,1,2,3]; have ht: D l=y:=by funext i j; refine if_pos ?_; fin_cases j <;> decide
 have h:= he l; rw [ht,show l.length=4 by rfl,Nat.cast_ofNat] at h; exact h
#print axioms AllJigR
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
