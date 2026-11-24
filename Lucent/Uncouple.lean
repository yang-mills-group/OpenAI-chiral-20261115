import Lucent.Carve
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Stationary (Gaia)
open Ballad.Twah SpinReceipt Emu Gist
open Regis Circuit
variable {I J K:Type}

def splitV (Q:Votive I)(E:Votive J):Votive (I⊕J):=
 { S:=fun (x,t) (y,z)=> match x,y with| .inl i,.inl j=>Q.S (i,t) (j,z)| .inr i,.inr j=>E.S (i,t) (j,z)|_,_=>0
   G:=fun (x,t) (y,z)=> match x,y with| .inl i,.inl j=>Q.G (i,t) (j,z)| .inr i,.inr j=> E.G (i,t) (j,z)|_,_=>0 }

lemma mergeQuotes (Q:Votive I)(E:Votive J)(S:Stencil I)(T:Stencil J): (splitV Q E).quoted ((S.remake Sum.inl)*(T.remake Sum.inr))=Q.quoted S*E.quoted T:=parts_done ⟨fun _ _=>rfl,fun _ _=>rfl⟩ ⟨fun _ _=>rfl,fun _ _=>rfl⟩ ⟨fun _ _=>rfl,fun _ _=>rfl⟩ S T

structure Cross (q:ℕ→Votive K)(f:I→K)(g:J→K):Prop where
 down(i j):Tendsto (fun n=> (q n).G (rebill f i) (rebill g j)) atTop (𝓝 0)
 up(i j): Tendsto (fun n=> (q n).S (rebill f i) (rebill g j)) atTop (𝓝 0)
lemma ptr {x y:ℕ→ℂ}{b:ℂ}(h:Tendsto y atTop (𝓝 b))(p:∀ n,x n=y n): Tendsto x atTop (𝓝 b) := h.congr fun n=>(p n).symm

lemma crossSplit {E: Votive I}{F: Votive J}{Q:ℕ→Votive (I⊕J)}
   (g:∀ n,(Q n).part E Sum.inl)(t:∀ n,(Q n).part F Sum.inr)
   (p:Cross Q Sum.inl Sum.inr)(u:Cross Q Sum.inr Sum.inl): Vow Q (splitV E F):=by
 constructor <;> rintro ⟨i|i,a⟩ ⟨j|j,b⟩
 · exact ptr (tendsto_const_nhds (x:=E.S (i,a) (j,b))) (fun n=> (g n).sameSpin (i,a) (j,b))
 · exact p.up (i,a) (j,b)
 · exact u.up (i,a) (j,b)
 · exact ptr (tendsto_const_nhds (x:=F.S (i,a) (j,b))) (fun n=>(t n).sameSpin (i,a) (j,b))
 · exact ptr (tendsto_const_nhds (x:=E.G (i,a) (j,b))) (fun n=>(g n).sameGauge (i,a) (j,b))
 · exact p.down (i,a) (j,b)
 · exact u.down (i,a) (j,b)
 · exact ptr (tendsto_const_nhds (x:=F.G (i,a) (j,b))) (fun n=>(t n).sameGauge (i,a) (j,b))

structure Tied (u:FieldPlan K)(a:FieldPlan I)(f:I→K): Prop where
    g(i): (u.hands (f i)).shade=(a.hands i).shade
    v(i): (u.roles (f i)).voice=(a.roles i).voice

structure SameChalk (u:FieldPlan K)(a: FieldPlan I)(f:I→K): Prop extends Tied u a f where
    static(i j):(u.hands (f i)).p-(u.hands (f j)).p=(a.hands i).p-(a.hands j).p
    warm(i j):(u.roles (f i)).pt-(u.roles (f j)).pt=(a.roles i).pt-(a.roles j).pt
variable {u:FieldPlan K}{a:FieldPlan I}{f:I→K}

lemma tiedP (h:Tied u a f)(x: Stamp I) :
     pilotS (upstairs u.roles) (rebill f x)=pilotS (upstairs a.roles) x:= by
   unfold pilotS; rw [show (rebill f x).1=f x.1 from rfl]; rw [show upstairs u.roles _= _ from h.v x.1]; rfl

lemma SameChalk.gives (h:SameChalk u a f) : u.aura.part a.aura f:=by
 constructor <;> intro i j
 · unfold FieldPlan.aura; dsimp; unfold fair; dsimp only [rebill,Prod.map]; rw [h.g i.1,h.g j.1,h.static i.1 j.1]; try rfl
 · unfold FieldPlan.aura; dsimp; unfold germRho
   rw [tiedP h.toTied i,tiedP h.toTied j,show outside u.roles (colbase (rebill f i))-outside u.roles (colbase (rebill f j))=outside a.roles (colbase i)-outside a.roles (colbase j) from h.warm i.1 j.1]

#check @FieldPlan.aura

structure FieldsApart (U:ℕ→FieldPlan K) (f:I→K)(g:J→K):Prop where
   apartG(i j): Tendsto (fun n=>dist ((U n).hands (f i)).p ((U n).hands (g j)).p) atTop atTop
   apartS(i j): Tendsto (fun n=>dist ((U n).roles (f i)).pt ((U n).roles (g j)).pt) atTop atTop
variable {U:ℕ→FieldPlan K}{g:J→K}
lemma FieldsApart.symmetric (h: FieldsApart U f g): FieldsApart U g f:=⟨fun i j=>(h.apartG j i).congr fun _=>dist_comm ..,fun i j=>(h.apartS j i).congr fun _=>dist_comm ..⟩

lemma FieldsApart.cut {b: FieldPlan J}(h:FieldsApart U f g)
    (t:∀ n,Tied (U n) a f) (w:∀ n,Tied (U n) b g):
   Cross (FieldPlan.aura ∘ U) f g:=by
 constructor <;> intro i j
 · have hz:=dies (specter (a.hands i.1).shade (b.hands j.1).shade) 4 (by decide) (mindful _ _)
            (fun _ h=>ticketEra _ _ h) ((h.apartG i.1 j.1).congr fun _=>dist_eq_norm ..)
   let q:ℂ:= Head.Brecht.sch (G:=SU.group) i.2 j.2
   have hu:= hz.const_mul q; rw [mul_zero] at hu
   exact hu.congr (fun n=> by dsimp [FieldPlan.aura]; unfold fair; dsimp only [rebill,Prod.map]; rw [(t n).g i.1,(w n).g j.1]; rfl)
 -- spin branch

 · let x(n):=((U n).roles (f i.1)).pt-((U n).roles (g j.1)).pt
   let Y:= pilotS (upstairs a.roles) i; let Z:= pilotS (upstairs b.roles) j
   have v:Tendsto (fun n=> ‖x n‖) atTop atTop:= (h.apartS i.1 j.1).congr fun n=> dist_eq_norm ..
   have eq(n): ((FieldPlan.aura ∘ U) n).S (rebill f i) (rebill g j)= if signW Y=signW Z then 0 else if signW Y then frank Y Z (x n) else -frank Z Y (-x n):=by
       dsimp only [FieldPlan.aura, Function.comp_apply]; unfold germRho; rw [tiedP (t n),tiedP (w n)]; try rfl
   simp_rw [eq]; split; · exact tendsto_const_nhds
   split; · exact fade v Y Z
   have he:Tendsto (fun n=>‖-(x n)‖) atTop atTop:=v.congr fun n=> (norm_neg _).symm
   simpa using (fade he Z Y).neg
#check @specter
#print fair

section
variable (P:Preparation)[Fintype I](d:FieldPlan I)(n:ℕ)
lemma lanesOnly : (lane P n d).aura =d.aura:= by
 have h:SameChalk (lane P n d) d id:= ⟨⟨fun _=>rfl, fun _=>rfl⟩,fun _ _=> Shuttle.gait_d ..,fun _ _=> Shuttle.gait_d ..⟩
 exact Votive.partial h.gives
lemma oppositeOnly : (legato P n d).aura=(opp d).aura:= by
 have hz(x y:Gaia): shade P x n-shade P y n=Shuttle.opposite x-Shuttle.opposite y:=by unfold shade leg; rw [Shuttle.flip_d,Shuttle.flip_d x,Shuttle.gait_d]
 have h:SameChalk (legato P n d) (opp d) id:= ⟨⟨fun _=>rfl,fun _=>rfl⟩,fun _ _=>hz ..,fun _ _=>hz ..⟩
 exact Votive.partial h.gives
lemma firsts(j k:FieldPlan I) : SameChalk (league j k) j Sum.inl ∧ SameChalk (league j k) k Sum.inr:= ⟨⟨⟨fun _=>rfl,fun _=>rfl⟩,fun _ _=>rfl,fun _ _=>rfl⟩,⟨⟨fun _=>rfl,fun _=>rfl⟩,fun _ _=>rfl,fun _ _=>rfl⟩⟩

lemma wispCross : Vow (fun n=>(trio P n d).aura) (splitV (opp d).aura d.aura):= by
 have e:FieldsApart (fun n=>trio P n d) Sum.inl Sum.inr:= ⟨fun _ _=> Shuttle.foreign ..,fun _ _=>Shuttle.foreign ..⟩
 have t:∀ n,Tied (trio P n d) (opp d) Sum.inl:=fun n=> ⟨fun _=>rfl,fun _=>rfl⟩
 have u:∀ n,Tied (trio P n d) d Sum.inr:=fun n=> ⟨fun _=>rfl,fun _=>rfl⟩
 apply crossSplit _ _ (e.cut t u) (e.symmetric.cut u t)
 · intro n; rw [←oppositeOnly P d n]; exact (firsts ..).1.gives -- ..
 intro n; have v:=(firsts (legato P n d) (lane P n d)).2.gives; rwa [lanesOnly] at v -- rw dependent?
lemma wispFinal(S:Stencil I): Tendsto (fun n=>faq (trio P n d) (night S)-faq (legato P n d) (dusk S)*faq (lane P n d) (dawn S)) atTop (𝓝 0):=by
 simp_rw [faq_call,lanesOnly,oppositeOnly]
 have h:= (wispCross P d).quotes (night S)
 rw [show (splitV (opp d).aura d.aura).quoted (night S)=_ from mergeQuotes _ _ (dusk S) (dawn S)] at h
 simpa using h.sub (tendsto_const_nhds (x:=(opp d).aura.quoted (dusk S)*d.aura.quoted (dawn S)))
end
