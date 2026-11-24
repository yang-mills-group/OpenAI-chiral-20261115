import YM.CF.BProof.Trek.Poles
import YM.CF.BProof.Tape.Contour
import YM.CF.BProof.Tape.Shelf
/-! Lease on comparison pair and aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Tape Hearth Wick Stint
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
structure Disk (ρ:ℝ) where
 model : Fin 5→Stamp
 v : ℝ
 p:0<v
 up : v < ρ
 lid : ρ<1
 works (i:Fin 5): tightLoop model v i
lemma wish : ∃ ρ,Nonempty (Disk ρ):=by obtain ⟨M,r,h,v,W⟩:= radC; obtain ⟨p,a,b⟩:= exists_between v; exact ⟨p,⟨M,r,h,a,b,W⟩⟩
variable {s c a:Side}{Y:Yard (More s)}{D:Script Y}{u v d:ℝ}{H:Herald u v}{t:ℕ}{C:Sized t H.whole}{g: Ratio c (More s)}{B:Blocks Y c}{F:Bkg (More s)}{f:Ratio a (More s)} {j:ℕ} {a' b l r:ℝ}{P: Ready j a' b l r}
namespace Permit
variable {U:Bkg (More s)}{δ:ℝ}(L: Pad Y H C g.count.val)(p:Permit D C U g B d)(T:4≤a.val)(W:f.count=H.whole) (e:Lamp C g B δ U F)(S:Sound Y H C d)
variable {ρ:ℝ}
include L p T W e S
private lemma funds (x:Site (More s)): Money (D.HH C g B F f x):= (p.HPort D C g B F f L T W e S x).1 -- must include all
-- expose hh premise via giving Q instead
lemma LeaseP (Q:Skein s rateH)(pQ:∀ i u,u∈walking→ roam Q.val (i,false) u=fun x=> D.HH C g B F f x (Tape.T i u)) (K: Credit P ρ Y.short)(J:Disk ρ)(q:Tape.Front P ρ)(qH: 2*v ≤ q.limit) (c₁:2*xm*d≤K.price)(c₂:2*xm*d+J.v≤ρ)(ht:2*Y.short≤Y.long)(u:K.reach≤t): Lease q K (Pins Y g B) (⟨F,e.year⟩:Counter (More s) δ) Q := by
 let t₀(X:ℝ)(z:Site (More s)):=D.HH C g B F f z X
 have hf(i:Bool)(u:ℝ)(t:u∈walking):roam Q.val (i,false) u=t₀ (Tape.T i u):=pQ i u t; have hh: Tiles q (⟨F,e.year⟩:Counter (More s) δ) Q:=by
    refine ⟨fun i u v x=>?_,fun i u v=>?_,?_⟩; rw [pQ i u v]; exact funds L p T W e S _|>.1 _; rw [pQ i u v]; exact fun x j=> ((p.speedH D C g B F f L T W e S (Tape.T i u) (T_b i _ v)) x j trivial trivial).trans qH; rw [hf true _ walk1,hf false _ walk0,Tape.T,Tape.T]; simp
 refine ⟨hh,vacancy Y g B ht,p.halo_pay L T W e S u ?_,fun w l=>?_,fun w l=>?_⟩
 · have hp:= mul_nonneg xm_p.le S.fields.le; linarith
 · apply p.view1 L T W e S u c₁; exact pQ _ _ walk1
 exact p.priced L T W e S u J.model J.works (J.up.trans J.lid) c₂ K.price (Tape.T false w) (by change 1 ≤ 1+w; linarith [l.1]) (Tiles.site hh false w l) (pQ false w l) -- tune named
lemma readyStory (Q:Skein s rateH) (h: Q=drawB (D.HH C g B F f) (fun i=>(p.HPort D C g B F f L T W e S i).1)) : let m:= Q.val; Story (week m (true,false)) (week m (false,false)) (week m (true,true)) (week m (false,true))∧
   week m (true,false) 0=postC (D.XX C g B F f) ∧ Slow F (hook (D.XX C g B F f)) u ∧ (roam m (false,false) 1=fun x=> D.HH C g B F f x 2):=by
 subst Q; let s:=fun i=> (p.HPort D C g B F f L T W e S i).1; let A:=drawB _ s; intro m; refine ⟨ Tape.story _ s,?_ ,Hero.pace_slow (p.liftF D C g B F f L T W e S) H.y_small,?_⟩
 · unfold week; rw [show roam m (true,false) 0= _ from pretty _ s true 0 walk0]; -- tune eta
   rw [show (fun x=> D.HH C g B F f x (Tape.T true 0))=StampX _ (D.XX C g B F f) from ?_,pair_post]; ext1 x; exact (p.HPort D C g B F f L T W e S x).2
 rw [show roam m (false,false) 1= _ from pretty _ s false 1 walk1,Tape.T]; norm_num -- tune rw lambda
end Permit
end YM.CF.BProof.Trek
