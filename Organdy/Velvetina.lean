import Organdy.Corrugate
import Organdy.Treasury
import Organdy.Opal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


namespace Royal
open Larva Buffered.Afterglow Satin Lifted

abbrev haloMark {N:Side}(K:Scree.Loom N)(p:BudgetPoint)(X:SOp N):Mark N:=
 fun V=>scint K p X V.1 • 1
abbrev mortise (B:ℕ):=Lattice.box (4*B+6)

/- The H raw price. Purity relation uses scalar on first Pane of Pairs. -/
section
variable {N:Side}{K:Scree.Loom N}{p:BudgetPoint}{X:SOp N}{B:ℕ}

lemma rayon_price
 {r τ η D:ℝ}{A:Ink _} (h:Domaine (B+6) r τ η D (scint K p X) A):
 AtSupport false (Satin.region (mortise B) N) (haloMark K p X) ∧
 covariant (haloMark K p X):=by
 have hk:halo (B+6) {(0:Seat N)} ⊆ Satin.region (mortise B) N:=by
    rintro i c
    obtain ⟨x,b,q⟩:=halo_spec.mp c; rw [mem_singleton.mp b] at q
    have a:separation (0:Seat N) i ≤ 4*B+6:=q.trans (by omega)
    exact mem_image.mpr ⟨_,Work.E08.lift_mem_box a,(wrap_lift _).trans (sub_zero _)⟩
 refine ⟨⟨Girt.pole_w (fun x:Fields N=>scint K p X x.1) (fun v:ℂ=>v • _) (continuous_id.smul continuous_const)
     ⟨h.meas.comp measurable_fst,_,fun _=> h.uniform _⟩, ?_,fun _=>Reed.Fine.one.scale _⟩,?_⟩

 · intro V W e g; exact congrArg (fun v:ℂ=>v • (1:FC (Single N))) (h.loc _ _ (agrees_mono e hk))
 intro V u; simp only [simultaneous,haloMark, twist_scalar,map_one, Prod.map,h.move]

lemma porch_on(u:p.B=B): Porch p (0:Site N) ⊆ Satin.region (mortise B) N:=by
 let n:=node (0:Site N)
 have a:n=wrap _ (1:Cover):=by
    have b:=node_of (N:=N) (0:Cover)
    rw [map_zero,show nodeC (0:Cover)=1 from by simp [nodeC]] at b; exact b
 intro i h; obtain ⟨x,b,q⟩:=halo_spec.mp h
 have t:separation n i ≤2*B:=by rw [mem_singleton.mp b,u] at q;exact q
 have k:=box_test.mp (Work.E08.lift_mem_box t)
 refine mem_image.mpr ⟨Lattice.lift (i-n)+1,box_test.mpr ?_,?_⟩
 · constructor
   · intro j; simp only [Pi.add_apply,Pi.one_apply]; have b:=k.1 j;omega
   intro j; simp only [Pi.add_apply,Pi.one_apply]; have b:=k.2 j;omega
 rw [map_add, wrap_lift,←a, sub_add_cancel]
end

section
variable {I:Type*} {N:I→Side}{p:I→BudgetPoint}{B q:ℕ}
 {K:(i:I)→Scree.Loom (N i)} {X:(i:I)→SOp (N i)}
 {a b d τ:ℝ}
local notation "n₀" => (fun i:I=>node (0:Site (N i)))
variable (S:Finset Cover) (u:Ruffles a b d τ B p K (fun i=>node 0) X)(h:∀ i,StageSet (K i) (p i) d)
local notation "G" i:max x:max=>graft S (N i) ((x : PairsC).1)
lemma starMask {F:I→PairsC→ℂ} (v:Menu F)(s:Bool):
 Menu (fun i x=>cSignX s (F i x)):=by
 cases s; exact v
 obtain ⟨c,z,t⟩:=v.budget
 refine ⟨v.deal.along (T:=fun i=> ℂ) (U:=fun i=>ℂ) (fun _=>cSignX true) ?_, c,z,
   fun i x=>by simpa [cSignX] using t i x⟩ -- goal norm, simpa? simpa also goal simp
 intro e f; exact ⟨e,f,fun i x y h=>by simpa [cSignX,dist_eq_norm,←map_sub] using h⟩
include u h
lemma beading (s:Signed):
 Menu (fun i x=>rayon s (K i) (p i) (X i) (G i x)):=by
 let z: Ruffles a (Tenant.quota^2*b) d τ B p K (fun i=> restL (N i) s)
       (fun i=> julStep (polestar (N i) s) (X i)) :=

    ⟨u.chest,mul_nonneg (sq_nonneg _) u.glow,u.depth,u.measure,u.hazard,u.paid,fun i=>jul_trunk _ (u.trunk i)⟩
 let y:= traceMenu S z
 let c:=ebony s
 refine (Menu.mul (T:=fun i=>ℂ) (Menu.cnst (I:=I) (fun _=>c) (norm_nonneg c) (fun _=>le_refl _)) (starMask y (detX s))).congr ?_
 intro i x
 have b:=congrFun (cassette_reads (h i) (u.trunk i) u.chest (polestar _ s)) (G i x)
 change c*cassette (polestar (N i) s) (K i) (p i) (node 0) (X i) (G i x)=rayon s (K i) (p i) (X i) (G i x)
 rw [b];rfl

lemma pigment:
 Menu (T:=fun i=>FC (Single (N i))) (fun i x=> haloMark (K i) (p i) (X i) (replant S _ x)):=by
 let c:ℂ:=(Fintype.card Signed:ℂ)⁻¹
 have t:Menu (fun i x=>scint (K i) (p i) (X i) (G i x)):=by
    refine (Menu.mul (T:=fun _=> ℂ) (Menu.cnst (I:=I) (fun _=>c) (norm_nonneg c) fun _=>le_refl _)
     (Menu.total univ (fun s i x=>rayon s (K i) (p i) (X i) (G i x)) (fun s _=>beading S u h s))).congr ?_

    intro i x; rw [scint,honeycomb,Finset.sum_apply]
 exact t.scale (Menu.cnst (T:=fun i=>FC (Single (N i))) (fun _=>1)
   (by norm_num: (0:ℝ)≤1) (fun _=>norm_one.le))
end

inductive Pin where
| stone | horn
| axis (d:Axis)
| plus (d:Axis)
| minus (d:Axis)
open Pin

def tooled {N:Side}(K:Scree.Loom N)(p:BudgetPoint)(X:SOp N)(J:Axis→SOp N)
 (m:ℕ):Pin → Mark N
 | .stone=>Zc K p 0 X
 | .horn => haloMark K p X
 | .axis i=> Jc K p 0 (J i)
 | .plus i=> Jd K p 0 (0+gapPlus i m) (J i)
 | .minus i=> Jd K p 0 (0-gapPlus i m) (J i)

section
variable {I:Type*} {N:I→Side}
-- all on a common index. 
structure Bezel (a b d τ:ℝ)(B m:ℕ)
 (p:I→BudgetPoint)
 (K:(i:I)→Scree.Loom (N i)) (X:(i:I)→SOp (N i)) (J:(i:I)→Axis→ SOp (N i)):Prop where
 paid: Ruffles a b d τ B p K (fun i=> node 0) X
 density(i:I):StageSet (K i) (p i) d
 axes(i:I)(j:Axis):Trunk (node 0) (J i j) ((p i).B/10) a b d
 aura(i:I):∃ r τ η D A, Domaine (B+6) r τ η D (scint (K i) (p i) (X i)) A
 width:24*m+4≤B

variable {a b d τ:ℝ}{B m:ℕ}
 {p:I→BudgetPoint}
 {K:(i:I)→Scree.Loom (N i)}{X:(i:I)→SOp (N i)}{J:(i:I)→Axis→ SOp (N i)}
 (u:Bezel a b d τ B m p K X J)
local notation "R" j:max i:max=>tooled (K i) (p i) (X i) (J i) m j
include u
lemma frameP(j)(i:I):
 AtSupport false (Satin.region (mortise B) (N i)) (R j i) ∧ (Lily (R j i) ∧ covariant (R j i)):=by
 have b:=u.paid; have g:=b.paid i

 have c:=b.chest
 have x:24*m+4≤(p i).B:= (b.measure i).symm ▸ u.width
 have t:separation (0:Site (N i)) 0 ≤ m:=by rw [separation_self]; omega
 have h:= porch_on (N:=N i) (b.measure i)
 cases j with
 | stone =>
    have v:=standZ g c (b.trunk i)
    exact ⟨v.realc.mono ((fitsPorch x t).trans h),v.first,v.color⟩
 | axis d=>
    have v:=standJ g c (u.axes i d)
    exact ⟨v.realc.mono ((fitsPorch x t).trans h),v.first,v.color⟩
 | plus d=>
    have v:=standJd g c x (stopBeam _ d m).1 (u.axes i d)
    exact ⟨v.realc.mono h,v.first,v.color⟩
 | minus d=>
    have v:=standJd g c x (stopBeam _ d m).2 (u.axes i d)
    exact ⟨v.realc.mono h,v.first,v.color⟩
 | horn=>
    obtain ⟨r,q,η,D,A,v⟩:=u.aura i
    exact ⟨(rayon_price v).1,fun _ _ _=>rfl,(rayon_price v).2⟩

lemma tiled(j):
 Menu (T:=fun i=>FC (Single (N i))) (fun i x=> (R j i) (replant (mortise B) _ x)):=by
 let S:=mortise B
 let y:=u.paid
 have v(j:Axis)(o:(i:I)→Site (N i)):
       Ruffles a (Tenant.quota^2*b) d τ B p K (fun i=>node (o i)) (fun i=>co_Ψ (o i) 0 (J i j)):=
    ⟨y.chest,mul_nonneg (sq_nonneg _) y.glow,y.depth,y.measure,y.hazard,y.paid,fun i=>co_trunk _ _ (u.axes i j)⟩
 cases j with
 | stone =>
    simp only [tooled,Zc,clef,replant]
    have h:=Menu.scale (traceMenu (mortise B) u.paid)
          (Menu.cnst (T:=fun i=>FC (Single (N i))) (fun _=>1) (by norm_num: (0:ℝ)≤1) (fun _=>norm_one.le))
    exact h
 | axis j =>
    have v:Ruffles a b d τ B p K (fun i=> node 0) (fun i=>J i j):=
      ⟨y.chest,y.glow,y.depth,y.measure,y.hazard,y.paid,fun i=>u.axes i j⟩
    exact harpMenu S v
 | horn=> exact pigment S u.paid u.density
 | plus j => exact harpMenu S (v j fun _=>0+gapPlus j m)
 | minus j=> exact harpMenu S (v j fun _=>0-gapPlus j m)

variable {C:Calibration}
lemma fundedPins(n:I→Side)
 (l:Ultrafilter I)
 (t:(i:I)→Tower.Tivoli (mortise B) (N i))(e:∀ i,C.c (n i)=N i):
 ∃ (F:Pin→I→Buffered.Family C)(x:Pin→Buffered.Family C), 
 (∀ j,Bolt (l:Filter I) (mortise B) n e (fun i=>R j i) (F j) (x j) ∧ (∀ i,Plumage (F j i)) ∧ Plumage (x j))∧
 ∀ j:Pin,j=.stone∨j=.horn → (∀ i,Cello (mortise B) (F j i)) ∧ Cello (mortise B) (x j):=by
 let g j i:=frameP u j i
 choose F x b using fun j=>rollcall l n e t (Y:=fun i=>R j i) (fun i=>(g j i).1) (tiled u j)
 refine ⟨F,x,fun j=>⟨b j,(b j).quality t (fun i=>(g j i).2)⟩,fun j h=>(b j).cello t (fun i=>(g j i).2) ?_⟩
 intro i; rcases h with rfl|rfl <;> exact fun _=>⟨_,rfl⟩
end

section addenda
variable {K:Calibration}{I:Type*}{N:I→Side} {l:Filter I}
 {n:I→Side}{S:Finset Cover}
 {p:I→BudgetPoint}
 {T:(i:I)→Scree.Loom (N i)}{X:(i:I)→SOp (N i)}{J:(i:I)→Axis→ SOp (N i)}
 {m:ℕ}{e:∀i,K.c (n i)=N i}
 {F:Pin→ I→Buffered.Family K}{u:Pin→Buffered.Family K}
def yFin (g:Pin→Buffered.Family K):= g .stone + ∑ i:Axis,(g (.plus i)-g (.minus i))
def yStart (g:Pin→ I→Buffered.Family K):= fun i=>yFin (fun j=>g j i)

lemma netted
 (p0:∀ j,Bolt l S n e (fun i=>tooled (T i) (p i) (X i) (J i) m j) (F j) (u j)):
 Bolt l S n e (fun i=>Yc (T i) (p i) 0 (J i) (X i) m) (yStart F) (yFin u):=
 (p0 .stone).add (Bolt.sum Finset.univ
   (fun d i=>tooled (T i) (p i) (X i) (J i) m (.plus d)-tooled (T i) (p i) (X i) (J i) m (.minus d))
   (fun d=>F (.plus d)-F (.minus d)) (fun d=>u (.plus d)-u (.minus d))
   fun d=>(p0 (.plus d)).sub (p0 (.minus d)))
end addenda
#print axioms netted
#print axioms fundedPins
