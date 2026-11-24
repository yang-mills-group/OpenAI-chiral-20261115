import Merino.Corolla.Label

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Cube Stax Fock Rill Mew
open Dial Py Oise Neon Rive QuadClock Paige Roots Vault
open scoped YM.CF.Mew
variable {N B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}
variable {I:Type}[LinearOrder I][Fintype I]


def roseMeter(P:BudgetPoint){g:ℝ}(t:Thimble P g):ℝ:= sigma ((P.B:ℝ)⁻¹+ (P.B:ℝ)⁻¹) P.B*yσE P (till t)
def mothMeter(P:BudgetPoint){g:ℝ}(t:Thimble P g)(m:ℕ):ℝ:= Real.exp (2*(m:ℝ))*yσF P (till t)
def rip(P:BudgetPoint):=P.supportExponent+(1:ℝ)/2

structure Tuning(P:BudgetPoint)(L:ℕ)(h a b v g w:ℝ)(m:ℕ):Prop where
 g0:Girdle P h (accent L*a) (accent L*b) v g m
 levels:18*(m:ℝ) ≤ (P.B:ℝ)
 seeds:nectar P*(accent L*b) ≤ w
 cool:0≤w
 ribbons:roseMeter P g0.toThimble ≤ w
 petals:mothMeter P g0.toThimble m≤ w

local notation "X"=>mid N B


abbrev wovenV(w:ℝ)(m:ℕ):= 2*w*m+w

/-- Outputs of fitting. An exact tipI identity for *any* matching at an Orbit,
plus payment even for simultaneous marks. -/
structure Fit (R:GramM (mid N B))(o:I→Site (mid N B))(s:Side)(w:ℝ)(m:ℕ)
   (y:I→Firing (mid N B))(h:ℝ)
   (D:Key I→RegBudget (mid N B))(K: Key I→ ForceBudget (mid N B)):Prop where
 plans:Notice o D K
 label:∀ i:I, Axon s.val (o i) R.p (νTip D i) h w 0
 lease: ∀ a:Key I, (∀ i, ‖a i‖≤2)→IncX primeU (D a) R.p h (wovenV w m) ∧ Dark primeU (K a) R.p h w
 dry(i:I):brim R.p (node (o i)) (νTip D i)
 earned {L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}
     (U:Grasp Y B e)
     (A:Scree.Loom (mid N B))
     (V:Orbit (mid N B))(dS:IsStarProjection (spar j R.J.M (A V)))
     (l:List I)(v:ψS (node∘o) l)
     (M':I→FC (Tulip.Single (mid N B)))
     (Pq:Rue.FleetS R.p.threshold V.1)
     (pM:l.Pairwise (fun i k=> Commute (M' i) (M' k)))
     (ht:∀ i:I, ∀ T,
      pilotH U R A V dS (acts (y i V) T)=acts (M' i) (pilotH U R A V dS T)):

     tipI (fun z=> denZ
       (color_b R R.beta (R.F + D z) R.slip (R.K + K z) R.v) U A V) l =
      acts (l.map M').prod (denZ R U A V)


variable {o:I→Site (mid N B)}{s:Side}{v w g a b h:ℝ}{m q:ℕ}
def flowerSum {n:Side}(y:I→Bag n): I→Firing n:= fun i=> ∑W:Aura n,y i W

lemma sings (R:GramM X) (y:I→Bag X)
  (U:Grasp Y B e)(A:Scree.Loom X)(V:Orbit X)(dS:IsStarProjection (spar j R.J.M (A V)))
  (T:Wave (Dwell X))(z:Key I)(M':I→FC (Tulip.Single X))
  (hy:∀ i:I,pilotH U R A V dS (acts (flowerSum y i V) T)=acts (M' i) (pilotH U R A V dS T)):
  pilotH U R A V dS (acts (∑W,scores y z V W) T)=
    acts (Liss.waveΦ M' z) (pilotH U R A V dS T):= by
 let H:= pilotH U R A V dS
 have hv {α:Type}[Fintype α][LinearOrder α](c:I→ FC α)(x:Wave α):
       acts (∑j:I,z j • c j) x=∑j:I,z j • acts (c j) x:=by
    let M: FC α→+ Wave α:= ⟨⟨(fun v=>acts v x), act_zero _⟩,fun j k=> act_add ..⟩
    change M _=_
    rw [map_sum]
    exact sum_congr rfl fun _ _=>act_smul ..
 have H1:(∑W,scores y z V W)=∑j,z j • flowerSum y j V:=by
    unfold scores impression flowerSum
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [sum_comm]
    simp only [smul_sum]

 rw [H1,Liss.waveΦ,hv,hv,map_sum]
 simp_rw [map_smul,hy]

variable (R:GramM (mid N B))
variable (f:Tuning R.p s.val h a b v g w m) -- implicit maybe binder


variable (u:Force_M R.p.B (node∘o) m)
    (d: FlagWidth R.p R.K (cipherK q))
    (k: SanB R.K (giftK R.p (rip R.p)) R.p h (fun _=> v))
include f u d k

-- Arbitrary product keys are covered (truncation does not limit the number).
theorem kitOf {y:I→Bag X}{c e:I→Aura X→ℝ}
 (p:Progress R.p q h (node∘o) y c e (accent s.val*a) (accent s.val*b))
 (l:∀i,long R.p s.val (y i))(dry:∀i,sluice R.p (node (o i)) (y i)):
    ∃ D K,Fit R o s w m (flowerSum y) h D K:=by
 obtain ⟨r,T⟩:=hem u f.g0 p d k
 let x:Ids X:=Classical.arbitrary _
 let E:=stems p.toSep x
 have hw:=f.g0.upright
 let C:=till f.g0.toThimble; let M:=scores y; let A:=p.toSep.stripe; let n:=Fintype.card I +1; let σ:=node∘o
 have cE(i:I):Axon s.val (o i) R.p (E i) h w 0:=
   crowned p f.g0.toThimble.support f.g0.levy (zero_le_one.trans hw) i (l i) x f.seeds
 have ht:=displayC C A σ q M T n hw x s o E (fun _=>0) w rfl cE
 let D:= awake σ (lensD (P:=R.p) R.K A n x) E; let F:= bustle σ (lensPort (P:=R.p) R.K A n)
 refine ⟨D,F, ht.1,fun i=> (ht.2 i).1.symm ▸ cE i,fun z a=>?_,fun i=> (ht.2 i).1.symm ▸ hemmed _ i (dry i) x,?_⟩

 · have h0:4 ≤ Real.exp 2:=by
      have e:=(Real.exp_add 1 1)
      rw [show (2:ℝ)=1+1 by norm_num,e]
      nlinarith [Real.exp_one_gt_d9]
   have h1:9*2*(m:ℝ) ≤ C.η*(R.p.B:ℝ)^2:=by
      rw [show C.η*(R.p.B:ℝ)^2 = (R.p.B:ℝ) from by
        change (R.p.B:ℝ)⁻¹*_=_
        field_simp [ne_of_gt (bpos R.p) ]]
      linarith only [f.levels]
   obtain ⟨⟨⟨V,Ve,Vq⟩,Vr⟩,⟨⟨K,Ke,Kq⟩,Kr⟩⟩:=lentEra C A σ q M T n hw x s o E (fun _=>0) w rfl cE
      2 h0 (by norm_num) h1 u f.cool z a
   exact ⟨⟨⟨V,Ve,fun i=>(Vq i).trans (by exact add_le_add le_rfl f.ribbons)⟩,Vr⟩,
     ⟨⟨K,Ke,fun i=>(Kq i).trans f.petals⟩,Kr⟩⟩
 intro L j ho Y e U G V pr l z H M0 t w
 exact rackKey U G V C A σ q M T n hw x pr l z E
    (fun i=>conducts C A σ q M T n hw x i (Nat.succ_pos _) E (shush _ _ _))
      H M0 ((uS_b _ z).length_le_card.trans (Nat.le_succ _)) t fun c _ h=>
      sings R y U G V pr h c H fun i=> w i h

/--
Send in any dictionary at single-root prices with the stated gap rule
on consultations, and receive full-key budgets (including initialized
first-tip Axons and receipts on ALL fresh-seat tips).
-/
theorem fitting (y:I→Bag X)
 (z:2*(postL s.val*R.p.B)<(Cube.More X).val)
 (price:∀i,Barrage R.p q {node (o i)} h (y i) (eighth R.p.B) a b):
    ∃ D K, Fit R o s w m (flowerSum y) h D K:= by
 let V:=fun i=>pseudopod R.p (node (o i)) s.val (y i)
 have v0(i):= extend R.p (node (o i)) s.val (price i)
 have eq:flowerSum V=flowerSum y:=funext fun _=> total ..
 have p(i):Barrage R.p q {node (o i)} h (V i) (eighth R.p.B) (accent s.val*a) (accent s.val*b):=by
   obtain ⟨c,e,t,r,q⟩:=(v0 i).price
   exact ⟨c,e,t,fun x w=>r x fun h=> w ((halo_subset _ _).trans h),q⟩
 rw [←eq]
 obtain ⟨_,_,P⟩:=rooted (σ:=node∘o) p
 exact kitOf R f u d k P (fun i=>markLong _ z (v0 i)) (fun i=>flush _ _ z (v0 i))
end YM.CF.Merino.Corolla
