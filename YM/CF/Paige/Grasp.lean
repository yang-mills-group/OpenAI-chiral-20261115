import YM.CF.Paige.Bound
/-! Choose meshes and block factor uniformly. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Paige
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush Brace
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L:Side}{ho:Odd L.val}{T:Script Male}
structure Grasp (Y:Pricing j L ho T) (B:Side) (e:ℝ) where
  rs : ℕ
  ea : ℕ
  gran : ℕ
  roundZ: ℕ -- RoundZ for input volume min
  b :Side
  K : Side
  chosen: b*K=B
  d:ℝ
  w:ℝ
  a:ℝ -- lambda energy
  positiveB: 0<a
  positiveW:0<w
  p : ℝ
  baseline:ℝ -- slow wide, slow production
  rmin :0<baseline
  sprawls: CoinG j rs gran ea d a w -- oops CoinG j l b_min n; use gran as minimum
  guardV: Guide b e p d
  baseY:Room B e
  capY: enoughV B e baseline
  gem : e ≤ Y.e
  small : baseline≤p
  tender : baseline ≤ Y.e
  believe :billK L.val e baseline < p
  plume : billK L.val e baseline < Y.e
  needed :Y.N≤roundZ
  clock : gran≤roundZ
  period :2*rankS L.val < roundZ
  broadness :∀ (N:Side), roundZ≤N.val→∀ M: Male,Sparkle N e M j
lemma grip (Y:Pricing j L ho T)(hp:1≤j) : ∃ b:Side, ∃ n:ℕ, ∀ B: Side,n≤B.val→(∃ K,b*K=B)→∃ e:ℝ,0<e∧∀ w:ℝ, 0<w→ w≤e → ∃ g: Grasp Y B w,g.b=b:=by
 obtain ⟨l,d,a,t,v,n,pA,k,H⟩:=coin_v j hp
 obtain ⟨N,V⟩:=resolve d H.posT
 let b:Side:= ⟨N+1,Nat.zero_lt_succ _⟩; obtain ⟨q,p,hp',hx⟩:= V b (Nat.le_succ N); -- structure Foil Guide? resolve returns ⟨e,p,h,...⟩
 let δ:=min Y.e p; have hd:0<δ:=lt_min Y.range hx.pPositive
 obtain ⟨u,h,hQ,W⟩:=kip L.val δ hd
 obtain ⟨N',R⟩:= scalable _ h; obtain ⟨x,A⟩:= all_room;
 refine ⟨b,max x N',?_⟩; intro B he' hM; obtain ⟨K,r⟩:=hM
 obtain ⟨c,r',Q⟩:= R B ((le_max_right ..).trans he'); obtain ⟨e,pE,Q'⟩:= A B ((le_max_left ..).trans he')
 obtain ⟨w,pW,v',Wy⟩:= drift_l j hp
 let m:=min (min (min u q) c) (min e w); have hm:0<m:=lt_min (lt_min (lt_min h hp') r') (lt_min pE pW)
 let b':= v+v'+Y.N+(2*rankS L.val)+1
 refine ⟨m,hm,fun M hk h'=>?_⟩ -- shadow k q
 have hg:= h'.trans (min_le_right .. : m≤ min e w); have hl := hg.trans (min_le_right ..); have hx' := h'.trans (min_le_left .. : m≤min (min u q) c)
 have hv:=hx'.trans (min_le_left ..); have hd':= hQ.le.trans (min_le_left .. : δ≤Y.e)
 have hh :billK L.val M u < δ:= (by
   apply lt_of_le_of_lt _ W; unfold billK; gcongr <;> exact hv.trans (min_le_left ..))
 refine ⟨⟨l,n,v,b',b,K,r,d,t,a,pA,k,p,u,h,H,hx.pull hk.le (hv.trans (min_le_right ..)), Q' _ hk.le (hg.trans (min_le_left ..)),Q _ (hx'.trans (min_le_right ..)),(hv.trans (min_le_left ..)).trans hd',hQ.le.trans (min_le_right ..),hd', hh.trans_le (min_le_right ..),hh.trans_le (min_le_left ..),?_,?_,?_, fun N hx M=> (Wy N (le_trans (show v'≤ b' from ?_) hx) M).red hl⟩,rfl⟩ <;> unfold b' <;> omega
variable {e:ℝ}{Y: Pricing j L ho T}{B m: Side}(g: Grasp Y B e)
namespace Grasp
lemma clock_fine {r:Side}(G: Ratio (CSide m B) (CSide r B))(h:g.roundZ ≤ (CSide m B).val):g.roundZ≤ (CSide r B).val:=by rw [G.exact_size]; exact h.trans (Nat.le_mul_of_pos_right _ G.count.property)
def cost(m:Side)(M:Tulip.Male):Duet m B:=tread (m*g.K) g.b j g.rs g.ea M (CSide m B) (knot_coarse g.sprawls g.guardV g.chosen.symm)
lemma couture (l : g.roundZ≤(CSide m B).val)(M) : Cane (CSide m B) j M e g.p (g.cost m M):= CaneV g.sprawls g.guardV _ _ (g.clock.trans l)
lemma topB:enoughV B e g.p:=⟨g.capY.1,g.capY.2.trans_le g.small⟩
-- caps
lemma home (r:Side)(G:Ratio (CSide m B) (CSide r B))(hG:G.count=L)(he:0<e)
    (hq:g.roundZ≤(CSide m B).val) (U:Nom (CSide m B) (CSide r B))(h:JointB G U e)(x:Stun _)(hp:Slow U.2 (hook x) g.baseline): Slow U.1 (hook (ascend G x U.1)) g.p ∧ Gild G (accordL G U x) Y.e:=by
  have hl:=g.period.trans_le (g.clock_fine G hq)
  let N:=CSide r B; have hm: 2*rankS G.count.val <(More N).val:=by rw [hG]; change 2*_ < N.val*2; exact hl.trans_le (by unfold N; omega)
  constructor
  · intro m i; exact lt_of_le_of_lt (marchG G U _ _ h he.le x hp g.rmin m i hm) (by rw [hG]; exact g.believe)
  exact guild G U e _ _ h he g.gem x hp g.rmin g.tender hm (by rw [hG]; exact g.plume)
end Grasp
end YM.CF.Paige
