import YM.CF.BProof.Tape.Trip

/-! B-op licenses. δ and μ angular-speed ceiling bought once for ALL costs on
these arguments meeting trigger/have had choices. For H clan, use a disk test
with center stamp norm≤2; in `VolumeB-marker` the sets are also compact. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η ρ:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N}
-- before D. mesh length bound bought along with speed. smaller d/v work too.
structure Front (P:Ready j a b l r)(ρ:ℝ) where
 size : ℕ
 limit : ℝ
 legal : 0 < limit
 first (n:Side)(g:size ≤ n.val) (F:Core j a b l r n)(d:ℝ)(v:0≤d)(t:d≤limit) : Honor P F d
 lip {N:Side}(q:size≤N.val)(F:Core j a b l r N)(B:Quilt N)(X:Counter (More N) limit)(g:∀ i, SealH (B i))(H:Speed X.val B limit)(u:ℝ)(x:‖u‖≤1): ‖F.θ X.val u*pair B-pair B*cc (F.θ X.val u)‖≤ρ
theorem buyFront (P:Ready j a b l r)(p:1≤j)(x:0<ρ): Nonempty (Front P ρ):=by
 obtain ⟨s,h,e,v,T⟩:= WindShield P p x; exact ⟨v+P.minN,s,h,fun n g f d r a=> ⟨⟨by omega,a.trans e,r⟩,fun X=>(T (by omega) f X.val (X.property.shrink a)).2.1⟩,fun q F B X g H u x=> (T (by omega) F X.val X.property).2.2 B g H u x⟩ -- tune n binder
structure Credit (P:Ready j a b l r)(ρ:ℝ) (t:ℕ) where
 reach:ℕ
 price : ℝ
 pos : 0<price
 c:ℝ
 cE:0<c
 cP: c≤1
 η:ℝ
 ηp:0<η
 ηs:η<1
 ηm:ρ ≤ η
 boardOffer {N:Side}{S: Support N}{d:ℝ}{F:Core j a b l r N} (v:Age P F d)(X:Counter (More N) d)(p:Shut t 0 S)(h:CloseH X.val price S reach): BoardH F X.val S c
 screen {N:Side}{S:Support N}{d:ℝ}{F:Core j a b l r N} (v: Age P F d)(X:Counter (More N) d)(p:Shut t 0 S)(h:CloseH X.val price S reach)(V:HScope N 3)(k:‖F.θ X.val 1*pair V.val - pair V.val * cc (F.θ X.val 1)‖≤ρ) (u:ℝ)(e:‖u‖≤1)(T:Picture N V S price ρ u reach): ‖gapE F X.val S V.val u‖≤η
lemma pledge (X:Streak N){S:Support N}{p q:ℝ}{k l:ℕ}(h:CloseH X p S l)(e:k≤l)(v:p≤q): CloseH X q S k:=fun i t=>(h i (leaks_up (Corona.halo_mono e Subset.rfl) t)).trans v
lemma clear {k:ℕ}(S: Support N)(h:0<c): CloseH 1 c S k:=by intro i t; simpa [scenery] using h.le
lemma buyCredit (P: Ready j a b l r)(p:1≤j)(x:0≤ρ)(g:ρ<1)(t:ℕ)(u:0<t):Nonempty (Credit P ρ t) :=by
 obtain ⟨c,b,hb,k,e,h,W⟩:= holeBuy P p t u; obtain ⟨v,f,j,hF,hM,H,S⟩:= buysP (P:=P) c b x g p; let n:=max k v; let m:= min f e
 have hk {N T d F}(v:Age P F d)(X:Counter (More N) d)(p:Shut t 0 T)(h:CloseH X.val m T n):BoardH F X.val T c :=W F v.minN d v.pos v.shelter X.val T p X.property (pledge X.val h (le_max_left ..) (min_le_right ..))
 refine ⟨n,m,lt_min hF h,c,b,hb,max j ρ,lt_max_of_lt_left H,max_lt hM g,le_max_right ..,@hk,?_⟩; intro N Y d F u X y lV V μ w z Z₀
 let W0:InRoad F d c:= ⟨(X,Y), hk u X y lV⟩; have hu:Picture N V Y f ρ w v:=by
   constructor; intro k l; obtain ⟨M,s,h|⟨q,H⟩⟩:= Z₀.near k l; exact ⟨M,s,.inl fun i p=> (h i (by apply (bay_mem _).mpr; exact (((bay_mem _).mp p).trans (le_max_right ..)))).trans (min_le_left ..)⟩; exact ⟨M,s,.inr ⟨q,fun i p t=> H i p (by apply (bay_mem _).mpr; exact (((bay_mem _).mp t).trans (le_max_right ..)))⟩⟩
 exact (S u (W0,V) (hk u ⟨1,guard0 u.pos⟩ y (clear Y (lt_min hF h))) μ (pledge X.val lV (le_max_right ..) (min_le_left ..)) w z hu).trans (le_max_left ..)
end YM.CF.BProof.Tape
