import YM.CF.BProof.Tape.Tool
/-! Path construction goals precisely during Proof B-marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j t:ℕ}{a b l r δ c v η ρ:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N}
variable (D: Front P ρ)(x: D.size≤N.val)(w:0≤δ)(g:δ≤ D.limit)(K:Credit P ρ t)
variable {X:Counter (More N) δ} {B:Skein N v} {S:Support N}
structure Tiles (D:Front P ρ)(X:Counter (More N) δ)(B:Skein N v): Prop where
 fields (i:Bool)(u) (v:u∈walking): ∀ l,SealH (roam B.val (i,false) u l)
 speed (i:Bool)(u)(v:u∈walking): Speed X.val (roam B.val (i,false) u) D.limit
 agree : roam B.val (true,false) 1=roam B.val (false,false) 0
namespace Tiles
variable {D}
def site (p:Tiles D X B) (i:Bool)(u)(v:u∈walking) : HScope N 3:=⟨roam B.val (i,false) u,fun t=> (CStarRing.norm_of_mem_unitary (p.fields i u v t).norm).le.trans (by norm_num)⟩
lemma breeze (F:Core j a b l r N) (p:Tiles D X B)(i:Bool)(u)(v:u∈walking)(r)(h:‖r‖≤1) (e:D.size ≤ N.val) (g:δ≤D.limit) : let P:=F.θ X.val r; let C:=week B.val (i,false) u; ‖P*C-C*cc P‖ ≤ ρ:= D.lip e F _ (⟨X.val,X.property.shrink g⟩) (p.fields i u v) (p.speed i u v) r h
lemma paired (p:Tiles D X B)(i:Bool){t':ℝ}(v:t'∈walking) : week B.val (i,false) t'∈ unitary _:= pair_unit fun j=>(p.fields i t' v j).norm
lemma bent (p:Tiles D X B)(i:Bool){t':ℝ}(v:t'∈walking) : (week B.val (i,false) t')ᵀ= -(week B.val (i,false) t'):= pair_skew _ fun j=>(p.fields i t' v j).symm
end Tiles
structure Lease (D:Front P ρ) (K:Credit P ρ t) (S:Support N)(X:Counter (More N) δ)(B:Skein N v) : Prop extends Tiles D X B where
 side: Shut t 0 S
 close: CloseH X.val K.price S K.reach
 -- u motion of ket projection stage fixed pre B. first-frame agreement near P. second κ-warm case.
 pref(u)(p:u∈walking) : Picture N (toTiles.site true 1 walk1) S K.price ρ u K.reach
 clan(u)(p:u∈walking) : Picture N (toTiles.site false u p) S K.price ρ 0 K.reach
namespace Lease
variable {K:Credit P ρ t} (F:Core j a b l r N)(p:Lease D K S X B)
include p g x w
lemma board_lease : BoardH F X.val S K.c:= K.boardOffer (D.first N x F δ w g).1 X p.side p.close
lemma ride : let y:Shed F δ K.c v:= (⟨(X,S),board_lease D x w g F p⟩, B); dream F δ K.c v K.η y := by
 intro y; let A:=F.θ X.val 1; have he:= D.first N x F δ w g; have hb:=board_lease D x w g F p; have hp:=F.leaning _ X.val he.1.minN he.1.shelter X.property -- tune
 let V:= path y (true,false); let Z:= path y (false,false); let P:=fun (u:Bool)=>bandCut S u; have hx(i:Bool)(u v:ℝ)(p0:u∈walking)(p1:v∈walking): Shelf (F.θ X.val v) (path y (i,false) u) K.η:= plunge (F.θp _ X.val he.1.minN he.1.shelter X.property v) (p.toTiles.paired i p0) (p.toTiles.bent i p0) ((p.toTiles.breeze F i _ p0 v (upt p1) x g).trans K.ηm) K.ηs
 have hC(u:ℝ)(q:u∈walking):Shelf (floorH A (P true) (P false) 0) (Z u) K.η:=by
    refine ⟨hb.fit0.landed,p.toTiles.paired false q,p.toTiles.bent false q,K.screen he.1 X p.side p.close (p.toTiles.site false u q) (p.toTiles.breeze F false u q 1 (by simp) x g) 0 (by simp) (p.clan _ q), K.ηs⟩
 refine ⟨hp,hb, fun u q=>hx true 0 u walk0 q,fun u q=>hx true u 1 q walk1,fun u q=>?_,fun u q=> hC u q,congrArg pair p.agree,⟨hb,cut_real _,cut_real _,pairCom ..,pairCom .., hC 1 walk1⟩,he.2 X⟩
 exact ⟨(hb.houseFit u (upt q)).landed,p.toTiles.paired true walk1,p.toTiles.bent true walk1,K.screen he.1 X p.side p.close (p.toTiles.site true 1 walk1) (p.toTiles.breeze F true 1 walk1 1 (by simp) x g) u (upt q) (p.pref _ q),K.ηs⟩
end Lease
end YM.CF.BProof.Tape
