import YM.CF.DPress.FD.Stock.Seed
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory Cube SU Lat Finset
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{I:Type}[Fintype I]{r d:ℕ}{u t:ℝ}
namespace Spoke
variable (X:Scout I n u t r) (f:ℕ→ℝ→I)
abbrev bonnet (c:Support (More n))(τ: Ids n): Bone n:= τ (greet c (priorP τ))
local notation "W"=>Support (More n)
def well (F:W)(U:Pane n)(i:reach n)(τ: Ids n):E:= if F.Nonempty then let v:=bonnet F τ; mend (X.X (f F.card v.1)) v.2.1 U i else U i
def glow (d:ℕ)(x:Orbit n):Pane n:= fun i=>well X f (soup (RG.flags u x.1) d i) x.1 i x.2
def ray (d:ℕ)(x:Orbit n):Pane n:= gauge (frameP x.2)⁻¹ (glow X f d (gauge (frameP x.2) x.1,x.2))
lemma bonnetB (s:Sweep n)(U: Ids n)(M: Support (More n))(k:ℕ)(i:reach n)(v:(soup M k i).Nonempty)(p:Injective (priorP U)): bonnet (Tw.ζ s⁻¹ (soup M k i)) (bun s U)= man s (bonnet (soup M k i) U):=by unfold bonnet bun; change man s (U (boxA s (greet _ (priorP (bun s U)))))=_; rw [Tw.ζ,sitU,mast_rev M s k i U v p] -- tune
lemma bonnetT (S:W)(g:Seat n →E)(X: Ids n): (bonnet S (threadG g X)).1=(bonnet S X).1 ∧ (bonnet S (threadG g X)).2.1=(bonnet S X).2.1:=⟨rfl,rfl⟩
lemma glow_s (i:reach n)(k:ℕ)(s:Sweep n)(U:Pane n)(V: Ids n)(p:Injective (priorP V)):glow X f k (flashA s U,bun s V) i=flashA s (glow X f k (U,V)) i:=by
 rw [flash]; let M:=soup (RG.flags u U) k (lane s i); change well X f (soup (RG.flags u (flashA s U)) k i) (flashA s U) i _=polarT s.charge (if s.s.flip i.2 then (well X f M _ _ _)⁻¹ else (well X f M _ _ _)); rw [show soup (RG.flags u (flashA s U)) k i=Tw.ζ s⁻¹ M from ?_]; swap; · rw [flagsA,soupS,Tw.ζ,sitU]
 unfold well; by_cases h:M.Nonempty; swap; · simp only [if_neg h,if_neg (mt (Tw.ζL s⁻¹ M).2 h)]; exact flash s U i
 simp only [if_pos h,if_pos ((Tw.ζL s⁻¹ M).1 h),show bonnet (Tw.ζ s⁻¹ M) (bun s V)=man s (bonnet M V) from bonnetB s V _ k (lane s i) h p,man,Tw.ζ,card_map,mends]; apply flash -- tune simp binder Bone
lemma ray_s(k:ℕ)(U:Pane n)(V: Ids n)(s:Sweep n)(p:Injective (priorP V)):ray X f k (flashA s U,bun s V)= flashA s (ray X f k (U,V)):=by
 unfold ray; dsimp only; rw [boong, show glow X f k (flashA s (gauge _ U),_)= _ from funext fun i=> glow_s X f i k s _ V p, revG]; congr 1; funext i; unfold frameP; simp only [bun,man,Pi.inv_apply,map_inv]
lemma ray_g(k:ℕ)(V:Ids n)(g:Seat n→E)(U:Pane n):ray X f k (gauge g U,threadG g V)= gauge g (ray X f k (U,V)):=by
 have hh:frameP (threadG g V)=frameP V*g⁻¹:= rfl; unfold ray; simp only [hh,_root_.mul_inv_rev, inv_inv,gauge_sq,inv_mul_cancel_right]; rfl -- tune
lemma here(k:ℕ)(V: Ids n)(U:Pane n)(i:reach n)(p:Disjoint (RG.flags u U) (win k i)):ray X f k (U,V) i=U i:=by
 let G:= frameP V; have ht:glow X f k (gauge G U,V) i=gauge G U i:=by unfold glow well; dsimp only; rw [RG.gauge_flags,if_neg (fun v=> (pieV ..|>.mp v) p)]
 have h: ray X f k (U,V) i=gauge G⁻¹ (gauge G U) i:= congrArg (fun v=> (G i.1)⁻¹*v*((G⁻¹) (i.1+step i.2))⁻¹) ht -- tune synt
 rw [h]; exact congrFun (noon V U) i
end Spoke
end YM.CF.DPress.FD
