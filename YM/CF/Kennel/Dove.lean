import YM.CF.Kennel.Hook
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Lattice Wilson Laurent Precision Tree Finset Exterior Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- gauge use two parallel unitaries
section
variable {n:Type*}[LinearOrder n][Fintype n]
lemma soar (A B:UNI n)(S K W Y:Op n)(p:IsUnit (1+bentT K S W Y)): let V:=twist A; let H:=twist B
 traitP (V S) (B.val*K*star A.val) (A.val*W*star B.val) (H Y)= V (traitP S K W Y)∧ bentT (B.val*K*star A.val) (V S) (A.val*W*star B.val) (H Y)= H (bentT K S W Y):=by
 intro V H; let g(P:Op n):= A.val*P*star B.val; let h(P:Op n):=B.val*P*star A.val
 have hg(U V:UNI n)(f k: Op n): (U.val*f*star V.val)*(V.val*k*star U.val)= twist U (f*k):=by simp only [twist_formula,mul_assoc]; rw [show star V.val*(V.val*(k*star U.val))=k*star U.val by rw [←mul_assoc,V.property.1,one_mul]]
 have hf(U V:UNI n)(f k: Op n): twist U f*(U.val*k*star V.val)=U.val*(f*k)*star V.val:=by rw [twist_formula]; simp only [mul_assoc]; rw [show star U.val*(U.val*(k*star V.val))=k*star V.val by rw [←mul_assoc,U.property.1,one_mul]]
 have ht:bentT (h K) (V S) (g W) (H Y)= H (bentT K S W Y):=by unfold bentT h g V H; rw [hf,hg, ←map_mul] -- tune
 refine ⟨?_,ht⟩; unfold traitP laneP creep; change (1-V S)*(g W*(1+H Y))*((1+bentT (h K) (V S) (g W) (H Y))⁻¹*h K)=V _; rw [ht]
 rw [show 1-V S=V (1-S) from by simp,show 1+H _=H (1+Y) from by simp,show 1+H _=H (1+bentT K S W Y) from by simp]
 rw [show (H (1+bentT K S W Y))⁻¹=H ((1+bentT K S W Y)⁻¹) from (singsUnit false B _ p).symm]
 unfold g h; dsimp only [H,V]
 rw [hf,show A.val*W*star B.val*twist B (1+Y)=A.val*(W*(1+Y))*star B.val by rw [twist_formula]; simp only [mul_assoc]; rw [show star B.val * (B.val*((1+Y)*star B.val))=(1+Y)*star B.val by rw [←mul_assoc,B.property.1,one_mul]],hf,hg]
end
variable {j:ℕ}{L:Side}{ho:Odd L.val}
structure Spack (j:ℕ)(L: Side)(ho:Odd L.val) (a b d:ℝ)(n:ℕ):Prop where
 W : Tax L (ticketT (Thread j) true) false true a b n d
 P : Tax L (foal j true) true true a b n d
 U : Tax L (wh j L ho true) false false a b n d
 K : Tax L (pine j L ho (Thread j) true) true false a b n d
 A : Tax L (ticketT (Thread j) false) false true a b n d
 H : Tax L (pine j L ho (Thread j) false) true false a b n d
 AlongC : ∀ {N Q:Side}(G:Ratio N Q),G.count=L→n≤N.val→∀ M:Male,∀ x:Nom N Q,JointB G x d→∀ u,Along j L ho (Thread j) u M G (unionP x)
 tape : ∀ {N Q:Side}(G:Ratio N Q),G.count=L→n≤N.val→∀ M:Male,∀ x∈legal G d,IsUnit (Peaks.cloth j M G x)
private lemma debt {n m:ℕ}{L:Side}{A:Script Male}{B C:Bool}{a b c d e h:ℝ}(u:Tax L @A B C a b n c)(p:n≤m)(w:d≤ a)(g:b ≤ e)(t:h≤c)(r:0<h) : Tax L @A B C d e m h :=fun i _ _ G v f=> (((decayV u r t) i G v (p.trans f)).drop w).books g
lemma peach (h:1≤j)(hx:Even j)(hL: Odd L.val):∃ a b c:ℝ,0<a∧0<b∧0<c∧ ∃ n,Spack j L hL a b c n:=by
 let o:=canUse j L hL; obtain ⟨T,P,U⟩:=cup j L hL hx h o true
 obtain ⟨d,b,r,hd,hb,hr,n,T,K⟩:= Save.pair T (pine_funds j L hL hx h _ o true);
 obtain ⟨a,e,c,ha,he,hc,m,F,Y⟩:= Save.pair P U
 obtain ⟨i,z,l,hi,hz,hl,N,Z,H⟩:= Save.pair (cup j L hL hx h o false).1 (pine_funds j L hL hx h _ o false)
 obtain ⟨p,hp,M,D⟩:= joined j L hL hx h _ o; obtain ⟨w,hv,s,B⟩:= (useK j L hx hL o).2
 let R:=min (min r c) (min (min p w) l); have hR:0<R:=lt_min (lt_min hr hc) (lt_min (lt_min hp hv) hl)
 let L':=min i (min a d); have Hx:L' ≤ i:=min_le_left ..; have Hy:= min_le_right i (min a d); have Ht:R≤min p w:=(min_le_right ..).trans (min_le_left ..)
 refine ⟨L',z+b+e,R,lt_min hi (lt_min ha hd),by positivity,hR,n+m+M+s+N, debt T (by omega) (Hy.trans (min_le_right ..)) (by linarith) ((min_le_left ..).trans (min_le_left ..)) hR, debt F (by omega) (Hy.trans (min_le_left ..)) (by linarith) ((min_le_left ..).trans (min_le_right ..)) hR, debt Y (by omega) (Hy.trans (min_le_left ..)) (by linarith) ((min_le_left ..).trans (min_le_right ..)) hR,debt K (by omega) (Hy.trans (min_le_right ..)) (by linarith) ((min_le_left ..).trans (min_le_left ..)) hR,debt Z (by omega) Hx (by linarith) ((min_le_right ..).trans (min_le_right ..)) hR, debt H (by omega) Hx (by linarith) ((min_le_right ..).trans (min_le_right ..)) hR,fun G h hh T x hx=> D G h (by omega) T _ (show JointB G x p from ⟨hx.fg.shrink (Ht.trans (min_le_left ..)),hx.cg.shrink (Ht.trans (min_le_left ..)),fun y=>(hx.follow y).trans (Ht.trans (min_le_left ..))⟩),fun G g l' t i p=> B G g (by omega) _ (insideP G p (Ht.trans (min_le_right ..))) t⟩ -- tune
variable {a b d:ℝ}{n:ℕ}{m A B:Side}(P:Spack j L ho a b d n)(G:Ratio (CSide m B) (CSide A B))(M:Male)(p:G.count=L)(r:n≤ (CSide m B).val)
def capT {N:Type*}[LinearOrder N][Fintype N]
    (P F:Op N):= (1-P)*F*P -- remove G
include P p r
lemma Dusk(x:nomA m A B)(h:unionP x∈legal G d)(g:Site (More (CSide A B))→E)(C:Op (Single (CSide A B)))(w: ‖desire L j ho G M x (capT (foal j true M G (unionP x)) (foot G C))‖<1): let y:= july G g x; let Y:=capT (foal j true M G (unionP y)) (foot G (ActZ g C)); let X:=capT (foal j true M G (unionP x)) (foot G C); let U:=(parcel G true d).run g
 fruit L j ho G M y Y= ActZ (scaleG G g) (fruit L j ho G M x X) ∧ desire L j ho G M y Y= twist U (desire L j ho G M x X):=by
 intro y Y X U; let V:=(parcel G false d).run g; let K:= pine j L ho (Thread j) true M G; let W:=ticketT (Thread j) true M G; let Lh:= wh j L ho true M G; let Z:=foal j true M G; let S:=unionP x; let T:=unionP y; have ht:Lh T= twist V (Lh S):=crown_pulse G (P.U _ G p r) x h g; have hx:K T=U.val*K S*star V.val:= crown_pulse G (P.K _ G p r) _ h _; have hw:W T=V.val*W S*star U.val:=crown_pulse G (P.W _ G p r) _ h _; have he:Z T=twist U (Z S):=crown_pulse G (P.P _ G p r) _ h _; have hY:Y=twist U X:=by unfold Y capT; change (1-Z T)*_* Z T= twist U _; rw [he,foot_l G d]; change (1-twist U _)*twist U _*twist U _= twist U ((1-Z S)*foot G C*Z S); simp only [map_mul,map_sub]; rw [show twist U 1=1 from by rw [twist_formula,mul_one]; exact U.property.2]
 have hm:IsUnit (1+bentT (K S) (Lh S) (W S) X):= close_c w; obtain ⟨hh,hP⟩:= soar V U (Lh S) (K S) (W S) X hm; change summit _ (traitP (Lh T) (K T) (W T) Y)= _ ∧ bentT (K T) (Lh T) (W T) Y=_; rw [hx,hY,ht,hw]; rw [hh,hP]; exact ⟨summit_l G d g _,rfl⟩
end YM.CF.Kennel
