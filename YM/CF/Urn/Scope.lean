import YM.CF.Urn.Room
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {N Q L:Side}{G:Ratio N Q} {ι:Type*}{e a s v:ℝ}
private abbrev bindL (A:WG ι)(i:ι)(G:Ratio N Q)(p:↑(cro G e)):=foot G (A i Q p.val.2)
private abbrev oat(A:Script ι)(i:ι)(G:Ratio N Q)(p:↑(cro G e)):= A i G p.val.1
def corn (L:Side)(u v:Bool)(A:Script ι)(B: WG ι)(C:WG ι)(z K:ℝ)(N':ℕ)(e:ℝ):Prop:=∀ i {N Q: Side}(G:Ratio N Q),G.count=L → N'≤ N.val → Crown (badge _) (pinH G e u) (pinH G e v) z K (fun x=> bindL B i G x *oat @A i G x *bindL C i G x)
lemma corner(A:Script ι)(B C:WG ι)(h:Save L true true @A)(p:Lively B)(q:Lively C) :∃ a K e:ℝ,0<a∧0<K∧0<e∧∃ m:ℕ,∀ t:ℝ,0<t→t≤e→ corn L true true @A B C a K m t:=by
 obtain ⟨b,r,e,i,k,u,m,H⟩:=h; obtain ⟨c,s,w,c',j,S,N,X⟩:=p; obtain ⟨v,l,f,t₀,z,t,M,Y⟩:=q
 let d:=min b (min c v); have hd:0<d:=lt_min i (lt_min c' t₀); let V:=min e (min w f)
 refine ⟨d, _,V,hd, (show 0 < (2:ℝ)*(2*(s*r)*l) by positivity), lt_min u (lt_min S t), max m (max N M),fun x p q i N' P G g l=>?_⟩
 have hp:N'.val ≤ P.val:=by rw [G.exact_size]; exact Nat.le_mul_of_pos_right _ G.count.property
 have he : N ≤ P.val := ((le_trans (le_max_left ..) (le_max_right ..) : N ≤ max m (max N M)).trans l).trans hp; have hf : M ≤ P.val:= ((le_trans (le_max_right ..) (le_max_right ..) : M ≤ max m (max N M)).trans l).trans hp
 have ht:= (rideC G _ ((axis_down _ _ (X i P he) x p (q.trans ((min_le_right ..).trans (min_le_left ..)))))).drop (show d ≤ c from (min_le_right ..).trans (min_le_left ..)); have hv:= (rideC G _ ((axis_down _ _ (Y i P hf) x p (q.trans ((min_le_right ..).trans (min_le_right ..)))))).drop (show d ≤ v from (min_le_right ..).trans (min_le_right ..))
 have hw:=room_c G _ ((decayV H p (q.trans (min_le_left ..)) i G g ((le_max_left ..).trans l)).drop (show d ≤ b from min_le_left ..)); exact (ht.product hw hd.le).product hv hd.le
lemma serene(B:WG ι)(h:Lively B)(m:ℕ):∃ C:ℝ,0<C ∧ ∃ a e:ℝ,0<a∧0<e∧∃ v:ℕ,∀ x:ℝ,0<x→x≤e→∀ L:Side,∀{N P:Side}(G:Ratio N P),v≤ N.val→∀ i:ι, Street (badge _) (pinH G x true) (pinH G x true) m (L.val:ℝ)⁻¹ a (fun _=> C) (bindL B i G):=by
 obtain ⟨a,c,e,p,l,t,n,H⟩:=h; let b:= min 1 (a/2); have hp:0<b:=lt_min zero_lt_one (half_pos p); have hb:2*b≤a:= (mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num:(0:ℝ)≤2)).trans_eq (by ring)
 refine ⟨_,show 0<((b/(m+1:ℝ))⁻¹)^m*c by positivity,b,e,hp,t,n,fun x u v L N P G h i=>?_⟩
 have he:N.val ≤P.val:=by rw [G.exact_size]; exact Nat.le_mul_of_pos_right _ G.count.property
 have hf:0<(L.val:ℝ):= Nat.cast_pos.mpr L.property
 exact deck_adap (rideC G _ (axis_down _ _ (H i P (h.trans he)) x u v)) hp (min_le_left ..) hb m (L.val:ℝ)⁻¹ (by positivity) (by rw [inv_le_one₀ hf]; exact_mod_cast L.property)
-- Curved two-background kernels, comprises mandatory charges working on same period (no relation between actual/washed fine)
def flower (L:Side)(A:Script ι)(B:WG ι)(z K:ℝ)(m n:ℕ)(v:ℝ):Prop:=∀ i {N Q: Side}(G:Ratio N Q),G.count=L→n ≤ N.val → Street (badge _) (pinH G v true) (pinH G v false) m (L.val:ℝ)⁻¹ z (fun _=> K) (fun x=>bindL B i G x*oat @A i G x)
lemma bloom(B:WG ι)(h:Lively B)(m:ℕ):∃ C:ℝ,0<C ∧∀ (F:Script ι)(L:Side)(z e u:ℝ)(p:0<z)(hx:0<e)(t:0≤u)(v:ℕ), Score L @F true false z u m v e→∃ a k:ℝ,0<a∧0<k∧∃ n:ℕ,∀ x:ℝ,0<x→x≤ k→ flower L @F B a (C*u) m n x:=by
 obtain ⟨c,f,a,d,hx,p,n,H⟩:=serene B h m; refine ⟨2*c,by positivity,fun F L z e u g v t b Y=> ⟨min z a,min e d,lt_min g hx,lt_min v p, max n b,?_ ⟩ ⟩; intro x h l i N P G m' hP
 have hy:(0:ℝ)<L.val:=Nat.cast_pos.mpr L.property
 have hq:= (H x h (l.trans (min_le_right ..)) L G ((le_max_left ..).trans hP) i).desc (min_le_right z a) (by positivity); have hp:Street (badge _) (pinH G x true) (pinH G x false) m (L.val:ℝ)⁻¹ (min z a) (fun _=>u) (oat @F i G):=(room_L G _ ((Scroll (A:=@F) Y h (l.trans (min_le_left ..))) i G m' ((le_max_right ..).trans hP))).desc (min_le_left ..) (by positivity)
 rw [mul_assoc]; exact duo hq hp (by positivity) (by positivity) t
end YM.CF.Urn
