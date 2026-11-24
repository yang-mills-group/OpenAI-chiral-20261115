import YM.CF.Urn.Scope
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {N P L:Side}{G:Ratio N P}{ι:Type*}
abbrev cope (j:ℕ)(v b:Bool): WG Male:= fun M N x=> if b then skewE j M v N x else 1
lemma cape (j:ℕ)(v b:Bool)(hj:1 ≤ j): Lively (cope j v b):=by cases b; exact Lively.one; exact skew_s j hj v
lemma boost (k:WG Male)(v:Lively k)(S:ι→Male): Lively fun i=>k (S i):=by obtain ⟨i,h,p,t,z,s,m,H⟩:=v; exact ⟨i,h,p,t,z,s,m,fun i _ _=> H (S i) _ (by assumption)⟩
section
variable (j:ℕ)(u v b t:Bool)
abbrev icyS(S:ι→ Male):WG ι:=fun i n=>pale (cope j u b (S i) n)
abbrev startZ(K:WG ι)(S:ι→Male)(h:Odd L.val)(v w:Bool): Script ι:= Fresco L h j K S v w (fun _ _ _ _ _=>1)
abbrev meet(K:WG ι)(S:ι→Male)(h:Odd L.val)(u v:Bool)(N M:Bool):Script ι:=Spree (startZ j K S h u N) (startZ j K S h v M)
lemma odds (h:Odd L.val)(K:WG ι)(S:ι→Male)(hp:Lively K)(he:Even j)(ht:1≤j)(p:∀ i n,K i n 1=0)(N M:Bool):Save L true true (meet j K S h u v N M):= SpreeV L _ _ (valley _ h j he ht _ hp p _ _ _ _ (Save.one ι)) (valley _ h j he ht _ hp p _ _ _ _ (Save.one ι))
lemma earnD (L:Side)(h:Odd L.val)(K:WG ι)(S:ι→Male)(hp:Lively K)(he:Even j)(ht:1≤j)(p:∀ i n,K i n 1=0)(N M:Bool): ∃ a C e:ℝ,0<a∧0<C∧0<e∧∃ m:ℕ,∀ x:ℝ,0<x→x≤e → corn L true true (meet j K S h u v N M) (icyS j u b S) (fun i=> cope j v t (S i)) a C m x:= corner _ _ _ (odds _ _ _ h K S hp he ht p N M) (boost (fun i N=>pale _) (Lively.reverseL (cape j u b ht)) S) (boost _ (cape j v t ht) S)
lemma workB (j:ℕ)(c b:Bool)(m:ℕ) : let K:=cope j c b; ∀ p:1≤ j,∃ C:ℝ,0<C ∧ ∀ S:ι→Male,∀ (F:Script ι) L (z e u:ℝ),0<z→0<e→0≤u→∀ v:ℕ,Score L @F true false z u m v e→∃ a k:ℝ,0<a∧0<k∧ ∃ n:ℕ,∀ x:ℝ,0<x→x≤ k→flower L @F (icyS j c b S) a (C*u) m n x:=by -- icy u shadow
 intro B p; obtain ⟨c',f,a,d,hx,l,n,H⟩:=serene _ (Lively.reverseL (cape j c b p)) m; refine ⟨2*c',by positivity,fun S F L z e u g v t b' Y=>⟨min z a,min e d,lt_min g hx,lt_min v l,max n b',?_⟩⟩; intro x h l i N P G m' hP
 have hy:(0:ℝ)<L.val:=Nat.cast_pos.mpr L.property; have hq:= (H x h (l.trans (min_le_right ..)) L G ((le_max_left ..).trans hP) (S i)).desc (min_le_right z a) (by positivity); have hp := (room_L G _ ((Scroll (A:=@F) Y h (l.trans (min_le_left ..))) i G m' ((le_max_right ..).trans hP))).desc (min_le_left z a) (x:=(L.val:ℝ)⁻¹) (by positivity)
 rw [mul_assoc]; exact duo hq hp (by positivity) (by positivity) t
end
end YM.CF.Urn
