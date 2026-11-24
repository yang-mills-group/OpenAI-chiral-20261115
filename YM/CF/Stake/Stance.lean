import YM.CF.Stake.Male
set_option autoImplicit false
noncomputable section
namespace YM.CF.Urn

set_option maxHeartbeats 400000
set_option synthInstance.maxSize 23000
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {ι n:Type*}[LinearOrder n][Fintype n]{W V P B K:Op n}(u:Bool)

variable (L:Side)(ho:Odd L.val)(j:ℕ)(K:WG ι)(p:∀ i n,K i n 1=0)(S:ι→Male)
 
variable {N Q:Side}
include p
omit L p
set_option linter.unusedSectionVars false in
lemma giantL (he:Even j)(hp:2≤j)(m:ℕ): ∃ C:ℝ,0<C ∧∀ L:Side,∀ t:Odd L.val,∀ v:Bool,∀ (ι:Type)(K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→ ∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (C*followV [] L) m k e:=by
 have ht(v:Bool):∃ C:ℝ,0<C∧∀ L:Side,∀ t:Odd L.val,∀ (ι:Type)(K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (C*followV [] L) m k e:=by
    have hj:1≤j:=by omega
    obtain ⟨C,h,H⟩:=tremendous j he v [] hp m -- tune
    refine ⟨C+1,by linarith,fun L t ι K S h p=>?_⟩; obtain ⟨a,e,hx,g,k,W⟩:= H L t K h p S
    let F:=treeF L t j K S v (grass j S v); let A:=Sky L t j K S v; let X:=liftD L t j K S v []; let R:Script ι:=fun i _ _ G x=> A i G x-X i G x
    have hp': Save L true false @F := vitalC L t j he hj K h p S v (grass j S v) (grass_S L t j he hj S v); have hA: Save L true false @A:=vitalC L t j he hj K h p S v _ (Save.one ι); have hg:Save L true false @R:= hA.sub ((transportS (grapple_f j L t he hj _ (canUse j L t) []) S).mul hp')
    obtain ⟨b,f,e',p₁,z,u,m',Y⟩:=hg; obtain ⟨c',p',N,H'⟩:= joined j L t he hj _ (canUse j L t); let n':= m'+N
    let e'' := min e e'; have hB:= lt_min g u
    have hw : Tax L @R true false b f n' e'' := fun i _ _ T L' G=> decayV (A:=@R) Y hB (min_le_right ..) i T L' ((show m'≤n' by unfold n'; omega).trans G)
    have hz (i) {N₀ Q:Side}(G:Ratio N₀ Q)(hc:G.count=L)(x:n' ≤ N₀.val): R i G 1=0:=by
       have hp:unionP (1:Nom N₀ Q)=1:=by simp [unionP,profile_trivial]
       have hj':JointB G 1 c':=by
           let T:= (1:Nom N₀ Q); refine ⟨guard0 p'.le, guard0 p'.le,fun x=>?_⟩; have he(x:Site (More Q))(d:Walk): travel T.1 x d=1:=by induction d generalizing x with| nil=>rfl|cons a d ih=>rw [travel,ih]; simp [T,Step.read];
           change ‖brand 1-brand (travel T.1 _ _)‖≤_; rw [he,sub_self,norm_zero]; exact p'.le
       have hv:=H' G hc ((show N ≤ n' by unfold n'; omega).trans x) (S i) _ hj'; rw [hp] at hv; unfold R; exact sub_eq_zero.mpr (glass _ _ _ _ p _ i G v (hv _))
    obtain ⟨a',l',w,z',r,v',E⟩:=weighted hw p₁ z hB _ (Vpos [] L) @hz m
    refine ⟨min a' a,l',lt_min w hx,z',k+v',fun i c f G hl su=>?_⟩
    have hx:= (E i G hl ((show v'≤ k+v' by omega).trans su)).desc (min_le_left a' a) (by positivity)
    have hv:= ((Scroll (A:=@X) W z' (r.trans (min_le_left ..))) i G hl ((show k≤ k+v' by omega).trans su)).desc (min_le_right a' a) (by positivity)
    have hu:=hx.plus hv
    have heq:(fun x: legal G l'=>R i G x.val+ X i G x.val)=(fun x:legal G l'=> A i G x.val):=funext fun x=>by unfold R; rw [sub_add_cancel]
    rw [heq] at hu; refine hu.prime ?_; intro i; simp [add_mul,add_comm]
 obtain ⟨c,p₁,f⟩:=ht true; obtain ⟨b,p,g⟩:= ht false; refine ⟨max c b,p₁.trans_le (le_max_left ..),fun L t v ι K S h x=>?_⟩
 have hx(v)(y:ℝ)(k:y ≤ max c b)(h: ∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (y *followV [] L) m k e):∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (max c b*followV [] L) m k e:=by
    obtain ⟨a,e,i,z,k',H⟩:=h; exact ⟨a,e,i,z,k',fun i _ _ G s l=>(H i G s l).prime (fun _=>mul_le_mul_of_nonneg_right k (Vpos ..|>.le))⟩
 cases v; exact hx _ _ (le_max_right ..) (g L t ι K S h x); exact hx _ _ (le_max_left ..) (f L t ι K S h x)

lemma workBB (j:ℕ)(c b:Bool)(m:ℕ) : let K:=cope j c b; ∀ p:1≤ j,∃ C:ℝ,0<C ∧ ∀ (ι:Type),∀ S:ι→Male,∀ (F:Script ι) L (z e u:ℝ),0<z→0<e→0≤u→∀ v:ℕ,Score L @F true false z u m v e→∃ a k:ℝ,0<a∧0<k∧ ∃ n:ℕ,∀ x:ℝ,0<x→x≤ k→flower L @F (icyS j c b S) a (C*u) m n x:=by -- icy u shadow
 intro B p; obtain ⟨c',f,a,d,hx,l,n,H⟩:=serene _ (Lively.reverseL (cape j c b p)) m; refine ⟨2*c',by positivity,fun ι S F L z e u g v t b' Y=>⟨min z a,min e d,lt_min g hx,lt_min v l,max n b',?_⟩⟩; intro x h l i N P G m' hP
 have hy:(0:ℝ)<L.val:=Nat.cast_pos.mpr L.property; have hq:= (H x h (l.trans (min_le_right ..)) L G ((le_max_left ..).trans hP) (S i)).desc (min_le_right z a) (by positivity); have hp := (room_L G _ ((Scroll (A:=@F) Y h (l.trans (min_le_left ..))) i G m' ((le_max_right ..).trans hP))).desc (min_le_left z a) (x:=(L.val:ℝ)⁻¹) (by positivity)
 rw [mul_assoc]; exact duo hq hp (by positivity) (by positivity) t

end YM.CF.Urn
namespace YM.CF.Stake
set_option synthInstance.maxSize 23000
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc MeasureTheory Urn Hake Levier
open Fir Matrix Phase
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j m:ℕ}{r d x:ℝ}{L:Side}{ι:Type*}
lemma priceX(v:TailB)(j:ℕ)(m:ℕ)(p:2 ≤ j)(h:Even j):∃ C:ℝ,0<C ∧∀ L:Side,∀ t:Odd L.val,∀ (ι:Type)(K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→∃ T r:ℝ,0<T∧0<r∧∃ k:ℕ, AspectB t v K S T r C k j m:=by
 obtain ⟨C',a,T⟩:=Urn.giantL j h p m; obtain ⟨B,x,V⟩:= Urn.workBB j (!v.2) v.1 m (by omega)
 refine ⟨B*C',by positivity,fun L t ι K S u b=>?_⟩; obtain ⟨a',e,hA,hE,l,A⟩:= T L t _ ι K S u b
 obtain ⟨c,d,hc,hd,z,T⟩:= V ι S (@Urn.Sky ι L t j K S (!v.2)) L _ _ _ hA hE (mul_nonneg a.le (Vpos ..|>.le)) l A -- tune `@`; syntax
 refine ⟨d,c,hd,hc,z,fun x p y=>?_⟩; rw [mul_assoc]; exact T x p y
local notation "Mine"=> Levier.mineB
local notation "Pit"=> Levier.mineC
lemma legWide (m:ℕ)(p:2 ≤ j)(h:Even j):∃ C:ℝ,0<C ∧∀ L:Side,∀ t:Odd L.val,∀ (ι:Type)(K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→∃ T r:ℝ,0<T∧0<r∧∃ k:ℕ,∀ x:ℝ,0<x→x≤T→∀ c ∈ (univ:Finset TailB),∀ {N P:Side}(G:Ratio N P),G.count=L→k ≤ N.val →∀ p:Odd G.count.val,∀ i:ι,Street (badge _) (pinH G x true) (pinH G x false) m (L.val:ℝ)⁻¹ r (fun _=>C*followV [] L) (Mine (j:=j) G p x S K i c) :=by
 choose C u D using fun p':TailB=>priceX p' j m p h
 let X:ℝ:= ∑ i,C i
 refine ⟨X,sum_pos (fun i _=>u i) univ_nonempty,fun L t ι K S l n=> ?_⟩
 choose T R g f k V using fun p:TailB=> D p L t ι K S l n
 let A:= (univ:Finset TailB); let W:= A.inf' (show A.Nonempty from univ_nonempty) T; let Z:= A.inf' (show A.Nonempty from univ_nonempty) R
 refine ⟨W,Z,(lt_inf'_iff _).mpr (fun i _=>g i),(lt_inf'_iff _).mpr (fun i _=>f i), A.sup k,fun x q b v hv N P G hx h u' i=>?_⟩
 have hp:= V v x q (b.trans (inf'_le _ hv)); have hz:= hp i G hx ((le_sup hv).trans h)
 subst L; have hy:0<(G.count.val:ℝ):=Nat.cast_pos.mpr G.count.property
 exact (hz.desc (inf'_le _ hv) (by positivity)).prime (fun i=>mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> (show 0<C i from u i).le) hv) (Vpos ..|>.le)) -- name collision u after subst
end YM.CF.Stake
