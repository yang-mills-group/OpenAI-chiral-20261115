import YM.CF.Proa.Plan
set_option autoImplicit false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {ι n:Type*}[LinearOrder n][Fintype n]{W V P B K:Op n}(u:Bool)
lemma clear_s (h:Clad P B W V K) : sprig u B *liftJet u (laneP B W K) W V=sprig u B * liftJet u (laneP B W K) W V * sprig u P:=by
 let S:=laneP B W K
 have hp : (1-S)*W*P=B*W*P:=by rw [mul_assoc,← show (1+S)*throat P B W=W*P from h.stave, ←mul_assoc,mul_eq_one_comm.mp h.flick,one_mul]
 have hv:B*star (1+S)*V*(1-P)=0:=by
   have he:W*K= (1+S)*B:=by
      unfold S laneP; rw [add_mul,one_mul,mul_assoc _ K B,h.stem,sub_mul,one_mul,sub_mul,h.quotaW]; abel
   have hq:star ((1-P)*star V*((1+S)*B))= star ((1-P)*K):= by rw [← he, ←mul_assoc _ W K, mul_assoc _ (star V),h.balance,mul_one]
   simp only [star_mul,star_star,h.proj.one_sub.isSelfAdjoint.star_eq,h.helm.isSelfAdjoint.star_eq] at hq; rw [mul_assoc,hq,←h.proj.one_sub.isSelfAdjoint.star_eq,←star_mul,sub_mul,one_mul,h.tray,sub_self,star_zero]
 cases u
 · change (1-B)*((1-S)*W)=(1-B)*((1-S)*W)*(1-P); rw [mul_sub,mul_one,show (1-B)*((1-S)*W)*P=0 from ?_,sub_zero]
   rw [mul_assoc,hp,←mul_assoc (1-B),←mul_assoc,sub_mul,one_mul,h.helm.isIdempotentElem.eq]; simp
 change B*(star (1+S)*V)= B*(star (1+S)*V)*P; rw [←mul_assoc]; exact sub_eq_zero.mp (by rwa [mul_sub,mul_one] at hv)
variable (L:Side)(ho:Odd L.val)(j:ℕ)(K:WG ι)(p:∀ i n,K i n 1=0)(S:ι→Male)
abbrev Sky(v:Bool): Script ι:= treeF L ho j K S v (fun _ _ _ _ _=>1)
variable {N Q:Side}
include p
lemma glass (i:ι)(G:Ratio N Q)(v:Bool)(h:Along j L ho (Thread j) true (S i) G 1): Sky L ho j K S v i G 1=liftD L ho j K S v [] i G 1:=by
 have hp:unionP (1:Nom N Q)=1:=by simp [unionP,profile_trivial]
 have hf:icec (1:Coil N Q)=1:=by rw [←hp,revI]
 rw [Sky,liftD,grapple,List.map_nil,List.prod_nil,one_mul]; simp only [treeF,hf,Fresco]; congr 2 -- tune
 unfold sees; rw [hf,pris_z L ho j K p]
 have hy:= clear_s v (court G j L ho (Thread j) true (S i) h); rw [mul_assoc] at hy; rw [mul_one]; exact hy
omit L p
set_option linter.unusedSectionVars false in
lemma giant (he:Even j)(hp:2≤j)(m:ℕ): ∃ C:ℝ,0<C ∧∀ L:Side,∀ t:Odd L.val,∀ v:Bool,∀ (K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→ ∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (C*followV [] L) m k e:=by
 have ht(v:Bool):∃ C:ℝ,0<C∧∀ L:Side,∀ t:Odd L.val,∀ (K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (C*followV [] L) m k e:=by
    have hj:1≤j:=by omega
    obtain ⟨C,h,H⟩:=tremendous j he v [] hp m -- tune
    refine ⟨C+1,by linarith,fun L t K S h p=>?_⟩; obtain ⟨a,e,hx,g,k,W⟩:= H L t K h p S
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
 obtain ⟨c,p₁,f⟩:=ht true; obtain ⟨b,p,g⟩:= ht false; refine ⟨max c b,p₁.trans_le (le_max_left ..),fun L t v K S h x=>?_⟩
 have hx(v)(y:ℝ)(k:y ≤ max c b)(h: ∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (y *followV [] L) m k e):∃ a e:ℝ,0<a∧0<e∧∃ k:ℕ,Score L (Sky L t j K S v) true false a (max c b*followV [] L) m k e:=by
    obtain ⟨a,e,i,z,k',H⟩:=h; exact ⟨a,e,i,z,k',fun i _ _ G s l=>(H i G s l).prime (fun _=>mul_le_mul_of_nonneg_right k (Vpos ..|>.le))⟩
 cases v; exact hx _ _ (le_max_right ..) (g L t K S h x); exact hx _ _ (le_max_left ..) (f L t K S h x)
end YM.CF.Urn
