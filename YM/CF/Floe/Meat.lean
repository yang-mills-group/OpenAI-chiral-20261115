import YM.CF.Floe.Ice
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c d r e:ℝ}{F G:pMat}{u v:Bool}
open LedgerP Tour Enters
abbrev Φv(j:ℕ):pMat:= xD^j
abbrev pN(j:ℕ):pMat:= tagC (Φv j)*kPv*(starL (Φv j))
abbrev pE(j:ℕ):pMat:= tagC (Φv j)*ePv*(starL (tagC (Φv j)))
abbrev pZ(j:ℕ):pMat:= (Φv j)*qPv*(starL (tagC (Φv j)))
lemma drop_c {h:certS F u v a b r}(p:d≤a)(q:e≤b)(x:r ≤c):certS F u v d e c:=fun i=>((slim_e (cert_drop h p) q) i).books x
lemma μLife : ∃ a b c r:ℝ,0<a∧0<b∧0<c∧0<r∧ r<1∧∀ i:ℕ, certS (pN i) false true a b (c*r^i) ∧ certS (pE i) false false a b (c*r^i) ∧ certS (pZ i) true false a b (c*r^i):=by
 obtain ⟨a,b,c,r,p,q,t,w,v,Z⟩:= drift; obtain ⟨d,e,f,x,y,l,D,E⟩:=like κLp σPv; obtain ⟨k,g,i,h,hg,hp,H⟩:=θPv; let A:=min a (min d k); let B:=min b (min e g); let M:=max f i; have hM:0<M:=lt_max_of_lt_left l; have hx:0<A:=lt_min p (lt_min x h); have hv(n:ℕ):certS (Φv n) true true A B (c*r^n):=drop_c (h:=Z n) (min_le_left ..) (min_le_left ..) le_rfl
 have hA:A ≤ d∧ A ≤ k:=⟨(min_le_right ..).trans (min_le_left ..),(min_le_right ..).trans (min_le_right ..)⟩; have hB:B≤e∧B≤g:=⟨(min_le_right ..).trans (min_le_left ..),(min_le_right ..).trans (min_le_right ..)⟩; have hU:= drop_c (h:=E) hA.1 hB.1 (le_max_left f i)
 refine ⟨A,B,4*(c*M*c),r^2,hx,lt_min q (lt_min y hg),by positivity,by positivity,by nlinarith,?_⟩
 intro i'; let z:= c*r^i'; rw [show 4*(c*M*c)*(r^2)^i'=2*(2*(z*M)*z) from ?eq]; swap; · unfold z; rw [pow_right_comm]; ring
 exact ⟨fun i'=>(((tagCt (hv _) i').product (drop_c (h:=D) hA.1 hB.1 (le_max_left f i) i') hx.le).product (opL (hv _) i') hx.le),fun i'=> (((tagCt (hv _) i').product (hU i') hx.le).product (opL (tagCt (hv _)) i') hx.le),fun i'=> (((hv _ i').product (drop_c (h:=H) hA.2 hB.2 (le_max_right f i) i') hx.le).product (opL (tagCt (hv _)) i') hx.le)⟩
section
variable (i:Δ)(k:ℕ)(x:Own i.1)
local notation "W"=>skin x.val
@[simp] lemma ζpv:Φv k i W=paddle i k x:=by change (xD i W)^k=_; unfold xD paddle; rw [mass_j, decay,decay,grow_nat]; rfl
@[simp] lemma pp_c:pN k i W=incomeD i k x:=by change tagC _ _ _* kPv _ _*starL _ _ _=_; rw [tag_my,star_my,kPv_i,ζpv]; unfold incomeD; rw [Kcc,ccT]; rfl
@[simp] lemma pe_c:pE k i W=incomeA i k x:=by
 change tagC _ _ _*ePv _ _*starL _ _ _=_; rw [tag_my,star_my,tag_my,ePv_i,ζpv]; unfold incomeA; rw [Kcg,←cc_star]; unfold cc; rw [star_star]; rfl
@[simp] lemma pz_c:pZ k i W=incomeW i k x:=by change Φv k i W*qPv _ _*starL _ _ _=_; rw [star_my,tag_my,qPv_i,ζpv, ← cc_star,cc,star_star]; rfl
end
abbrev user(H:Seal (Site (More N)) → Raw ↥(Kelp N a) (Model N))(p:0<a)(i:Seal (Site (More N))) (x:Own N): Op (Model N):=H i (uθ x p)
def euro {s:Tag (ku (a:=a) (N:=N))}:Tag (slotK N):=⟨s.run,fun i j x p=> s.keeps _ _ _ p⟩
lemma tipV{F':Raw (Kelp N a) (Model N)}{S T:Tag (ku (N:=N) (a:=a))} (θCt:Continuous (skin (N:=N)))(h:Crown (badge _) S T b c F')(p:0<a):∃ H K,(∀ i: Seal (Site (More N)),Suite (badge _) S T i (K i) (H i))∧(∀ i,Ticket (@euro _ _ S) (@euro _ _ T) i (K i) (user H p i)) ∧ Ledger b K c∧ ∀ z:Own N,F' (uθ z p)= ∑ i,H i (uθ z p):=by
 obtain ⟨H,K,u,v,x⟩:=h; refine ⟨H,K,u,fun i=>?_,v,fun z=>x _⟩; refine ⟨fun g j=>?_,fun j k=>?_⟩
 · have he:(ku (N:=N) (a:=a)).drive g (uθ j p)=uθ ((slotK N).drive g j) p:=Subtype.ext (scene ..); unfold user; exact he ▸ ((u i).frame g (uθ j p)) -- tune e.Ticket orientation
 obtain ⟨g,w,y,v',f⟩:=((u i).expo j k); refine ⟨g,w,fun x=>y _,fun x y=>Floe.moment i x y p ▸ v' _ _, f.comp ?_⟩ -- f comp meta
 exact Continuous.subtype_mk (Continuous.comp θCt continuous_subtype_val) _
end YM.CF.Floe
