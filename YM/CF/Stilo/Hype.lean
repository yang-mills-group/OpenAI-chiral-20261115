import YM.CF.Stilo.Rive
set_option synthInstance.maxSize 8000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {A:Type*}[Fintype A][DecidableEq A]{ι n:Type*}[LinearOrder n][Fintype n][LinearOrder ι][Fintype ι]
open Pastry Scree
lemma view_y(L:ι→n→ℂ)(q:ι→ι→ℂ)(p:List ι): taskC (lank L) (price q n) p=((claps p).map (fun x=> offer q x • rollC (lank L) x.term)).sum:=by
 have he(p:List ι): spanP n (rollC (lank L) p):=by induction p with| nil=>exact grandP | cons i j ih=> exact spanT (slap L i) ih
 apply borderE (rent_m ..) (mountT 0 _ _ (fun i _=> spanS (he _) _)); rw [pitchA]
 let u:= pod (LinkI ι n); let X:=pod n
 let B:=largeH L; let C:ι→FC (LinkI ι n):=smallH q; let V:=pailL (@seenH ι n) ∅
 have hk:u= hoist seenH ∅ X:=by unfold X; rw [pod,hoops,knot_empty]
 have hp : Deck (@seenH ι n) ∅:=dH
 have ht(i)(x:Wave (LinkI ι n)):V (acts (B i) x)=acts (lank L i) (V x):=by
    have he:flame (n:=n) i∉ lows seenH:=by simp only [lows,Finset.mem_map,mem_univ,true_and]; rintro ⟨j,h⟩; exact distinguish i j h.symm
    unfold B V largeH lank; rw [act_add,map_add,show pailL seenH ∅ (acts (put (flame i)) x)=0 from branchX seenH ∅ hp he (notMem_empty _) _,zero_add,act_sum,map_sum,act_sum]
    exact sum_congr rfl fun j _=> by rw [act_smul,map_smul,act_smul,show pailL seenH ∅ (acts (put (seenH j)) x)=_ from petals _ ∅ hp j x]
 have hu(i):acts (C i) u=0:=by
    unfold C smallH; rw [act_sum]; apply sum_eq_zero; intro j _; rw [act_smul]; rw [show acts (takeF (flame j)) u=0 from ?_,smul_zero]
    unfold u pod; exact Eq.trans (take_act (n:=LinkI ι n) _ _) (if_neg (notMem_empty _))
 have hV (p:List ι) : V (chime B u p)=chime (lank L) X p:=by induction p with| nil=> rw [emptyChime,emptyChime,hk]; exact pourL _ _ hp X | cons i p ih=> rw [charm,charm]; exact (ht i _).trans (congrArg _ ih)
 change V (chime (B+C) u p)=acts _ X
 rw [shadeW (B+C) B C u q hu (shoot L q) (fun i=> rfl),map_list_sum,List.map_map]
 have he(L:List (Cl ι))(F:Cl ι→FC n):acts (L.map F).sum X=(L.map (fun i=>acts (F i) X)).sum:=by induction L with| nil=> simp |cons i L h=> simp [h]
 rw [he]; congr 1; apply List.map_congr_left; intro i _; rw [Function.comp_apply,invest,map_smul,hV,act_smul]; rfl
abbrev fixT(P:Op n)(t:ι→ Bool)(v:ι→ n → ℂ)(q:ι→ι→ℂ)(D:List ι): FC (LeanV n):= taskC (lank (fun i (j:LeanV n)=> if j.1=!(t i) then v i j.2 else 0)) (price q (LeanV n)) D
lemma cedar(P:Op n)(t:ι→Bool)(v:ι→n→ℂ)(q:ι→ι→ℂ)(D:List ι)(h:IsStarProjection P): (nursery P h).eval (fixT P t v q D)= ((claps D).map (fun x=>offer q x • rollC (fun i=> ∑ j,v i j • cry P (t i,j)) x.term)).sum:=by
 unfold fixT; rw [view_y,map_list_sum,List.map_map]; congr 1; let Z(i:ι)(j:LeanV n):ℂ:= if j.1=!(t i) then v i j.2 else 0
 let L:=lank Z; let K:=(nursery P h); let F(i):=∑ j,v i j • cry P (t i,j)
 have he(u:List ι):spanP (LeanV n) (rollC L u):=by induction u with| nil=> exact grandP| cons x u ih=> exact spanT (slap Z x) ih
 suffices H:∀ u:List ι,K.eval (rollC L u)=rollC F u from List.map_congr_left (fun x _=> show K.eval (offer q x • rollC L x.term)=_ from (map_smul ..).trans (congrArg _ (H x.term)))
 intro u; induction u with
 | nil=> exact K.eval_one
 | cons x u ih=>
    change K.eval (L x* rollC L u)=F x*rollC F u; rw [fireT K (slap Z x) (he u),ih]; congr 1
    unfold F lank; rw [map_sum,Fintype.sum_prod_type,Finset.sum_eq_single (!(t x))]; apply sum_congr rfl; intro i _; rw [map_smul]; unfold Z; simp only [if_pos rfl]; apply congrArg; rw [show put (!(t x),i)=poke _ from (Poly.tag_once (Pastry.cane _) _).symm,K.eval_oneT,Poly.tag_once]; cases l:t x <;> rfl
    intro a _ p; apply sum_eq_zero; intro j _; unfold Z; rw [if_neg p]; simp
    simp
lemma meantZ(P:Op n)(t:ι→Bool)(v:ι→n→ℂ)(q:ι→ι→ℂ)(D:List ι)(h:IsStarProjection P)(u:Wave n): acts ((nursery P h).eval (fixT P t v q D)) u=((claps D).map (invest (fun i=> ∑ j,v i j • cry P (t i,j)) u q)).sum:=by
 rw [cedar]; have he(L:List (Cl ι))(F:Cl ι→FC n):acts (L.map F).sum u=(L.map (fun i=>acts (F i) u)).sum:=by induction L with| nil=>simp| cons i L h=> simp [h]; -- tune
 rw [he]; congr 1; apply List.map_congr_left; intro i _; rw [act_smul]; rfl
open Phase Spire Proa
variable {L N Q B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P:Grasp Y B e}(he:0<e)
variable (G:Ratio (CSide N B) (CSide Q B))(hk:G.count=L)(w:P.roundZ ≤ (CSide N B).val)(A:Aim (CSide Q B))(M:Male)(x:nomA N Q B)(p:JointB G x e)
variable (C:Op (Single (CSide N B)))
include he hk w p
set_option maxHeartbeats 200000 in
lemma shone (F:Letter ι (Iota G))(D:List ι) : let α:=foal j true M G (unionP x); let β:=wh j L ho true M G (unionP x); let R:=spar j (upMale L ho M) x.2; let V:=ticketT (Thread j) true M G (unionP x); let U:=ticketT (Thread j) false M G (unionP x); let Z:=Kennel.capT α (foot G (A.den x.1)); let H:=traitP β (pine j L ho (Thread j) true M G (unionP x)) V Z; let W:=fruit L j ho G M x Z
 ∀ h:IsStarProjection R,TagG R C → ‖desire L j ho G M x Z‖<1 → TagG R (W-C) ∧
 fire (Thread j) G M (unionP x) (acts (rollC (dialL F) D) (acts (exp (dg Z)) (graft G P x.1 M))) = (Complex.exp (altar G P x M+invoice (desire L j ho G M x Z))) • (acts ((nursery R h).eval (fixT R F.seek (fun i y=>enC F β H V U i (patchQ G y)) (fuelC F β H V U) D)) (acts (exp (dg C)) (acts (exp (dg (W-C))) (changeM P x.2 (upMale L ho M))))):=by
 intro α β R V U Z H W h g k; obtain ⟨a,r⟩:= token he G hk w A M x p C F D g k; constructor
 · exact a
 rw [meantZ]; exact r
end YM.CF.Stilo
