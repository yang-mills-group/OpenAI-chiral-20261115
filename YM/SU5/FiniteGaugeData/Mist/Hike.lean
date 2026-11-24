import YM.SU5.FiniteGaugeData.Mist.Ore
/-! # Pc deletion for the gaps of chronological lists. Consume solely topology on stamps interior,
without any continuation presumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist.Hike
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace
variable {σ T:Type}[Monoid T](F G:σ→T)(A B:σ→σ→ T)
section
variable (p s: List σ)(i j:σ)
lemma split (s:List σ): TapeT F A (p ++ [i] ++ j::s)= (TapeT F A (p++[i])) * A i j * (TapeT F A (j::s)):=by
 induction p with
 | nil=> exact (mul_assoc ..).symm
 | cons x p h=> cases p with
                | nil=> change F x* (A x i*TapeT F A ([i] ++ j::s)) = F x*(A x i*F i)*_*_; simp_rw [show TapeT F A ([i]++j::s)=F i* (A i j*TapeT F A (j::s)) from rfl]; simp [mul_assoc]
                | cons y p=> change F x*(A x y * TapeT F A ((y::p)++[i]++j::s))=(F x*(A x y*TapeT F A ((y::p)++[i])))*_*_; rw [h]; simp [mul_assoc]
lemma same_quil {x:σ} {v:List σ}(h:∀ i∈ x::v,F i=G i)(p:∀ i∈x::v,∀ j∈x::v,A i j=B i j): TapeT F A (x::v)=TapeT G B (x::v):=by
 induction v generalizing x with
 | nil=> exact h _ (by simp)
 | cons i s ih=> exact congrArg₂ (·*·) (h x (by simp)) (congrArg₂ (·*·) (p x (by simp) i (by simp)) (ih (x:=i) (fun j v=> h _ (by simp [v] -- v itself `J.mem`
                                                                                                               )) (fun a v b w=> p a (List.mem_cons_of_mem _ v) b (List.mem_cons_of_mem _ w))))
lemma same_tape (h:∀ i∈ p,F i=G i)(g:∀ i∈p,∀ j∈p,A i j=B i j):TapeT F A p=TapeT G B p:= by cases p with
 | nil=> rfl
 | cons i v=> exact same_quil F G A B h g
-- change ONLY last affect
lemma right_last (u:T)(v:∀ i∈p,G i=F i)(q:G i=F i*u): TapeT G A (p++[i])=TapeT F A (p++[i])*u:= by induction p with
 | nil=> exact q
 | cons x s ih=> cases s with
      | nil=> change G x*(A x i*G i)=(F x*(A x i*F i))*u; rw [v x (by simp),q]; simp [mul_assoc]
      | cons y s=> change G x*(A x y*TapeT G A ((y::s)++[i]))=(F x*(A x y*TapeT F A ((y::s)++[i])))*u; rw [v x (by simp), ih (fun x h=> v x (List.mem_cons_of_mem _ h))]; simp [mul_assoc]
end
section
variable {H:Hilbert}{L:Side}{α:Axis}(P:Terrace H L α)
local notation "R"=> VistaQ L
local notation "E"=> (σ → Carousel L)
open scoped Classical
variable [DecidableEq σ]
-- uniform operation signs. 
abbrev aerate {L:Side}(G:σ→Carousel L)(J:List σ)(a:Axis)(v:VistaQ L)(i:σ):Carousel L:= if i∈J then G i+Pi.single a v else G i
variable (Ω:H.space)(F:σ→ H.Op)(x:σ→Carousel L)
variable (w : σ→List Axis)
abbrev coupes (F:σ→H.Op)(w:σ→List Axis)(i:σ):= F i*planeP (GroupR P (w i))
local notation "R'" w:max=> coupes P F w
variable (Ξ:(σ→Carousel L) → σ → σ → H.Op)
variable (Z:List σ)(hΩ:Ω∈ P.Unity) (hz:Z.Nodup)
abbrev moneyV (x:σ→Carousel L):= inner ℂ Ω (TapeT (R' w) (Ξ x) Z Ω)
abbrev usual (x:σ→Carousel L):= inner ℂ Ω (TapeT F (Ξ x) Z Ω)
abbrev Ideal (P:Terrace H L α)(Z:List σ)(D:Set (σ→Carousel L)): Prop:= ∀ x∈D, moneyV P Ω F w Ξ Z x=usual Ω F Ξ Z x
local notation "J" x:max=>Ξ x
#check Ideal
-- deletion tool only needs for every active b (b≠time) shifting suffix in P clock. use relative stamps predicate.
structure Flu (D:Set (σ→Carousel L)) (C:Axis→Prop):Prop where
    cont (x:σ→Carousel L)(h:x∈D)(b)(p:C b)(K:List σ) : ∀ᶠ v:VistaQ L in 𝓝 0,aerate x K b v ∈D
    awake (x:σ→Carousel L)(h:x∈D)(b)(p:C b)(K:List σ): Tendsto (fun v:VistaQ L=>usual Ω F Ξ Z (aerate x K b v)) (𝓝 0) (𝓝 (usual Ω F Ξ Z x))
    relative (x y:σ→Carousel L)(i j:σ): x j-x i=y j-y i→ Ξ x i j= Ξ y i j
    tug (x y:σ→Carousel L)(i j:σ)(v:VistaQ L)(b:Axis)(p:C b)(u:b≠α): y j-y i = x j-x i+ Pi.single b v → Ξ y i j= (ramble P b v) * Ξ x i j
variable {D:Set (σ→Carousel L)} {C:Axis→Prop}
#check Flu
lemma time_id (w:List Axis) : planeP (GroupR P (α::w))=planeP (GroupR P w):=by
    have he:Stamina P α=⊤:= SetLike.ext' (Set.eq_univ_of_forall (fun x=>by change Tendsto _ _ _; exact (tendsto_const_nhds (x:=x)).congr' (Eventually.of_forall (fun t=> DFunLike.congr_fun (ramble_self P t).symm x)))) -- may infer
    rw [GroupR,he,inf_top_eq]
lemma widget (v:List Axis)(b:Axis): planeP (GroupR P (b::v))=planeP (GroupR P v)*planeP (Stamina P b):=by rw [GroupR,infP]; exact (comm_Group P v (A:=planeP _) (fun a=> desk_nick P b a)).symm -- argument A?
-- projector test: continuous scalar clip
lemma vocable {L:Side}(P:Terrace H L α)(v x:H)(b:Axis)(g:H.Op)(p:Tendsto (fun t:VistaQ L=>inner ℂ x (g (ramble P b t v))) (𝓝 0) (𝓝 (inner ℂ x (g v)))) : inner ℂ x (g (planeP (Stamina P b) v))=inner ℂ x (g v):=by
    let U:=(ScrollQ P b); let f:H→L[ℂ]ℂ:=(innerSL ℂ x).comp g
    change Tendsto (fun t:VistaQ L=> f (U.U t v)) _ (𝓝 (f v)) at p
    apply dist_eq_zero.mp; refine le_antisymm ?_ dist_nonneg; refine le_of_forall_gt_imp_ge_of_dense fun ε h=> ?_; obtain ⟨n,t,c⟩:= Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp p ε h)
    let ℍ:= Set.preimage f (closedBall (f v) ε); apply closure_minimal (t:=ℍ) ?_ (isClosed_closedBall.preimage f.continuous) (U.immersion v n t)
    intro z w; change U.Gem v n z at w; induction w with
    | glide s p=> exact (show dist (f (U.U s v)) _ < ε from c (show s∈ball 0 n from Metric.mem_ball.mpr (by simpa using p))).le
    | mount x y a b u v' t ih ig=>
         change f _∈closedBall _ _; rw [map_add,map_smul,map_smul]; apply convex_closedBall _ _ ih ig u v' t -- R vs C
variable (M:Flu P Ω F Ξ Z D C)
local notation "P₀" w:max=> Ideal Ω F w Ξ P Z D
include hΩ hz M
private lemma hike (i:σ)(b:Axis)(v:C b)(hw:Ideal Ω F w Ξ P Z D): Ideal Ω F (Function.update w i (b::w i)) Ξ P Z D:=by
    let u:=R' w; let w':=Function.update w i (b::w i); let t:=R' w'; let G:=planeP (Stamina P b)
    have hy(j:σ)(e:i≠j): u j=t j:=by unfold u t coupes w'; rw [Function.update_of_ne e.symm]
    have hx: t i=u i*G:=by unfold u t w' G coupes; rw [Function.update_self,widget,←mul_assoc]
    intro x p; rw [← hw x p]; change inner ℂ Ω (TapeT t (J x) Z Ω)=inner ℂ Ω (TapeT u (J x) Z Ω)
    by_cases nm:i∈Z; swap; · rw [same_tape t u (J x) _ Z (fun j hj=> (hy j (fun e=>nm (e.symm ▸ hj))).symm) (fun _ _ _ _=>rfl)] -- shadow! dsnippets
    obtain ⟨K,A',eq⟩:= List.append_of_mem nm
    -- eq orientation
    subst Z
    let y:=K++[i]
    have hl:i∈ y:=List.mem_append_right _ (by simp)
    have he: i∉K:= fun p=> hz.disjoint p (show i∈i::A' from by simp)
    have hD:y.Disjoint A':= (show List.Nodup (y++A') from by simpa [y] using hz).disjoint
    let A:=J x; let M':=TapeT u A y; let m:=TapeT u A A'
    have ht: TapeT t A y=M'*G:= right_last u t A K i G (fun x p=> (hy x (fun v=> he (v.symm ▸ p))).symm) hx
    have hm:TapeT t A A'=m:= same_tape t u _ _ A' (fun j h=> (hy j (fun w=> hD hl (w.symm ▸ h))).symm) (fun _ _ _ _=>rfl)
    cases A' with
    | nil=> -- simplifies K++i::nil
       have hl: G Ω=Ω:=inlet (show Ω∈ Stamina P b from (sting P [b] _).1 (include_unity _ [b] hΩ) b (by simp)); change inner ℂ Ω (TapeT t A y Ω)= _; rw [ht,mul_apply_eq_comp,hl]
    | cons j Z=>
       let K':=j::Z
       let L':=A i j (TapeT u A K' Ω); change List.Disjoint y K' at hD; have hp(l:σ)(e:l∈y):l∉K':= hD e
       have hs(z:σ→H.Op)(x:σ→Carousel L): TapeT z (J x) (K ++ i :: j :: Z)= TapeT z (J x) y * (Ξ x i j) * TapeT z (J x) K':=by rw [show K++i::j::Z=y++K' from by simp [y,K']]; exact Hike.split ..
       suffices hv: inner ℂ Ω (M' (G L'))= inner ℂ Ω (M' L') by rw [hs,hs]; exact (by change inner ℂ Ω ((TapeT t A y*A i j*TapeT t A K') Ω)=_; rw [ht,hm]; exact hv)
       by_cases hy:b=α; · subst b; have hh: G Ω=Ω:=inlet ((sting P [α] _).1 (include_unity _ _ hΩ) _ (by simp)); -- instead simplify P_b=1 at L'
                          have hx:G L'=L':=inlet (show L'∈Stamina P α from (tendsto_const_nhds (x:=L')).congr' (Eventually.of_forall (fun t=>DFunLike.congr_fun (ramble_self P t).symm L'))); rw [hx]
       apply vocable (P:=P) L' Ω b M'
       let ℤ':=K++i::j::Z; let f(x:σ→Carousel L):=usual Ω F Ξ (K++i::j::Z) x; have hZ:inner ℂ Ω (M' L')=f x:= Eq.trans (congrArg (fun f:H.Op=>inner ℂ Ω (f Ω)) (hs u x).symm) (hw x p) -- defeq
       refine (show Tendsto (fun t=>f (aerate x K' b t)) (𝓝 0) (𝓝 (inner ℂ Ω (M' L'))) from hZ ▸ M.awake x p b v K').congr' ?_
       filter_upwards [M.cont x p b v K'] with s p; let x':=aerate x K' b s
       refine Eq.trans (hw x' p).symm ?_; change inner ℂ Ω (TapeT u (Ξ x') ℤ' Ω)= _; unfold ℤ'; rw [hs]
       have hp': j∈ K':=by simp [K']
       have ht:TapeT u (Ξ x') y=M':= same_tape _ _ _ _ _ (fun _ _=>rfl) (fun i h j v=> M.relative _ _ i j (by simp [x',aerate,hp i h, hp j v]))
       have ht':TapeT u (Ξ x') K'=m:= same_tape _ _ _ _ _ (fun _ _=>rfl) (fun i h j v=> M.relative _ _ i j (by simp [x',aerate,h,v]))
       have hx:Ξ x' i j= ramble P b s * Ξ x i j:= M.tug _ _ _ _ s b v hy (by unfold x' aerate; rw [if_pos hp',if_neg (hp _ hl)]; abel)
       rw [ht,ht',hx]; rfl
-- build purchases for ALL indices at once with choices.Bridge
private lemma descent (Q:List σ)(G:Axis)(v:C G) (hw:Ideal Ω F w Ξ P Z D):∃ w', Ideal Ω F w' Ξ P Z D∧∀ x,w' x=if x∈Q then G::w x else w x:=by
 induction Q with
 | nil=> exact ⟨w,hw,fun i=>by simp⟩
 | cons i y ih=>
                  by_cases h:i∈ y
                  · obtain ⟨w',p,t⟩:=ih; exact ⟨w',p,fun j=> (t j).trans (ite_congr (by simpa using (or_iff_right_of_imp (fun (hj:j=i)=> hj.symm ▸ h)).symm) (fun _=>rfl) (fun _=>rfl))⟩
                  obtain ⟨w',p,t⟩:=ih; refine ⟨_,hike P Ω F w' Ξ Z hΩ hz M i G v p,fun x=> ?_ ⟩; by_cases e:x=i; · subst x; simp [t,h]
                  rw [Function.update_of_ne e,t]; simp [e]
omit hΩ hz M in
private lemma dupe (w':σ→List Axis)(p:∀ x∈ Z,w x=w' x) : moneyV P Ω F w Ξ Z x= moneyV P Ω F w' Ξ Z x:= Eq.trans (congrArg (fun f:H.Op=>inner ℂ Ω (f Ω)) (same_tape _ _ _ _ Z (fun i h=>congrArg (fun v=> F i * planeP (GroupR P v)) (p i h)) (fun _ _ _ _=>rfl))) rfl -- add variable w'
theorem trek (B:List Axis)(u:∀ b∈ B,C b) : Ideal Ω F (fun _=> B) Ξ P Z D:= by induction B with
 | nil=>
    intro x p; have he: coupes P F (fun _=>[])=F:=funext fun i=>by unfold coupes; rw [seat_group]; simp
    unfold moneyV; rw [he]
 | cons b q ih=>
    obtain ⟨w,p,t⟩:= descent P Ω F (fun _=> q) Ξ Z hΩ hz M Z b (u _ (by simp)) (ih (fun i v=> u i (List.mem_cons_of_mem _ v)))
    intro x u; exact (dupe P Ω F x _ Ξ Z w (fun i v=> by rw [t i,if_pos v])).trans (p x u)
#print axioms trek
end
variable {H:Hilbert}(Q:ClosedSubmodule ℂ H)(Ω:H.space)(F:σ→ H.Op)(A:σ→σ→H.Op)(Z:List σ)
variable (p:∀ i j,Commute (A i j) (planeP Q))
lemma commute_short {L:H.Op}(p:Commute L (planeP Q)) : social Q L=social Q (planeP Q*L):=by
 ext1; rename_i x; rw [← p.eq]; let z:=(cpo Q x); change dip Q (L z)=dip Q (L (planeP Q z)); rw [inlet (show z∈Q from among x)]
local notation "C"=> planeP Q
include p
lemma social_chain : social Q (TapeT (fun i=>F i *(C)) A Z) =TapeT (fun i=> social Q (F i)) (fun i j=>social Q (A i j)) Z:=by
 cases Z with
 | nil=> exact social_id
 | cons i Z=> induction Z generalizing i with
    | nil=> apply ContinuousLinearMap.ext; intro x; change dip Q (F i (planeP Q (cpo Q x)))=dip Q (F i (cpo Q x)); rw [inlet (show cpo Q x∈Q from among x)]
    | cons j Z ih=>
       let U:= TapeT (fun i=> F i*C) A (j::Z); change social Q ((F i * C) * (A i j * U))= _
       rw [social_mul, Cot.citizen (p i j)]
       change _*(_*social Q U)=(social Q (F i))*(social Q (A i j)* _); rw [show social Q U=_ from ih j]; rfl
lemma social_chain_price (u:Ω∈Q) : inner ℂ Ω (TapeT (fun i=> F i*C) A Z Ω)=inner ℂ (dip Q Ω) (TapeT (fun i=> social Q (F i)) (fun i j=>social Q (A i j)) Z (dip Q Ω)) :=by rw [←social_chain Q F A Z p,sightS, castC,inlet u]
end YM.CF.Buffered.Afterglow.Hierarchy.Mist.Hike
