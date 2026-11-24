import YM.CF.Maize.Art
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
abbrev Fo (B:Side)(e U:ℝ)(n:ℕ)(T:Briar m B e→ Ewe m B)(H w:ℝ): Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](f:E→ Briar m B e)(S:Set E),IsOpen S→ (∀ x∈ S,TransK n (fun i=>(f i).val) x U) →∀ x∈ S, Allows n (fun x=>Gas.dilF H (T (f x))) x w
private lemma κK : ∃ (a b K:ℝ),0<a∧0<b∧0≤K∧∀ i:IndexK,∃ F C,Spends (ku (a:=b) (N:=i.1)) F C a K ∧ (∀ S,Looks _ (F S))∧∀ p:0<b,∀ x:Own i.1, (Kmat i x * Pmat i x).trace=∑ S:Seal (Site (More i.1)), Shove p F S x:=by
 obtain ⟨a,b,h,v,p,l,H⟩:= LedgerP.times μLp σLp; refine ⟨a/2,b,vane a h,half_pos v,p,?_,fun i=>?_⟩ -- tune
 · unfold Floe.vane; refine mul_nonneg (tsum_nonneg ?_) l.le; intro i; unfold quota; positivity
 obtain ⟨F,C,L,g,x⟩:=seeP H v i; refine ⟨F,C,L,g,fun s x' =>?_⟩; have he:= x (uθ x' s); change Matrix.trace (_*_)=_ at he; rw [mass_j,comp_j] at he; exact he
-- combined jet and Token stem certificate on payment set
structure CoInk (S:Acres m) (e H:ℝ)(p:1 ≤ H)(U:ℝ)(n:ℕ)(F:Briar m B e→Ewe m B)(w:ℝ) :Prop where
 home:Token (welter m B e H p) S F w (Grove (terr _))
 growth : Fo (m:=m) B e U n F H w
abbrev coBooks (e U H:ℝ)(p:1≤ H)(n:ℕ)(F:Briar m B e→Ewe m B)(a c:ℝ):= ∃ (T: Acres m→Briar m B e→ Ewe m B) (w:Acres m→ℝ),(∀ i,CoInk i e H p U n (T i) (w i)) ∧ (∀ i,hitE a w i≤ c)∧∀ i,F i=∑ z:Acres m,T z i
lemma groupT {T:Type}[Fintype T]{R:T→Acres m}{p:1≤H}{F:Briar m B e→ Ewe m B}{Y:T→ Briar m B e→Ewe m B}{w:T→ℝ}
 (h:∀ i,CoInk (R i) e H p U n (Y i) (w i)) (t:∀ i,hitE r (fun S=>∑ i∈dest R S,w i) i ≤ K) (u:∀ i,F i=∑ z:T,Y z i):coBooks e U H p n F r K:=by
 let Z(i:Acres m) (x:Briar m B e):=∑ j∈dest R i,Y j x; refine ⟨Z,_,fun i=>⟨Token.mass _ _ _ (fun j (u:j∈dest R i)=>((mem_filter.mp u).2: R j=i) ▸ (h j).home),?_⟩,t,fun i=> (u i).trans (lump R (fun S=> Y S i))⟩
 intro E _ _ _ f S k l x hx; simp only [Z,map_sum]; exact allows_sum (s:=dest R i) (fun j _=>(h j).growth E f S k l x hx) -- tune
lemma token_e {p:1≤H}{f:Briar m B e→ℂ}{S:Acres m}(g:Token (moneyW m B e) S f r (Grove (terr _))) {w:ℝ}(q:r≤w)(t:w ≠ 0 → r ≠ 0): Token (welter m B e H p) S (fun i=>hollow (n:=Hearth m B) (f i)) w (Grove (terr _)):=by
 refine ⟨g.price.trans q,fun w=>g.shape (t w),fun i=>?_,fun p=> congrArg _ (g.locality p), fun i=>?_, scalarC.comp g.ct,fun j x=>?_⟩ -- ct ambiguity
 · exact (stretch_ok ..).mpr (Flour.grainE.smul _) -- tune
 · exact (hollow_cost ..).trans_le ((g.owns i).trans q)
 rw [show (welter m B e H p).rule j (hollow _)=_ from route_s j _]; exact congrArg _ (g.dress j x)
private lemma toot {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{F:E→ℂ}{I:Type}[LinearOrder I][Fintype I](p:Allows n F x K)(h:0≤H): Allows n (fun i=>dilF H (hollow (n:=I) (F i))) x K:=by rw [←one_mul K]; change Allows _ (fun i=>Maize.bark I H (F i)) x _; refine Allows.linear (G:=Dough I) _ p ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; exact mintB h I
lemma coin_s (n:ℕ)(l:1≤ U)(b:0<r):∃ J:ℕ,∀ B:Side,J≤B.val→∃ C:ℝ,0≤C∧∀ (m:Side)(e H:ℝ)(p:1≤H)(d:Room B e)(W:Foot m B), coBooks (m:=m) (B:=B) e U H p n (fun x=>hollow (energ m B W x.val)) r C:=by
 obtain ⟨a,s,C,hA,hs,g,V⟩:= κK; let k:=2*r; have hk:0<k:=(by positivity); obtain ⟨J,h⟩:= exists_nat_gt (k*21^4/a)
 refine ⟨J,fun B u=>?_⟩
 obtain ⟨K,z,w⟩:=brimA n hs l B; obtain ⟨D,y,t⟩:=ryth n U B l; obtain ⟨R,hR,hF⟩:=stash D y n hk
 let C' := Real.exp (k*21^4)*(16*(7*(B.val:ℝ)+1)^4*C); refine ⟨(R*K+1)*C',by unfold C'; positivity,fun m e H v d f=>?_⟩
 let T:= Treasury m B e; let i:=codify (m:=m) (B:=B) f; obtain ⟨L,Q,x1,u',P⟩:=V i; let X:= Shove hs L; have he:= shoves (p:=hs) x1; let Y(S:Stamp m B):= cin (e:=e) m B (X S); let E'(S:Stamp m B):= motor T (Y S); have hy(S:Stamp m B) : Manifest T (Y S) (Q S) (pavilion m B S) (chairs m B S):=cin_paid (he.stamped _) d
 let W(S:Stamp m B):= mercury (chairs m B S).card n D (K*Q S)+Q S
 refine groupT (R:=pavilion m B) (Y:=fun S (x:Briar m B e)=> hollow (n:=Hearth m B) (E' S x)) (w:=W) (fun S=>?_ ) (fun i=>?_ ) (fun x=>?_) -- tune
 · have ht:=hy S; have hC:0≤ mercury (chairs m B S).card n D (K*Q S):= (mul_nonneg z ht.price).trans (bigger n _ (mul_nonneg z ht.price) y)
   refine ⟨token_e {(ht.flush) with shape:= fun z=>pad_grove (m:=m) (B:=B) ((he.stamped _).conduct z)} (le_add_of_nonneg_left hC) (fun p s=>p (by simp [W,s,mercury])),?_⟩
   intro E _ _ _ F U' o G x g; apply toot _ (zero_le_one.trans v); let p(j:E):= (T.seat ∘ F) j; have hp:FireK U' p D n:=t m E U' o (fun i=>(F i).val) G
   refine (waitB hp (fun i t=>Y S (F i,t)) (chairs m B S) (fun i _=> ht.records (F i)) (fun i j v z=>?_) (mul_nonneg z ht.price) (fun i _ u v g l s=>ht.localise _ _ _ s g l) (fun i _=> ht.cashG _) x g).mono (le_add_of_nonneg_right ht.price)
   let Q':= slot m i; let V'(k:E):= release (F k,i); have hU:=u' S; obtain ⟨_,_,_,G',p',w'⟩:=x1.stamped S -- x shadow
   have hz: stick (0:Row)∈Phase.zone {0}:=stick_in _ (mem_singleton_self _)
   refine w E m (L S) hU G' _ p' (fun k=> (F k).val) (fun _=>Q') _ _ none j e {0} hz hz (by rw [sub_self,norm_zero]; positivity) d (G _ v) (fun k=> voteR i l j k.1) ?_
   filter_upwards [o.mem_nhds v,(fire_num hp v _ i).continuousAt.eventually_ne z] with j v l; let c : Train m B e:= (F j,i); have hl : (F j,i)∈Breath m B e:= l; exact (show release c ∈ payer m B e from pays (m:=m) (B:=B) hl)
 · have hh:k*21^4≤a*(B.val:ℝ):=(le_of_lt ((div_lt_iff₀ hA).mp h)).trans (by rw [mul_comm];exact mul_le_mul_of_nonneg_left (by exact_mod_cast u) hA.le)
   have hv:= hit_transfer (m:=m) (v:=Q) hk.le hh (fun S c=> (he.stamped S).conduct c) (fun S=>(he.stamped S).posT) he.payline g i -- tune
   rw [codify_hit]; apply le_trans _ (mul_le_mul_of_nonneg_left hv (show 0≤R*K+1 by positivity)); unfold cellHit spotHit; rw [mul_sum]; refine sum_le_sum fun i hi=> ?_
   let F:= pavilion m B i; have hp:= hF (K*Q i) (mul_nonneg z (hy i).price) _ _ (card_le_card (chair_pad (S:=i)))
   rw [show k/2=r by unfold k; ring] at hp
   unfold W; rw [mul_add,add_mul,one_mul]; refine add_le_add (hp.trans (le_of_eq ?_)) (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hy i).price)
   · unfold rent; ring
   apply mul_le_mul_of_nonneg_right (show r ≤ k by unfold k; linarith) (Nat.cast_nonneg _)
 · rw [hollow_sum]; apply congrArg; symm
   have ht z' (v' : (x,z')∈Breath m B e) : ∑ S:Stamp m B,Y S (x,z')=energ m B f x.val:= by
     let y : Train m B e:= (x,z'); have hx := tenant_t d v'; unfold Y cin; simp_rw [entrance (p:=stick 0) (q:=stick 0) (m:=m) (B:=B) (v:=none) hx]; exact (P hs (⟨_,hx⟩:Post m B)).symm
   change ∑ S:Stamp m B, (∫ i, law m B x.val i • Y S (x,i) ∂rains m)=energ m B f x.val; rw [←integral_finsetSum _ (fun i _=> net_compact (show Continuous (fun z=>law m B x.val z • Y i (x,z)) from (hy i).cashG x))]; simp_rw [←smul_sum]; let G:= energ m B f x.val
   apply Eq.trans (b:=∫ i,law m B x.val i • G ∂rains m) (integral_congr_ae ?_) ?_
   · apply Eventually.of_forall; intro i; by_cases hy:law m B x.val i=0; · exact (show law m B x.val i • (∑ S:Stamp m B,Y S (x,i))=law m B x.val i • G from by rw [hy]; exact (zero_smul ..).trans (zero_smul ..).symm)
     exact congrArg (fun v:ℂ=> law m B x.val i • v) (ht i (show (x,i)∈Breath m B e from hy))
   rw [integral_smul_const,rain_law,one_smul]
end YM.CF.Gully
