import YM.SU5.WakeFields.FootLights
--! clustering of all (primary,00) tariff formulas. no self-distinctness needed for this algebra.
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
open Function Filter Metric Cube Lat Lattice Satin Fock Finset MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Classical
open Py Py.Rate LocalLimit FullBill Preparation Yoke Yoke.Shuttle
open Lifted EmberWind EmberWind.Staff EmberWind.MixedCards MixedCards.Receipt
open Papal (household)
open Regis.Head.Brecht Regis.Circuit
open Ballad
open Hiro.Crossing (Story)
open Jewel
open YM.Stationary (Gaia)
open YM.WakeFields
attribute [local instance] opCStarAlgebra
local notation "z" => (3:Axis)
local notation "Z" => P.calibration
local notation "Jus" => SU.group.ColorIndex
local notation "Tc" => MixedCards.Ticket
local notation "ƒ" => Resolving.primary
local notation "₲" => Spine.pairMood
variable {J K : Type*} (L : List J) (D:J→MixedCards.Ticket) (F:Receipt.Deck J→Story J→ℂ)(G:Receipt.Deck J) (H: Story J)
abbrev rG (f:J→ K) : materialL J→materialL K := fun i=> (f i.1,i.2)
abbrev rH (f:J→ K) : Twah.Stamp J→ Twah.Stamp K:= fun i=> (f i.1,i.2)
lemma cue_more (V:List J): cue D F (L++V) G H= cue D (fun G H=> cue D F V G H) L G H:= by
 induction L generalizing G H with
 | nil=> rfl -- defeq? cue well rec
 | cons i L ih=> cases t:D i with|some a=> rw [List.cons_append,payPure _ _ _ _ t,payPure _ _ _ _ t]; simp_rw [ih]| none=> rw [List.cons_append,payMix _ _ _ _ t, payMix _ _ _ _ t]; simp_rw [ih]
lemma cues (A:K→ Tc) (F:Receipt.Deck K→ Story K→ℂ)(f:J→ K) (g:Receipt.Deck K)(u: Story K) : cue A F (L.map f) (g++ G.map (rG f)) (u ++ H.map (rH f)) = cue (A ∘ f) (fun G H=> F (g++ G.map (rG f)) (u ++ H.map (rH f))) L G H:=by
 induction L generalizing G H with
 | nil=> rfl
 | cons i L ih=>
    cases t:A (f i) with
    | some a=> rw [List.map_cons,payPure _ _ _ _ t, payPure _ _ _ _ (show (A∘f) i=some a from t)]; apply sum_congr rfl; intro v _; rw [←ih, with2, with2,List.map_append,List.append_assoc]; rfl
    | none=> rw [List.map_cons,payMix _ _ _ _ t, payMix _ _ _ _ (show (A∘f) i=none from t)]; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; -- tune list lengths
             rw [←ih,with2,with2]; simp only [List.map_append,List.append_assoc]; rfl
lemma cue_scale (r:ℂ): cue D (fun G H=> r*F G H) L G H=r*cue D F L G H:=by
 induction L generalizing G H with
 | nil=> rfl
 | cons i L ih=>
    cases t:D i with
    | some a=> rw [payPure _ _ _ _ t,payPure _ _ _ _ t]; simp_rw [ih,mul_sum,mul_left_comm (1/16:ℂ) r]
    | none=> rw [payMix _ _ _ _ t,payMix _ _ _ _ t]; simp_rw [ih,mul_sum,mul_left_comm (dyeC _ _ _) r]
-- price split
abbrev CS (J : Type*) := materialL J → materialL J → ℂ
abbrev PS (J : Type*) := Twah.Stamp J → Twah.Stamp J → ℂ
variable {m:List K} {Q:Type*} (A:Q→ Tc)
variable (p:J→ Q) (q:K→ Q) (x:CS Q)(y:PS Q)
def fetch {I I': Type*}(x:I→ I→ℂ)(f:I'→ I) (u v:I'):= x (f u) (f v)
lemma reap_rows (c:∀ i j,x (rG p i) (rG q j)=0)(d:∀ i j, y (rH p i) (rH q j)=0) (m:List K):
  bus (L.map p ++ m.map q) A [] [] x y= bus L (A ∘ p) [] [] (fetch x (rG p)) (fetch y (rH p)) * bus m (A∘q) [] [] (fetch x (rG q)) (fetch y (rH q)):= by
 let a:=A∘p; let b:=A∘q; let F (G: Receipt.Deck Q)(H: Story Q):= Ferro.ledger x G * Emu.runes y H
 let X (G:Receipt.Deck J)(H:Story J):= Ferro.ledger (fetch x (rG p)) G*Emu.runes (fetch y (rH p)) H; let Y (G:Receipt.Deck K)(H:Story K):= Ferro.ledger (fetch x (rG q)) G * Emu.runes (fetch y (rH q)) H
 have h(g:Receipt.Deck J)(k:Receipt.Deck K)(u:Story J)(v:Story K): F (g.map (rG p)++k.map (rG q)) (u.map (rH p)++v.map (rH q))= X g u * Y k v:=by
    unfold F X Y; rw [Ferro.distinct_earn x _ _ ?_ _ le_rfl, WakeInvestment.rune_divide y _ _ ?_]; swap
    · intro i l j t; rcases List.mem_map.mp l with ⟨i,_,rfl⟩; rcases List.mem_map.mp t with ⟨j,_,rfl⟩; exact d i j
    swap; · intro i l j t; rcases List.mem_map.mp l with ⟨i,_,rfl⟩; rcases List.mem_map.mp t with ⟨j,_,rfl⟩; exact c i j
    rw [←Ferro.faces (fetch x (rG p)) g x _ (fun i j=>rfl) _ le_rfl,←Ferro.faces (fetch x (rG q)) k x _ (fun i j=>rfl) _ le_rfl,
            WakeInvestment.rune_map (fetch y (rH p)) u _ y (fun i j=>rfl), WakeInvestment.rune_map (fetch y (rH q)) v _ y (fun i j=>rfl)]
    ring
 let P':= cue b Y m [] []
 have hc(g:Receipt.Deck J)(u:Story J): cue A F (m.map q) (g.map (rG p)) (u.map (rH p)) = P'* X g u:=by
    let he:=cues m ([]:Receipt.Deck K) ([]: Story K) A F q (g.map (rG p)) (u.map (rH p))
    simp_rw [List.map_nil,List.append_nil,h] at he -- maybe rw destroys h inside if? 
    rw [he,cue_scale]; exact mul_comm ..
 change cue A F (L.map p ++ m.map q) [] []= cue a X L [] []*P'
 rw [cue_more]; let he:=cues L [] [] A (fun g h=>cue A F (m.map q) g h) p [] []; simp_rw [List.nil_append,List.map_nil,hc] at he; rw [he,cue_scale]; exact mul_comm ..

abbrev ledge (u : J→ Gaia) : CS J:= valueHue (fun _=> Resolving.primary) u
abbrev noteP (u:J→ Gaia) : PS J:= valueSpin (fun _=> Spine.pairMood) u
abbrev plaque (u:J→Gaia) := tariff L D (fun _=> Resolving.primary) (fun _=> Spine.pairMood) u u
variable (u v:J→ Gaia) (t:∀ i j,u i-u j=v i-v j)
include t
lemma equalC : ledge u=ledge v:=funext fun i=> funext fun j=> by change _ * specter ƒ ƒ _=_ * specter ƒ ƒ _; rw [t]
lemma equalP : noteP u=noteP v:=funext fun i=> funext fun j=>by unfold noteP valueSpin Twah.germRho; simp_rw [comp_apply,t]
lemma ident : plaque L D u=plaque L D v:=by change bus L D [] [] (ledge u) (noteP u)= bus L D [] [] (ledge v) (noteP v); rw [equalC u v t,equalP u v t]
omit t
-- For any far layout sequence. First Maxwell fades. To avoid algebra bound just fix first pair components; applies when along this primary F and time shifts. Can't use µ at the coincident limit; this is far.
lemma fadeGauge (t:ℕ → Gaia)(p:Tendsto (fun i=>‖t i‖) atTop atTop)(x y:ℝ)(h:∀ i,t i 0=x)(e:∀ i,t i 1=y):
        Tendsto (fun i=> specter ƒ ƒ (t i)) atTop (𝓝 0) := by
 let u (i:ℕ):=(‖t i‖^2)⁻¹
 have he:Tendsto u atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (p.atTop_mul_atTop₀ p |>.congr fun i=> by rw [sq]) -- lemma tune
 let D' := Maxwell.normal
 let L' (x:ℝ) (i:ℕ) := -2 * D' * u i^2 + 8* D' * (x*x) * u i ^3
 have hv(x:ℝ): Tendsto (L' x) atTop (𝓝 0) := by simpa only [zero_pow (by decide : 2≠0), zero_pow (by decide : 3≠0), mul_zero,add_zero] using (((he.pow 2).const_mul (-2*D')).add ((he.pow 3).const_mul (8*D'*(x*x))))
 have ht := ((hv x).neg.sub (hv y)); rw [neg_zero,sub_zero] at ht
 have hc:Tendsto (fun i=> (↑(-L' x i-L' y i):ℂ)) atTop (𝓝 0):= (by simpa only [comp_def,Complex.ofReal_zero] using (Complex.continuous_ofReal.continuousAt.tendsto.comp ht))
 apply hc.congr'; filter_upwards [p.eventually_gt_atTop 0] with i v; let g:t i≠0:=norm_pos_iff.mp v
 apply congrArg (fun (z':ℝ)=>(z':ℂ)); unfold Maxwell.bareCurl; rw [Pi.sub_apply,Maxwell.Bare.opp_grad g,Maxwell.Bare.opp_grad g]; norm_num [show (ƒ).val.1=0 from rfl,show (ƒ).val.2=1 from rfl, ↓reduceIte,Maxwell.second_Green g, YM.basis_eq, h, e]; unfold L' u D'; ring -- tune
#print axioms reap_rows
#print axioms fadeGauge
open CrossMoment Emu
lemma spins_far (F:ℕ→J→ Gaia)(p q:Twah.Stamp J)(g:Tendsto (fun n=> dist (F n p.1) (F n q.1)) atTop atTop) :
    Tendsto (fun n=> noteP (F n) p q) atTop (𝓝 0) := by
  let K:J→Twah.DirSpin:=fun _=> Spine.pairMood; let N (n):=valueSpin K (F n); let E (n):=CrossMoment.pen K (F n)
  have h (p q:J)(v:Tendsto (fun n=> dist (F n p) (F n q)) atTop atTop) : Tendsto (fun n=> E n p q) atTop (𝓝 0) := by
    have he: Tendsto (fun i=>‖F i p-F i q‖) atTop atTop:=v.congr fun i=>dist_eq_norm _ _
    have hv:= SpinReceipt.kP_further _ he; change Tendsto (fun i=>PPrice (F i p - F i q)) _ _; unfold PPrice; simpa only [mul_zero] using hv.const_mul (8:ℂ)
  -- story_t has [Fintype J] auto unused; omit proof uses Germ formula directly via funds. Here NO Fintype J.
  obtain ⟨p,x,a⟩:=p; obtain ⟨q,y,b⟩:=q
  change Tendsto (fun n=> N n _ _) _ _; unfold N; cases a <;> cases b
  all_goals simp only [valueSpin, Cordial.funds_neg,Cordial.funds,Cordial.dcash,mul_zero,mul_neg,mul_ite] -- fund orientation
  all_goals first| exact tendsto_const_nhds|skip
  · split; next w=> simpa only [neg_zero] using (h q p (g.congr fun i=> dist_comm ..)).neg
    next w=> simpa only [neg_zero] using (tendsto_const_nhds (x:=(0:ℂ)))
  split; exact h p q g; exact tendsto_const_nhds

local notation "ιl" => Sum.inl (β:=K)
local notation "ιr" => Sum.inr (α:=J)
def parallelB {α : Type*} (f:J×α→ J×α→ℂ)(g:K×α→ K×α→ℂ) (x y: (J⊕K) ×α) := match x.1,y.1 with
 | Sum.inl i,Sum.inl j => f (i,x.2) (j,y.2) | Sum.inr i,Sum.inr j=>g (i,x.2) (j,y.2)|_,_=>0

variable [Fintype J][Fintype K] (P:Preparation)
variable (t:K→ Tc)(v: K→ Gaia)(m:List K)
abbrev pathUp (u:J→Gaia) (P:Preparation)(n:ℕ) (i:J):= gait P (u i) n
-- easier within-sector projection theorem pointwise
abbrev Rosters (u:J→ Gaia)(v:K→ Gaia)(P:Preparation)(n:ℕ) := Sum.elim (Shuttle.opposite ∘ pathUp u P n) (pathUp v P n)
lemma linkHue (f:J→ Q)(v:J→ Gaia)(G:Q→ Gaia)(u:∀ i j,G (f i)-G (f j)=v i-v j):
     fetch (ledge G) (rG f) = ledge v := by funext i j; unfold fetch ledge valueHue; rw [show G _-G _= _ from (u i.1 j.1)]
lemma linkSpin (f:J→ Q)(v:J→ Gaia)(G:Q→ Gaia)(u:∀ i j,G (f i)-G (f j)=v i-v j) :
     fetch (noteP G) (rH f) = noteP v := by
     funext ⟨i,a,b⟩ ⟨j,c,d⟩; unfold fetch noteP valueSpin Twah.germRho
     simp only [Twah.pilotS,rH,Twah.colbase,comp_apply,u]

-- pay gauge cross component (all tariff entries) with spoke_move exactly at coordinates.
lemma tariffs_unroll : Tendsto (fun n:ℕ=> plaque (L.map Sum.inl ++ m.map Sum.inr) (Sum.elim D t) (Rosters u v P n)) atTop
     (𝓝 (plaque L D (Shuttle.opposite ∘ u) * plaque m t v)) := by
  let f : J→ _ := ιl; let q: K→ _ := ιr; let D' := Sum.elim D t; let A':= L.map f ++ m.map q
  let U := u; let V := Shuttle.opposite ∘ u; let G:= Rosters u v P; let S (n:ℕ):= noteP (G n); let T (n:ℕ):= ledge (G n)
  have E(n)(i j:J): G n (f i) - G n (f j)= V i - V j:= by change opposite (gait _ _ n) - opposite (gait _ _ n) = Shuttle.opposite _ - opposite _; rw [flip_d,flip_d,gait_d]
  have e(n)(i j:K): G n (q i)-G n (q j)=v i-v j:= gait_d _ n (v i) (v j)
  have p(n): fetch (T n) (rG f)=ledge V:= linkHue f V _ (E n)
  have h₁(n): fetch (T n) (rG q)=ledge v:= linkHue q v _ (e n)
  have p'(n): fetch (S n) (rH f)=noteP V:= linkSpin f V _ (E n)
  have h₂(n): fetch (S n) (rH q)=noteP v:= linkSpin q v _ (e n)
  let Pf: CS (J⊕K) := parallelB (ledge V) (ledge v)
  let Sf: PS (J⊕K) := parallelB (noteP V) (noteP v)
  have u'(i j): Tendsto (fun n:ℕ=> dist (G n (f i)) (G n (q j))) atTop atTop:= foreign P (u i) (v j)
  have v' (i: J)(j: K)(a:Axis)(h:a≠(3:Axis)) (n): (G n (f i)-G n (q j)) a=u i a-v j a:=by
     change _=_; rw [PiLp.sub_apply]; change Shuttle.opposite (gait P (u i) n) a - gait P (v j) n a = _
     unfold opposite; change (if a = 3 then -(gait _ _ n) _ else (gait _ _ n) _) - _= _; rw [if_neg h,xP,xP,if_neg h,add_zero, add_zero]
  have μ(i j:J⊕K)(a b:Jus)(G':∀ t:Axis,t ≠ 3→∃ c,∀ n,(G n i-G n j) t=c)(hp:Tendsto (fun n=>dist (G n i) (G n j)) atTop atTop):
         Tendsto (fun n=> T n (i,a) (j,b)) atTop (𝓝 0):=by
     obtain ⟨x,y⟩:= G' 0 (by decide); obtain ⟨w,f⟩:= G' 1 (by decide)
     have h:= fadeGauge _ (hp.congr fun i=> dist_eq_norm ..) x w y f
     let b:ℂ:=sch (G:=SU.group) a b; exact mul_zero b ▸ h.const_mul b
  have H(i j : materialL (J⊕K)) : Tendsto (fun n=> T n i j) atTop (𝓝 (Pf i j)):=by
     obtain ⟨i,a⟩:=i; obtain ⟨j,b⟩:=j; cases i <;> cases j
     · next i j=> exact tendsto_const_nhds.congr fun n=> congrFun (congrFun (p n).symm (i,a)) (j,b)
     · next i j=> exact μ _ _ _ _ (fun t h=>⟨_,v' i j t h⟩) (u' i j)
     · next i j=>
        apply μ (q i) (f j) _ _ _ ((u' j i).congr (fun _=> dist_comm ..)); intro a h
        exact ⟨-(u j a-v i a),fun n=>by rw [show G n (q i)-G n (f j)= -(G n (f j)- G n (q i)) from (neg_sub ..).symm,PiLp.neg_apply,v' j i a h]⟩
     next i j=> exact tendsto_const_nhds.congr fun n=> congrFun (congrFun (h₁ n).symm (i,a)) (j,b)
  have Q(i j:Twah.Stamp (J⊕K)): Tendsto (fun n=> S n i j) atTop (𝓝 (Sf i j)):=by
     obtain ⟨i,a⟩:=i; obtain ⟨j,b⟩:=j; cases i <;> cases j
     · next i j=> exact tendsto_const_nhds.congr fun n=> congrFun (congrFun (p' n).symm (i,a)) (j,b)
     · next i j=> exact spins_far _ _ _ (u' i j)
     · next i j=> exact spins_far _ _ _ ((u' j i).congr fun _=> dist_comm ..)
     next i j=> exact tendsto_const_nhds.congr fun n=> congrFun (congrFun (h₂ n).symm (i,a)) (j,b)
  have hf:= busLimit (M:= fun _ _=> True) A' D' [] [] Pf Sf atTop (List.pairwise_of_forall (fun _ _=>trivial)) (fun i j _=> H i j) Q
  have P₀:= reap_rows L D' f q Pf Sf (fun _ _=> rfl) (fun _ _=>rfl) m
  change bus A' D' [] [] Pf Sf = _ at P₀; rw [P₀] at hf; exact hf

#print axioms spins_far
#print axioms equalC
#print axioms ident
#print axioms tariffs_unroll
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
