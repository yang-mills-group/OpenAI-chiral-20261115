import GaugeFieldConstruction.Coolie
import GaugeFieldConstruction.Tellur
import YM.CF.Buffered.StepIdentity
import YM.CF.Kea.Fleet
/- One direction integration with sharp Step -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 90000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d v t r u c:ℝ}{j k:ℕ}{m B n:Side}
namespace Echo
local notation "GS"=>SU.group
local notation "Λ"=> CSide m B
open Shield F03
open Brace Ledger
variable (o:Seat (CSide m B))(e:Axis) (g:SU.group.Color) (q:Clip) (p:BudgetPoint)(b:ℝ)
variable {L: Side}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}(P: Grasp Y B d)
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
abbrev marker0 (n:Side):= Pane n → FC (Single n)
abbrev trans1 (n:Side):=Pane n→ Phys n
abbrev tight (p:BudgetPoint)(n:Side):= {x: Pane n| RG.flags p.threshold x=∅}
abbrev moving (n:Side)(b:ℝ)(q:Clip)(x:Pane n):ℝ:=Real.exp (-(b*ding_B q x))
abbrev coatHead (u:Skin m B):= moving Λ b q u • changeM P u firstM
abbrev hard (u:Skin m B):= Set.indicator (tight p Λ) (coatHead (B:=B) q b P) u
lemma moving_C (n:Side):Continuous (moving n b q):=by
 have h:Continuous (ding_B q (n:=More n)):=continuous_iff_continuousAt.mpr fun x=> lively x (ding_π x q).continuousAt; exact (continuous_const.mul h|>.neg).rexp
open Push.Mark
lemma oscilla (U:Pane Λ) : let a:= turnLink (o,e) g; HasDerivAt (fun t:ℝ=> moving Λ b q (a t U)) (-(b * hue_T (Dorm o q) U (at_E o e g))*moving Λ b q U) 0 :=by
 intro a; rw [← dorm_read o q e U g]; let s (x):=ding_B (n:=More Λ) q x; let P0:=fun t:ℝ=> a t U; have he:P0 0=U:=turn_zero ..; apply HasDerivAt.congr_deriv (((stared o e g s U (ding_π ..)).const_mul b|>.neg).exp); simp [moving,a,s]; ring -- tune position/order/f exp
lemma cap_env (e:0<d)(w:P.roundZ≤(CSide m B).val)(t:1≤j)(W:Pearl P)(S:Stamped j L ho Y)(s:∀ U∈tight p Λ, U∈Clode Λ d): Envelope (hard q p b P (m:=m)):=by
 let F:= coatHead (m:=m) q b P; let U:= tight p Λ; have h:IsClosed U:=turn_open; have he:ContinuousOn F U:=by
    apply ((moving_C q b Λ).continuousOn.smul (?_ : ContinuousOn (fun x:Pane Λ=> changeM P x firstM) U)); apply ContinuousOn.mono (s:= {x:Pane Λ|Guard x d}) ?_ (fun x v=> interior_subset (s x v)) -- tune ambiguity
    exact continuousOn_iff_continuous_restrict.mpr (Kea.concur W S e t firstM w)
 obtain ⟨C,c⟩:= h.isCompact.exists_bound_of_continuousOn he; exact Buffered.env_piece _ h.measurableSet he C c
abbrev cashT (u:Pane Λ):=ζcone (n:=Λ) o q p b u (at_E o e g)
def Eff (R:marker0 Λ)(A:Pane Λ): FC (Single Λ):= cashT o e g q p b A • 1 - Turret o p.threshold A • R A -- ∂χ sign
lemma Eff_bound (R:marker0 Λ)(p':Envelope R): Envelope (Eff o e g q p b R):=by
 have hp:Continuous (cashT o e g q p b):=by
    apply continuous_iff_continuousAt.mpr; intro i; apply lively; exact (zeta_jet o q p b i).continuousAt.clm_apply continuousAt_const
 have hh :Continuous (Turret o (G:=GS) p.threshold):=continuous_iff_continuousAt.mpr fun i=>lively i (turret_π o _ _).continuousAt
 let X (A:Pane Λ):= cashT o e g q p b A • (1:FC (Single Λ)); let Y(A:Pane Λ):= Turret o p.threshold A • R A; exact Girt.kitE X Y (· - ·) (continuous_fst.sub continuous_snd) (Env.scale (Env.compact hp) (Env.compact (show Continuous (fun A:Pane Λ=> (1:FC (Single Λ))) from continuous_const))) (Env.scale (Env.compact hh) p') -- tune name
private lemma marked_s {X:Type*}[LinearOrder X][Fintype X](C: FC X)(x:Wave X)(b d t u:ℝ): acts ((b*d - t) • (1:FC X)-d • C) x= -(d • acts C x+(t-b*d) • x):=by
 -- tune
 rw [sub_eq_add_neg, act_add]; have he(V:FC X): acts V x + acts (-V) x=0:=by rw [← act_add,add_neg_cancel,act_zero]
 have hp(V:FC X): acts (-V) x= -acts V x:=by rw [← add_right_inj (acts V x),he,add_neg_cancel]
 rw [hp, ← Complex.coe_smul, ← Complex.coe_smul,act_smul,act_smul, Complex.coe_smul,Complex.coe_smul,act_one,neg_add]; module -- tune X
variable (R:marker0 (CSide m B))(U:Pane (CSide m B))
-- derivative agreement. R(A) pays physical matrix
local notation "Pk"=> turnLink (o,e) g
lemma header(pU:U∈tight p (CSide m B))(s: HasDerivAt (fun t:ℝ=>changeM P (Pk t U) firstM) (acts (R U) (changeM P U firstM)) 0): HasDerivAt (fun t:ℝ=>Turret o p.threshold (Pk t U) • hard q p b P (Pk t U)) (-acts (Eff o e g q p b R U) (hard q p b P U)) 0:=by
 let X:= coatHead (B:=B) (m:=m) q b P; let Y:=hard (m:=m) q p b P; let V:= Turret (G:=GS) o p.threshold; let W:= fun A:Pane Λ=> V A • X A; let E(t'):Pane Λ:= Pk t' U; have he:E 0=U:=turn_zero ..; let e':=at_E o e g; have hk': X U=Y U:=(Set.indicator_of_mem pU _).symm
 have hp:HasDerivAt (fun t=> W (E t)) (-acts (Eff o e g q p b R U) (Y U)) 0:=by
    let c:= hue_T V U e'; let z:= moving Λ b q U; let G:= - (b*hue_T (Dorm o q) U e') ; let q':=changeM P U firstM
    have h: HasDerivAt (fun t=> V (E t)) c 0:= stared o e g _ _ (turret_π ..); have hh: HasDerivAt (fun t=> X (E t)) (z • acts (R U) q' + (G*z) • q') 0:=by
        have hv:= (oscilla o e g q b U).smul s; -- helper simp h
        apply hv.congr_deriv; change moving _ b q (E 0) • _ + (G*z) • changeM P (E 0) firstM = _; rw [he]
    apply (h.smul hh).congr_deriv; rw [←hk']; let K:=hue_T (Dorm o q) U e'; let Eff':=Eff o e g q p b R U; have he': Eff'=(b*K*V U-c) • 1- V U • R U := by change ((b*_)*_-_) • _-_= _; change ((b*V U)*K-c) • _-_= _; rw [mul_right_comm b]; -- tune
    change V (E 0) • _ + c • X (E 0)=_; rw [he]; change V U • (z • acts (R U) q'+ (-(b*K)*z) • q')+c • (z • q')= -acts Eff' (z • q'); rw [he',marked_s _ _ _ _ _ 0,neg_neg]; rw [show acts (R U) (z • q')= z • acts (R U) q' from map_smul ((acts (R U)).restrictScalars ℝ) z q']; module -- tune
 let S':= tight p Λ; have hv:(fun A:Pane Λ=> V A • Y A)=S'.indicator W:=funext fun v=>by
    by_cases p:v∈S'
    · rw [Set.indicator_of_mem p, show Y v = X v from Set.indicator_of_mem p _]
    rw [Set.indicator_of_notMem p,show Y v=0 from Set.indicator_of_notMem p _,smul_zero]
 by_cases h: ∀ i∈slab o,faire GS U i<p.threshold
 · refine hp.congr_of_eventuallyEq ((turn_rise o e g U p.threshold pU h).mono fun t v=> ?_); change V _ • Y _=_ ; rw [show Y (E t)=_ from Set.indicator_of_mem (show E t ∈ S' from v) X]
 push Not at h
 obtain ⟨i,p',g'⟩:=h; obtain ⟨hx,hh⟩:=hotel_tie o p.threshold_pos i p' U (le_antisymm (sooty U i pU) g'); have hv':Eff o e g q p b R U=0:=by
    unfold Eff cashT ζcone hue_T; rw [hx,mul_zero,zero_smul,hh,sub_zero]; simp
 change HasDerivAt (((fun A:Pane Λ=> V A • Y A))∘ E) (-acts (Eff o e g q p b R U) (Y U)) 0; rw [hv,hv',act_zero,neg_zero]; apply blanket o e g W U p.threshold ?_ ?_
 · rw [hv',act_zero,neg_zero] at hp; exact hp
 unfold W V; rw [hx,zero_smul]
-- against arbitrary bystander. accepts all Envelope. choose for any Slot component λ.Total.
def untax(S:marker0 (CSide m B)) : Prop:= Envelope S ∧ ∀ (A A':Pane (CSide m B)), (∀ i:Edge (Seat (CSide m B)), i≠(o,e)→A i=A' i)→ S A=S A'
lemma cost_hand (S: marker0 (CSide m B))(pS:untax o e (m:=m) (B:=B) S)(p':Envelope R)(T':Envelope (hard q p b P (m:=m))) (s:∀ U∈tight p Λ, HasDerivAt (fun t:ℝ=>changeM P (Pk t U) firstM) (acts (R U) (changeM P U firstM)) 0):
 (∫ x:Pane Λ, letterRead ((S*Eff o e g q p b R) x) (hard q p b P x)∂prior GS (More Λ))=0:=by
 let F:= hard (m:=m) q p b P; let E:= Eff o e g q p b R; let H(x:Pane Λ):=letterRead ((S*E) x) (F x); let G':= Turret o (G:=GS) p.threshold; let X(x:Pane Λ):= G' x • letterRead (S x) (F x)
 have hc:Continuous G':=continuous_iff_continuousAt.mpr fun i=> lively i (turret_π o _ _).continuousAt; have hm:Envelope X:= Env.scale (Env.compact hc) (env_letterRead pS.1 T'); have he:Envelope H:= env_letterRead (Buffered.env_mult pS.1 (Eff_bound o e g q p b R p')) T'
 let W:=S
 have hp:(∫ x:Config SU.group (More Λ),(-H x) ∂prior GS (More Λ))=0:=by
    apply trPref o e g X (fun i=> -H i) 0 _ hm (Girt.pole_w H (- ·) continuous_neg he); intro i
    let Q:=fun t:ℝ=>Pk t i; let L:Phys Λ→L[ℝ]ℂ:= (letterRead (S i)).restrictScalars ℝ
    have hx(x:Phys Λ)(j:FC (Single Λ)):letterRead (S i * j) x= L (acts j x):=by unfold letterRead; simp only []; change inner ℂ (Dial.mateK Λ) (acts _ x)=inner ℂ (Dial.mateK Λ) _; rw [act_mul]; rfl
    by_cases hi:i∈ tight p Λ
    · have ht:= L.hasFDerivAt.comp_hasDerivAt (f:=fun x:ℝ=> G' (Q x) • F (Q x)) 0 (header o e g q p b P R i hi (s i hi)); refine ht.congr_deriv ?_|>.congr_of_eventuallyEq (Eventually.of_forall fun v=>?_)
      · change L (-acts (E i) (F i)) = -letterRead (S i * E i) _; rw [map_neg,hx]
      change _ • letterRead (S (Q v)) _ = L (_ • _); rw [show S (Q v)= S i from pS.2 _ _ fun j e=> turn_away _ _ _ e,map_smul]; rfl
    have ht:∀ᶠ t in 𝓝 0, Q t ∉ tight p Λ:= ((turn_see g i (o,e)).tendsto 0).eventually (turn_open.isOpen_compl.mem_nhds (by change Q 0∉tight p Λ; unfold Q; simpa using hi)) -- tune unused turn_open free
    change HasDerivAt _ (-H i) _; have hJ: H i=0:=by unfold H; rw [show F i=0 from Set.indicator_of_notMem hi _,map_zero]
    rw [hJ,neg_zero]; exact (hasDerivAt_const 0 (0:ℂ)).congr_of_eventuallyEq (ht.mono fun t v=>by change _ • letterRead _ (F (Q t))=0; rw [show F (Q t)=0 from Set.indicator_of_notMem v _,map_zero, smul_zero])
 rw [integral_neg,neg_eq_zero] at hp; exact hp
end Echo
end YM.CF.XGarden
end
