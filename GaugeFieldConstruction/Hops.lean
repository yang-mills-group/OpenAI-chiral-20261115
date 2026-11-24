import GaugeFieldConstruction.Apparel
import GaugeFieldConstruction.Aresia
import YM.CF.Spire.Hats
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes Tenant
variable {K b c d r v e a:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=> CSide m B
open Fock.Celeb
variable {R:Stamp m B}
abbrev ScriptK (K:ℝ)(n:ℕ)(e:ℝ) (R S:Stamp m B)(A:SheetT m B)(q:ℝ):Prop:= Ka K n e S A q∧ (q≠0→ Grove (Tenant.terr _) S∧ R⊆S)
abbrev Scribes (K:ℝ)(n:ℕ)(e a d:ℝ) (R:Stamp m B) (A:SheetT m B):Prop:=∃ (V:Stamp m B→ SheetT m B)(q:Stamp m B→ℝ),(∀ S, ScriptK K n e R S (V S) (q S))∧ (∑ S,Branch.rent a S*q S)≤ d∧ (∀ x∈ Lobby m B e,A x=∑ S,V S x)
variable {F G: SheetT m B}
lemma Scribes.add_B (p:Scribes K n e a c R F)(h:Scribes K n e a d R G): Scribes K n e a (c+d) R (fun x=>F x+G x):=by
 obtain ⟨V,q,hq,w,g⟩:=p; obtain ⟨U,r,t,v,l⟩:=h; refine ⟨V+U,q+r,fun S=> ⟨(hq S).1.add_H (t S).1,fun u=>?_⟩,?_,fun x p=>by simp [sum_add_distrib,g x p,l x p]⟩
 · by_cases v:q S=0; exact (t S).2 (by simpa [v] using u); exact (hq S).2 v
 simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add w v
lemma Scribes.neg_B (p:Scribes K n e a c R F): Scribes K n e a c R (fun x=> -F x):=by obtain ⟨V,q,hq,w,g⟩:=p; exact ⟨-V,q,fun S=> ⟨(hq S).1.neg_H, (hq S).2⟩,w,fun x p=> by simp [g x p]⟩
lemma Scribes.lin_B (p:Scribes K n e a c R F)(L:ℂ→L[ℝ]ℂ)(v:‖L‖≤d): Scribes K n e a (d*c) R (fun x=> L (F x)):=by
 obtain ⟨V,q,hq,w,g⟩:=p; refine ⟨fun S x=> L (V S x), fun S=>d*q S,fun S=>⟨(hq S).1.maps_H L v,fun p=> (hq S).2 (right_ne_zero_of_mul p)⟩,?_,fun x p=>by dsimp only; rw [g x p,map_sum]⟩; simp_rw [mul_left_comm _ d (q _),←mul_sum]; exact mul_le_mul_of_nonneg_left w ((norm_nonneg _).trans v)
lemma Scribes.down_B(p:Scribes K n e a c R F)(h:v≤a): Scribes K n e v c R F:=by obtain ⟨V,q,hq,w,g⟩:=p; exact ⟨V,q,hq,(sum_le_sum fun S _=>mul_le_mul_of_nonneg_right (rent_up h _) (hq S).1.pos).trans w,g⟩
lemma Scribes.traceH (W:MSheet m B)(p:HitM K n e a c R W):Scribes K n e a c R (fun x=> (W x).trace):=by
 obtain ⟨V,q,h,w,g⟩:=p -- note p Hit ∃q A in that order
 let k(S:Stamp m B):=∑ i:Single Λ,V S i i; refine ⟨fun S x=> (q S x).trace,k,fun S=> ⟨Ka.sumH univ _ _ fun i _=> (h S i i).1,?_⟩,?_,fun x p=>by change (W x).trace=_; rw [g x p,Matrix.trace_sum]⟩
 · intro v; obtain ⟨i,_,u⟩:= exists_ne_zero_of_sum_ne_zero v; have he:= (h S i i).2 u; exact ⟨he.1,he.2.1⟩
 apply le_trans _ w; unfold costM k; simp_rw [mul_sum]; rw [sum_comm]; exact sum_le_sum fun i p=> single_le_sum (f:=fun j=> saleM a V i j) (fun j _=>sale_nn h.positive ..) (mem_univ i)
lemma pack_S {I:Type*} [Fintype I] (s:I→Stamp m B)(V:I→ SheetT m B)(q:I→ℝ)(p:∀ i,ScriptK K n e R (s i) (V i) (q i))(v:∀ x∈Lobby m B e,F x=∑ i,V i x)(h: (∑ i,Branch.rent a (s i)*q i)≤ c):Scribes K n e a c R F:=by
 refine ⟨fun S x=> ∑ i∈dest s S,V i x,fun S=>∑ i∈dest s S,q i, fun S=> ?_,?_,fun x p=> (v x p).trans (lump s _)⟩
 · have he(i)(u:i∈dest s S):ScriptK K n e R S (V i) (q i):= (mem_filter.mp u).2 ▸ p i; refine ⟨Ka.sumH _ _ _ fun i v=> (he i v).1, fun p=>?_⟩; obtain ⟨i,v,b⟩:=exists_ne_zero_of_sum_ne_zero p; exact (he i v).2 b
 rw [lump s (fun k=> _) ] at h; refine Eq.trans_le ?_ h; apply sum_congr rfl; intro S _; rw [mul_sum]; exact sum_congr rfl fun i hi=>by rw [(mem_filter.mp (show i∈dest s S from hi)).2]
-- Flash ∂_E cycled.All h.
open Brace
variable {L:Side}{j:ℕ}{ho: Odd L.val}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
variable (S:Stamp m B) (W:Brace.Chord m B e P.p→ℂ) (q:ℝ) (p:Jet.Flash (pWorks m B e P.p) (partQ m B e P.p 7 b) 7 S W q)
abbrev Revenue (B:Side)(e K b:ℝ)(pP:ℝ):Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](m:Side)(X:E→Skin m B)(x:E)(i:Cue m), (X x,i)∈ Lobby m B e → TransK 7 X x K→Jet.seek (fun t=> starfish m B (X t) i) 7 x b
lemma issue_B (P:Grasp Y B e)(l:1≤K):∃ b:ℝ,K<b∧∃ c:ℝ,b≤c∧Revenue B e b c P.p:=by -- FALSE exp. need K < input K0 and costT≥input
 let k:=K+1; obtain ⟨C,u,v⟩:= Jet.star_cost 7 (by linarith only [l] : (0:ℝ)≤ K+1) B
 exact ⟨k, lt_add_one K,C,u,fun E _ _ _ m X x i p h=> v E m X (fun _=>i) x h (fun j=> allows_const _ ((vote_unit (i j)).trans_le (by linarith))) _ _ P.baseY.1 (lobby_G p).1 (lobby_G p).2 P.topB⟩
include p
abbrev spinP (P:Grasp Y B e)(v:Pantry m B) (p:v∈ Lobby m B e): Brace.Chord m B e P.p:=⟨(v.1,starfish m B v.1 v.2),(lobby_G p).1,starK P.topB P.baseY.1 (lobby_G p).1 (lobby_G p).2⟩
def altP (P:Grasp Y B e)(F: Brace.Chord m B e P.p→ℂ) (x: Pantry m B):ℂ:= if h:x∈ Lobby m B e then F (spinP P x h) else 0
private lemma go_M (A:ℝ)(k:K<A)(p₀:A≤b)(h:Revenue B e A b P.p): ScriptK K 7 e (∅:Stamp m B) (foam _ (8*B.val) S) (altP P W) q:=by -- grove. continuity. Flash requires exact chart everywhere in open sample. choose extensions. ensure $b$ enough *near points from derivative* (inputK maybe)
 let r:=P.p; let C:=Brace.Chord m B e r
 have hp:Continuous (fun i: ↑(Lobby m B e)=> spinP P i.val i.property):=by
   refine Continuous.subtype_mk (Continuous.prodMk (continuous_fst.comp continuous_subtype_val) ?_) _; apply (starfish_c P.topB P.baseY.1).comp_continuous (f:= (Subtype.val:↑(Lobby m B e)→ Pantry m B)) continuous_subtype_val; exact fun x=> lobby_G x.property
 refine ⟨⟨p.pos,continuousOn_iff_continuous_restrict.mpr ((p.cont.comp hp).congr (fun i=>by change W _=altP P W _; unfold altP; rw [dif_pos i.property])), ?_,?_⟩,fun v=>⟨(foams _ (mul_pos (by decide:0<(8:ℕ)) B.property) _).plus (p.travel v),empty_subset _⟩⟩
 · intro i u j v l s; unfold altP; rw [dif_pos u,dif_pos v]; exact p.reads _ _ ⟨fun i u v=> l i (foam_in _ _ _ u) (foam_in _ _ _ v),Broc.honor _ _ S s l⟩
 intro E _ _ _ X x i v u; have he:∀ᶠ z in 𝓝 x,(X z,i)∈ Lobby m B e ∧ TransK 7 X z A:=(((cliff_n u).prodMk (g:=fun _=>i) continuousAt_const).eventually (lobby_o.mem_nhds v)).and (stream_T u k)
 obtain ⟨U,s,V,hx⟩:=_root_.mem_nhds_iff.mp he; have hz(y)(p:y∈U) : _∧ TransK 7 X y A:= s p; let Q(t:E):C:= if g:t∈U then spinP P (X t,i) (s g).1 else spinP P (X x,i) v
 apply (p.plot E U V Q ?_ x hx).germ
 · filter_upwards [V.mem_nhds hx] with y t; dsimp only [Q,altP, comp_apply]; rw [dif_pos t,dif_pos (hz y t).1] -- orientation goals order? apply .germ opens target first
 intro y vy; obtain ⟨p',u⟩:=hz y vy; have he:∀ᶠ y in 𝓝 y,(Q y).val=(X y,starfish m B (X y) i):=by filter_upwards [V.mem_nhds vy] with x g; unfold Q; rw [dif_pos g]
 refine ⟨fun j=> ((u j).mono p₀).germ (he.mono fun i u=> (congrArg (fun x=> SU.fund (x.1 j)) u).symm),fun j=> ?_⟩; exact (h E m X y i p' u j).germ (he.mono fun i u=> (congrArg (fun x=> Dial.hook x.2 j) u).symm)
omit p
lemma denomin (h:hud_T 7 c)(p:Ka b 7 e R F d)(i:V8 Λ)(T:tangD Λ)(u:c≤b)(v:lin_T 7*c*K≤b)(o:HookP i T)(p0:‖T‖ ≤1)(t:d≠0→ Grove (terr _) R):∃ A,ScriptK K 6 e (ends i) R A (if ends i⊆ R then d else 0) ∧ ∀ x∈Lobby m B e, HasDerivAt (fun y:ℝ=> F (bud T x.1 y,x.2)) (A x) 0:=by
 have he(x:Pantry m B)(l:x∈Lobby m B e):=Ka.coef_tone T p0 h p l u
 split_ifs with s; exact ⟨_,⟨Ka.coef_arr T p0 h p u v,fun x=>⟨t x,s⟩⟩,he⟩
 exact ⟨fun _=>0, ⟨Ka.zero_H,fun x=>(x rfl).elim⟩,fun x p'=> (he x p').congr_deriv (drop_Q _ _ p p' o s)⟩
open Dial Floe
abbrev rateMo (B:Side)(r:ℝ):=r/feeG (8*B.val)
-- auth retains use globally
abbrev BillMood (P: Grasp Y B e)(m:Side) : SheetT m B:=fun x=> Fock.Celeb.Mood P x.1 x.2
lemma bishop (P: Grasp Y B e) (l:ℝ) (l':1≤l)(d₀:hud_T 7 c)(x:c≤l)(V: lin_T 7*c*K≤l):∃ F:ℝ,0≤F ∧∀ (m:Side),P.roundZ≤ (CSide m B).val →∀ T:tangD (CSide m B),‖T‖≤1 → (∀ y∈ Lobby m B e, HasDerivAt (fun t=> BillMood P m (bud T y.1 t,y.2)) (coefG T (BillMood P m) y) 0)∧ ∀ i:V8 (CSide m B),HookP i T→Scribes K 6 e (rateMo B (radF P)) F (ends i) (coefG T (BillMood P m)):=by
 obtain ⟨A,ta,C',hC,E⟩:= issue_B P l'; obtain ⟨F',f,H⟩:= launder P 7 C' (l'.trans (ta.le.trans hC))
 let K:=8*B.val; have hv:0<K:=mul_pos (by decide) B.property; let fK:=feeG K; have ht:0<fK:=by unfold fK feeG; positivity
 refine ⟨fK*F',mul_nonneg ht.le f,fun m u T y=>?_⟩; obtain ⟨U,c0,s,t,p⟩:= H m u firstM; let Pm(S:Stamp m B):=foam _ K S; let J:= foams _ hv (Domain m B); let R V:=altP P (U V); let H'(V:Stamp m B):=go_M V _ _ (s V) A ta hC E
 have hp:∀ x∈ Lobby m B e,BillMood P m x=∑ V,R V x:= by
    intro x l; unfold R altP; simp_rw [dif_pos l]; exact p (spinP P x l) -- tune
 have hx(Y':Pantry m B)(p:Y'∈ Lobby m B e): (fun t:ℝ=> BillMood P m (bud T Y'.1 t,Y'.2)) =ᶠ[𝓝 0] fun t=>∑ V,R V (bud T Y'.1 t,Y'.2):=by
    let f(t:ℝ):= (bud T Y'.1 t,Y'.2); have he:Continuous f:= ((bud_c T).comp (f:=fun t=>(t,Y'.1)) (continuous_id.prodMk continuous_const)).prodMk continuous_const; exact (he.continuousAt.tendsto.eventually (lobby_o.mem_nhds (show f 0∈ Lobby m B e from by unfold f; rw [bud_x]; exact p))).mono fun i p=> hp _ p
 constructor
 · intro x' v; apply DifferentiableAt.hasDerivAt; apply DifferentiableAt.congr_of_eventuallyEq (HasDerivAt.differentiableAt (HasDerivAt.fun_sum (u:=univ) (fun V _=> Ka.coef_tone T y d₀ (H' V).1 (x:=x') v x))) (hx x' v)
 intro i h; choose Y' g τ using fun S:Stamp m B=>denomin d₀ (H' S).1 i T x V h y (fun z=> ((H' S).2 z).1); refine pack_S Pm Y' _ g (fun x z=> ?_) ?_
 · apply ((HasDerivAt.fun_sum (u:=univ) (fun i _=>τ i x z)).congr_of_eventuallyEq (hx x z)).deriv
 -- Hit one mark root with enlargement. Sum over root sheets via coverage. require exponent.
 obtain ⟨D,H,Hl⟩:=J.coverage i.1; let β:=rateMo B (radF P); have hb:0≤β:=div_nonneg (rad_pos P).le ht.le; apply le_trans _ (show ∑ y∈ D,hitE (radF P) c0 y ≤ _ from (sum_le_sum fun y θ=> t y).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right H f)); simp_rw [hitE, hit0,sum_filter]; rw [sum_comm]; apply sum_le_sum; intro S _; have he(z:Site (Domain m B)):0≤(if z∈ S then Branch.rent (radF P) S*c0 S else 0):= by split; exact mul_nonneg (rent_pos ..).le (s S).pos; rfl
 split_ifs with e'; swap; · rw [mul_zero]; exact sum_nonneg fun z _=> he z
 by_cases z:c0 S=0; rw [z,mul_zero]; simp
 have ht':= (s S).travel z; change Grove (terr _) S at ht'
 obtain ⟨j,w,k⟩:= Hl S ht' (e' (mem_insert_self .. : i.1∈ ends i)); apply le_trans _ (single_le_sum (fun j _=> he j) w); rw [if_pos k]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone ((mul_le_mul_of_nonneg_left (J.band ht') hb).trans_eq (by rw [←mul_assoc]; exact congrArg (·*_) (div_mul_cancel₀ _ ht.ne')))) (s S).pos
end YM.CF.XGarden
end
