import YM.SU5.May.FloeHeights
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
variable {N:Side}{j:ℕ}(P:Ramp)(x y z:Cover)
variable {C α β:Type*}[TopologicalSpace C]
-- continuous off collision. cp26 footprint spends.Any theta x−y.
private lemma champion {x:Gaia}(h:x≠0): ContinuousAt Onyx.pencil x:=by
 refine ContinuousAt.smul (g:=gleamV) (f:=fun x:Gaia=>(Real.pi^2*‖x‖^4)⁻¹) ?_ ?_
 exact ContinuousAt.inv₀ (f:=fun x:Gaia=>Real.pi^2*‖x‖^4) (by fun_prop) (mul_ne_zero (pow_ne_zero _ Real.pi_pos.ne') (pow_ne_zero _ (norm_pos_iff.mpr h).ne'))
 unfold gleamV; apply ContinuousAt.mul continuousAt_const; exact (continuous_finsetSum _ fun i _=> ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).smul continuous_const)).continuousAt
lemma posted_shift (x y z:Gaia) (s t:Personality): poster (x+z) (y+z) s t=poster x y s t:=by unfold poster; rw [add_sub_add_right_eq_sub,add_sub_add_right_eq_sub]
private lemma payC {x:C→Gaia}{z:C}(s t:Personality)(p:x z≠0)(h:ContinuousAt x z): ContinuousAt (fun i=>inner ℂ s.voice (acts (Onyx.pencil (x i)) t.voice)) z:= ContinuousAt.inner continuousAt_const (((acts_cont.continuousAt.comp' ((champion p).comp' h))).clm_apply continuousAt_const) -- tune comp symbol
lemma postCont {x y:C→Gaia}{z:C}(s t:Personality) (p: x z ≠ y z)(h:ContinuousAt x z)(u:ContinuousAt y z): ContinuousAt (fun i=> poster (x i) (y i) s t) z:=by
 by_cases a:s.down=t.down; · simp_rw [poster,if_pos a]; exact continuousAt_const
 by_cases b:s.color=t.color; swap; · simp only [poster,if_neg a,toward,b, Ne.symm b, ↓reduceIte,neg_zero,ite_self]; exact continuousAt_const
 cases k:s.down
 · simp_rw [poster,if_neg a,toward, if_pos b, if_pos b.symm,k,Bool.false_eq_true,ite_false]; exact (payC (x:=fun i=> y i-x i) t s (sub_ne_zero.mpr (Ne.symm p)) (u.sub h)).neg
 simp_rw [poster,if_neg a,toward,if_pos b, if_pos b.symm,k,ite_true]; exact payC (x:=fun i=> x i-y i) s t (sub_ne_zero.mpr p) (h.sub u)
-- forward absolute.
variable {F D:ℕ→Side}{R:ℕ→ℝ}(L:ℕ→Jill.Male) (q:∀ i, Wave (Single (F i)))(h:Yard F R)(u:1≤j)(t:∀ᶠ i in atTop, Sea (latPose j (L i) (F i)) (q i)) (s v:Personality)
include t h u q in
lemma regularAt {x y:ℕ → Cover}{A B:Gaia}(p:A≠ B)(X:Tendsto (fun i=>traceV (R i) (x i)) atTop (𝓝 A))(Y:Tendsto (fun i=>traceV (R i) (y i)) atTop (𝓝 B)): Tendsto (fun i=>ice j (F i) (L i) (R i) (x i) (y i) s v) atTop (𝓝 (poster A B s v)):=by
 let a:Agenda Bool R:=⟨fun b=>if b then A else B,fun i b=> if b then x i else y i,?_,?_⟩; exact PriceCliff.whole L q h u t a s v true false
 · intro b; cases b; exact (trace_iff h ..).mp Y; exact (trace_iff h ..).mp X
 · intro a b; cases a <;> cases b <;> first | simp [p,Ne.symm p] | exact fun _=> Eventually.of_forall fun _=>rfl
variable {J :∀ i, Ratio (D i) (F i)}
local notation "G" i:max=> (J i).count
local notation "S" i:max=> Trace j ((J i).count)
variable (w:∀ i:ℕ,R i=(J i).count.val)(d:∀ i:ℕ,Odd ((J i).count.val))(p:∀ᶠ i in atTop, Sea (latPose j white (F i)) (q i))
local notation "F₀" i:max x:max c:max=> point (G i) x (traces (G i) j c)
def prior (P:Ramp)(x:Cover)(y:Cover):Prop:=Gap P j (x-y)
include u q h w d p
set_option linter.flexible false
lemma polls (P:Ramp)(x y:Cover)(ε:ℝ)(a:0<ε)(e:Gap P j (x-y)) : ∀ᶠ i:ℕ in atTop,∀ (c d':S i), ‖ice j (F i) white (R i) (point (G i) x (traces (G i) j c)) (point (G i) y (traces (G i) j d')) s v-poster (nature (G i) x c) (nature (G i) y d') s v‖< ε:=by
 by_contra! hp
 have hz(n:ℕ):∃ m,n ≤ m ∧ ∃ (c d:S m), ε ≤ ‖ice j (F m) white (R m) (F₀ m x c) (F₀ m y d) s v-poster (nature (G m) x c) (nature (G m) y d) s v‖:= frequently_atTop.mp hp n
 choose m g c C l using hz
 obtain ⟨X,k,i⟩:=compactHere (j:=j) x; obtain ⟨Y,f,j'⟩:=compactHere (j:=j) y; let V(i:ℕ):Gaia×Gaia:=(nature (G (m i)) x (c i), nature (G (m i)) y (C i)); obtain ⟨B,t,k',a',W⟩:= (k.prod f).tendsto_subseq (fun i':ℕ=> (show V i'∈ X×ˢ Y from ⟨i _ _ (d _),j' _ _ (d _)⟩))
 have hx:Tendsto (fun i=>(V (k' i)).1) atTop (𝓝 B.1):= continuous_fst.continuousAt.tendsto.comp W; have hy:Tendsto (fun i=>(V (k' i)).2) atTop (𝓝 B.2):=continuous_snd.continuousAt.tendsto.comp W
 let r:=m ∘ k'; have hk:Tendsto r atTop atTop:=(tendsto_atTop_mono g tendsto_id).comp a'.tendsto_atTop
 have H: Yard (F∘r) (R∘r):=⟨fun i=>h.pos _,h.high.comp hk,h.water.comp hk,fun i=>h.even _⟩
 have he:B.1≠ B.2:=by
    intro p; let t':Gaia×Gaia→ℝ:=fun v=> (v.1 P.a+v.1 P.b)-(v.2 P.a+v.2 P.b); have hh:= le_of_tendsto ((show Continuous t' by unfold t'; fun_prop).continuousAt.tendsto.comp W) (b:=-1) (Eventually.of_forall fun i=> off_m P x y (d _) (c (k' i)) (C (k' i)) e); unfold t' at hh; rw [p,sub_self] at hh; linarith
 let X(i):=point (G (r i)) x (traces _ j (c (k' i))); let Y(i):=point (G (r i)) y (traces _ j (C (k' i)))
 have hg:Tendsto (fun i=> ice j (F (r i)) white (R (r i)) (X i) (Y i) s v) atTop (𝓝 (poster B.1 B.2 s v)):= regularAt (x:=X) (y:=Y) (fun _=>white) (fun i=>q (r i)) H u (hk.eventually p) s v he (by unfold Function.comp X; simp_rw [w]; exact hx) (by unfold Function.comp Y; simp_rw [w]; exact hy) -- tune
 let f:Gaia× Gaia→ℂ:=fun t=>poster t.1 t.2 s v; have hF:= Tendsto.comp (postCont (x:=Prod.fst) (y:=Prod.snd) s v he continuous_fst.continuousAt continuous_snd.continuousAt |>.tendsto) W
 have hz:= ge_of_tendsto ((hg.sub hF).norm) (b:=ε) (Eventually.of_forall fun i=>l (k' i)); rw [sub_self,norm_zero] at hz; exact a.not_ge hz
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.polls
