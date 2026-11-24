import YM.CF.Pic.Sig
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b v K a x:ℝ}{P:Grasp Y B e}
def shapeP (m:Side) (P:Grasp Y B e)(M:Jill.Male)(U:Bkg (Domain m B)):ℂ:= let X:=vacuumW (CSide m B); (Real.log ‖coneP j M U X‖:ℝ)+Spire.zen (hum m B (P.cost m M) U X)
lemma verse (p:ℝ→Bkg (Domain m B))(M:Jill.Male)(S:Set ℝ)(g:IsOpen S)(e':x∈S)(h:∀ t∈S,Guard (p t) e∧ Slow (p t) (hook (vacuumW (CSide m B))) P.p ∧ TransK 1 p t K)(l:1≤K)(v:Screen (pWorks m B e P.p) (partQ m B e P.p 1 K) 1 (fun y=>hum m B (P.cost m M) y.val.1 y.val.2) a b)(ha:0≤a): Allows 1 (fun t=> hum m B (P.cost m M) (p t) (vacuumW (CSide m B))) x ((Fintype.card (Site (Domain m B)):ℝ)*b):=by
 classical
 let X:=vacuumW (CSide m B); let f(t:ℝ): Brace.Chord m B e P.p:=if e:t∈S then ⟨(p t,X),(h _ e).1,(h _ e).2.1⟩ else ⟨(p x,X),(h _ e').1,(h _ e').2.1⟩
 let F:=fun i:Brace.Chord m B e P.p => hum m B (P.cost m M) i.val.1 i.val.2; have he(u)(e:u∈S): (f u).val=(p u,X):=by unfold f; rw [dif_pos e]
 have ht:Allows 1 (F∘f) x ((Fintype.card (Site (Domain m B)):ℝ)*b):=by
    apply debt0 _ _ _ b _ v ha S g _ _ e'; intro t e; have hp:=g.mem_nhds e; refine ⟨fun i=> ((h _ e).2.2 i).germ ?_,fun i=> (allows_const t (show ‖hook X i‖ ≤ K from (hookN ..).le.trans l)).germ ?_⟩
    · filter_upwards [hp] with i' u; rw [he _ u]
    filter_upwards [hp] with i' u; rw [he _ u]
 apply ht.germ; filter_upwards [g.mem_nhds e'] with i e; unfold F Function.comp; simp only; rw [he _ e]
lemma cue(P0:Pearl P)(H:Stamped j L o Y)(p:1≤j)(l:P.roundZ≤(CSide m B).val)(M:Jill.Male)(U:Bkg (Domain m B))(h:Guard U e)(hk: Slow U (hook (vacuumW (CSide m B))) P0.q) : Complex.exp (shapeP m P M U) • changeM P U M=filled (spar j M U) (poleC (CSide m B)):=by
 let X:=vacuumW (CSide m B); have hp:Slow U (hook X) P.p:=fun x i=> (hk x i).trans_le (P0.roof.trans P.small); have hv:= Real.exp_log (norm_pos_iff.mpr (((P.couture l M).rhythm U h X hp X hp).2)); exact change_v P0 H l p M U h X hk _ hv
-- geometric purse across paths
structure CartP (P0:Pearl P)(s:Jill.Male)(U V:Bkg (Domain m B))(k z:ℝ):Prop where
 lf: Guard U e
 rt: Guard V e
 slow_u: Slow U (hook (vacuumW (CSide m B))) P0.q
 slow_v: Slow V (hook (vacuumW (CSide m B))) P0.q
 stab:‖stage (spar j s U) (poleC (CSide m B))-poleC (CSide m B)‖ ≤1/3
 near:‖spar j s V-spar j s U‖≤ k
 piano:|(shapeP m P s U-shapeP m P s V).im|≤ z
lemma shape_im(M:Jill.Male)(P:Grasp Y B e)(U:Bkg (Domain m B)):(shapeP m P M U).im=(hum m B (P.cost m M) U (vacuumW (CSide m B))).im:=by simp [shapeP,Spire.zen]
set_option maxHeartbeats 600000 in
theorem pencil(p:1≤j)(u:0<e)(H:Pearl P):∃ A D v:ℝ,0<A∧0<D∧0<v∧∃ n:ℕ,∀ m:Side,n≤ (CSide m B).val→∀ d:Candle,slowT (Domain m B) d→∀ (V:Bkg (Domain m B))(x:ℝ),0<x→ x ≤ v→ lawnK V (Kea.tax d) x→∀ M:Jill.Male, CartP H M (Kea.tax d) V (A*x) (D*(CSide m B).val^4*x):=by
 obtain ⟨C,w,g,hW,R⟩:=allure; obtain ⟨A,a,h,hA,n,Q⟩:= marchC p; obtain ⟨s,T,G⟩:= boost (min e a) (lt_min u hA)
 have hc:0<H.q:=H.hp.trans_le H.wide; let X:=min (min (s/2) (H.q/4)) (1/(6*A)); have hx:0<X:=lt_min (lt_min (by positivity) (by positivity)) (by positivity); have hu:0<C:= zero_lt_one.trans_le g
 obtain ⟨k,hk,K⟩:= launder P 1 C g; obtain ⟨j',jH⟩:= leanC X hx
 let b:= min w (X/(2*C)); have hb:0<b:=lt_min hW (by positivity); refine ⟨A,16*k+1,b,h,by positivity,hb,n+j'+P.roundZ,fun m l d v V x hp ht e' M=>?_⟩
 let N':= CSide m B; let c':=Domain m B; let f:Bkg c':=Kea.tax d; have hF:lawnK f 1 X:=jH _ (by change j'≤ N'.val*2; unfold N'; omega) d v
 obtain ⟨F,Lc,E,hf⟩:=R c' f V x hp (ht.trans (min_le_left ..)) (car_v e'); let S:= ball (0:ℝ) (2*x)
 have he:0∈S:=mem_ball_self (by positivity); have hE:x∈S:=mem_ball_zero_iff.mpr (by rw [Real.norm_of_nonneg hp.le]; linarith)
 have hQ(y:ℝ)(p:y∈S):lawnK (F y) 1 (2*X):=by
    intro a; refine ((beacon c' _ _ _ (hf y p).2 hF) a).trans ?_; have hx:= (_root_.le_div_iff₀ (show 0< 2*C by positivity)).mp (ht.trans (min_le_right ..)); have ht:|y|<2*x:=mem_ball_zero_iff.mp p; nlinarith
 have hh(y)(t:y∈S):Guard (F y) (min e a):= G c' _ (fun i=>(hQ y t i).trans (by have hp:X ≤ s/2:=(min_le_left ..).trans (min_le_left ..); linarith))
 have hr: Guard f (min e a):=Lc ▸ hh 0 he; have hV:Guard V (min e a):= E ▸ hh x hE; have hB:P.roundZ≤N'.val:=by unfold N'; omega
 have hs(y)(p:y∈S):Slow (F y) (hook (vacuumW N')) H.q:=lease_x (by have he:X ≤ H.q/4:=(min_le_left ..).trans (min_le_right ..); linarith) (F y) (hQ y p)
 have he':Guard f e:=hr.shrink (min_le_left ..); refine ⟨he',hV.shrink (min_le_left ..),show Slow f _ _ from Lc ▸ hs 0 he,E ▸ hs x hE,?_,Q N' (by unfold N'; omega) V f (hV.shrink (min_le_right ..)) (hr.shrink (min_le_right ..)) M x hp.le e',?_⟩
 · let U:UNI (Single N'):=⟨poleC N', LxxX _⟩; apply (stroke (U:=U) ((P.broadness N' hB M).projection f he') (Q N' (by unfold N'; omega) f 1 (hr.shrink (min_le_right ..)) (guard0 hA.le) M X hx.le hF) (spoke _ p _ N')).trans
   have hp':X ≤1/(6*A):=min_le_right ..; rw [le_div_iff₀ (by positivity : 0<6*A)] at hp'; nlinarith
 let J(y:ℝ):=hum m B (P.cost m M) (F y) (vacuumW N')
 have hb:= town J S (convex_ball 0 _) he hE fun i g'=> verse F M S isOpen_ball g' (fun t p=>⟨(hh t p).shrink (min_le_left ..),fun z y=>(hs t p z y).trans_le (H.roof.trans P.small),(hf t p).1⟩) g (K m hB M) (rad_pos P).le
 rw [Complex.sub_im,shape_im,shape_im]; change |_ - _| ≤ _; rw [←(show F 0=Kea.tax d from Lc),← E, ← Complex.sub_im]; refine (Complex.abs_im_le_norm _).trans (hb.trans ?_)
 rw [zero_sub,abs_neg,abs_of_nonneg hp.le, site_card];have hx : (Domain m B).val=(CSide m B).val*2:=rfl
 rw [hx]; push_cast; rw [←sub_nonneg]; ring_nf; positivity
end YM.CF.Pic
