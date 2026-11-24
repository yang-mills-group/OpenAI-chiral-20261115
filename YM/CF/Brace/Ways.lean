import YM.CF.Brace.Dawn
/-! Repack the field logarithm on the original volume N with a submesh witness. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N B K m r b:Side}
abbrev Bars (r b N:Side):=CSide r b=N
def tread(m B:Side)(j l n:ℕ)(M:Tulip.Male)(N:Side)(h:Bars m B N): Bkg (More N)→ Stun N→ Stun N→ ℂ:= by unfold Bars at h; subst N; exact lick j l n M m B
lemma tread_at(m B j l n)(M:Tulip.Male): tread m B j l n M (CSide m B) rfl= lick j l n M m B:=rfl
structure Cane (N:Side)(j:ℕ)(M:Tulip.Male)(e p:ℝ)(F:Bkg (More N)→ Stun N→ Stun N→ ℂ):Prop where
 cap :ContinuousOn (fun x: Gaz N=>F x.1 x.2.1 x.2.2) {x|Guard x.1 e∧ Slow x.1 (hook x.2.1) p ∧ Slow x.1 (hook x.2.2) p}
 rhythm : ∀ U,Guard U e→∀ x, Slow U (hook x) p→∀ y, Slow U (hook y) p → Complex.exp (F U x y) • coneP j M U x=coneP j M U y ∧ coneP j M U x≠0
 spore : ∀ U,Guard U e→∀ x, Slow U (hook x) p→∀ y, Slow U (hook y) p →∀ z,Slow U (hook z) p→ F U x y+F U y z=F U x z
 gour : ∀ U,Guard U e→∀ x, Slow U (hook x) p→∀ y, Slow U (hook y) p →∀ t, F (gauge t U) (feast t x) (feast t y)=F U x y
variable {j l n c:ℕ}{e p d a w:ℝ}(H: CoinG j l c n d a w)(G:Guide b e p d)
include H G
lemma CaneV (M:Tulip.Male)(hx:Bars r b N)(hg:c≤N.val):Cane N j M e p (tread r b j l n M N hx):=by
 unfold Bars at hx; subst N
 rw [tread_at]; exact ⟨lick_c H G hg M,fun U h x hp y hy=> claim H G hg h hp hy M,fun U h x hp y hy z hz=> additiveL H G hg h hp hy M z hz,fun U h x hp y hy t=> lick_g H G hg M t h hp hy⟩
lemma knot_coarse (hb:B=b*K): CSide (m*K) b= CSide m B:=by rw [hb]; unfold CSide More; ac_rfl
omit H G
variable {U:Skin m B}{s:ArrayF m}{x:Cue m}{r':Zone}{q:Sq}
lemma poet (g:enoughV B e p)(h:Guard U e)(hk:0≤e)(u:Verified m B margin U s r')(hx:q∈zone r'): hook (airing m B U s q)=paintV m B U s q:=by
 funext i; change (Brace.box _).val=ren _; have he:=paint_unit hx.1 hk h u hx.2 g i; have hp: paint m B U s q i ≠0:=by intro hy; simp [paintV, hy,ren] at he
 exact box_u hp
lemma kleid(g:enoughV B e p)(h:Guard U e)(hk:0≤e)(u:Verified m B margin U s r')(hx:q∈zone r'): Slow U (hook (airing m B U s q)) p:=by rw [poet g h hk u hx]; exact paint_slow hx.1 hk h u hx.2 g
lemma air_at(g:enoughV B e p)(h:Guard U e)(hk:0≤e)(u:Verified m B margin U s r')(hx:q∈zone r'): ContinuousAt (fun t:Skin m B × ArrayF m×Sq=>airing m B t.1 t.2.1 t.2.2) (U,s,q):=by
 apply continuousAt_pi.mpr; intro i
 let F:=fun t:Skin m B × ArrayF m × Sq=> paint m B t.1 t.2.1 t.2.2 i
 have he := box_cont (x:=F (U,s,q)) (norm_pos_iff.mp ((half_pos low_p).trans_le (prism_nonzero s hx.1 hk h u hx.2 g.1 i)))
 exact he.comp (f:=F) ((show Continuous F from (continuous_apply i).comp (paint_cont m B)).continuousAt)
def starfish (m B: Side)(U:Skin m B)(x:Cue m):= airing m B U (slot m x) (stick 0)
lemma starK (f: enoughV B e p)(he:0≤e)(h:Guard U e)(g:ZeroF m B U x):Slow U (hook (starfish m B U x)) p:=kleid f h he (r':={0}) g (stick_in 0 (mem_singleton_self _))
lemma starG (f:enoughV B e p)(he:0≤e)(h:Guard U e)(g:ZeroF m B U x)(t):starfish m B (gauge t U) (partner m B t x)=feast t (starfish m B U x):=by
 have ht: slot m (partner m B t x)= onF t (slot m x):=rfl
 have hp:= poet f h he (r':={0}) g (stick_in 0 (mem_singleton_self _)); have hz:= poet f (h.cov t) he ((verified_g U t margin (slot m x) {0}).mpr g) (stick_in 0 (mem_singleton_self _))
 unfold starfish; rw [ht]; funext i; apply Subtype.ext; exact congr_fun (hz.trans ((paint_g ..).trans (congrArg (turnX t) hp.symm))) i
lemma starfish_c (f:enoughV B e p)(he:0≤e):ContinuousOn (fun x:Skin m B × Cue m=>starfish m B x.1 x.2) {x|Guard x.1 e∧ZeroF m B x.1 x.2}:=by
 rintro ⟨U,i⟩ ⟨h,H⟩; let K:= fun x:Skin m B×Cue m=>(x.1, slot m x.2,stick 0);
 exact (ContinuousAt.comp (f:=K) (air_at f h he (r':={0}) H (stick_in 0 (mem_singleton_self _))) ((continuous_fst.prodMk (((slot_cont m).comp continuous_snd).prodMk continuous_const)).continuousAt)).continuousWithinAt -- tune
end YM.CF.Brace
