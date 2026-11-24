import YM.CF.BProof.Shade.Mosaic
/-! Buying Basic. Power. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option synthInstance.maxSize 4096
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Equiv Nest Stave Gallery Function MeasureTheory Metric Filter Finset Wilson Lattice Nerve Carpet Score Regard
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side} {s l k:ℕ} {u ε d a b δ θ:ℝ}
namespace Fancy
open Wool
local notation "K_"=>partK k
variable {T:Tray (Floor (partK k)) ε}{F:Drum (rollup (partK k) T) (Floor (partK k))}
-- numeric purchases. group radius Scope.G. δ budget first adjust.
private lemma enoughF(q:ℕ)(p:0< q): (Stave.King (Floor q)).Nonempty:= by
 let c:Fin q:=⟨0,p⟩; exact ⟨btl c 1, show (btl c 1)ᴴ*(btl c 1)= 1 from by rw [bond]; simp⟩
private lemma tinyδ (d:ℝ)(h:0<d): ∀ᶠ (x:ℝ) in 𝓝 0, C₀ x x ≤ d:= by
 have he:Continuous (fun x:ℝ=> C₀ x x):=by unfold C₀ Wool.cash; fun_prop
 have ht:= he.tendsto 0; have hp:(C₀ 0 0)=0:=by simp [Wool.cash,C₀]
 change Tendsto _ _ (nhds (C₀ 0 0)) at ht; rw [hp] at ht; exact ht.eventually (ge_mem_nhds h) -- ≤? ge_mem_nhds t means x≤ b
open Nerve.Pie in
private theorem sponsors(q:ℕ)(U:ℝ)(p:0<U)(d:ℝ)(h:0<d)(hq:0<q):∃ ε> (0:ℝ), ∃ T:Tray (Floor q) ε,∃ l s:ℕ,∃ u a b δ θ:ℝ, ∃ F:Drum (rollup q T) (Floor q), 0<u∧ u≤U ∧ 0<l ∧ 2*press s<Guard.alpha q∧rate s q<b∧ 2*press l<Guard.alpha q∧ rate l q<a ∧ Writ q T s l u a b δ d θ F:=by
 obtain ⟨θ,H,p0,Y⟩:= costume (J:=Floor q) d h; let ε:=θ/4; have he:0<ε:=by unfold ε; positivity
 obtain ⟨T⟩:= Tray.tender he (enoughF q hq); obtain ⟨F,g⟩:=Y (T.house (Fin q)); obtain ⟨v,pv,R⟩:= console d h g
 let a:=v/2; have ha:0<a:=half_pos pv
 obtain ⟨l,hL,lP,lR⟩:= (Pie.tinyD q a ha).exists; let a':ℝ:=θ/(2*(4*(gapR l)+1)); have hx:0<a':=by unfold a'; positivity
 have gz: ∀ᶠ i in 𝓝[>] (0:ℝ), C₀ i i ≤ min a' d := nhdsWithin_le_nhds (tinyδ _ (lt_min hx h))
 have hz: ∀ᶠ i in 𝓝[>] (0:ℝ),(0:ℝ) < i := self_mem_nhdsWithin
 obtain ⟨x,u',A⟩:= (hz.and gz).exists
 obtain ⟨s,Hs,pS,V⟩:= (Pie.tinyD q x u').exists; obtain ⟨u,hU,uU,H'⟩:= Nest.register Home x u' (Nerve.King*s) U p
 refine ⟨ε,he,T,l,s,u,a,x,x,θ,F,hU,uU,hL,pS,V,lP,lR,he,Hs,u',H',?_,H,p0,A.trans (min_le_right ..),g,?_⟩
 · have h:C₀ x x≤a':= A.trans (min_le_left ..); have hf:a'*(2*(4*(gapR l)+1))=θ:=div_mul_cancel₀ _ (by positivity); have h'': (0:ℝ)≤ gapR l:=by positivity
   apply (mul_le_mul_of_nonneg_right h (by positivity : 0≤4*(gapR l:ℝ))).trans; unfold ε; linarith only [hf,hx]
 exact fun S p i x y hx hy hk=> (R _ p i x y hx hy (hk.trans_lt (half_lt_self pv))).le
end Fancy
open Skye
structure Spice (n:Side)(K:Type)(d u:ℝ)(r L:ℕ) where
  ne : Nonempty K
  book : Finite K
  P : K→ Pane n→Pane n
  ok(t:K): Basic n (P t) u d r
  ride (s:Signed)(i: Seat n) (k:Bool): ∃ E:Perm K,∀ w U,P (E w) (Opts s i k U)=Opts s i k (P w U)
  gap : SplitK (Cube.More n) (fun t x (U:Pane n)=>Function.curry (P t U) x) L
namespace Fancy
open Nerve.Pie
local notation "K_"=>partK k
variable {T:Tray (Floor (partK k)) ε}{F:Drum (rollup (partK k) T) (Floor (partK k))}
lemma proven {d1:ℝ}(hk:Nerve.King≤ k) (r0:2*press s <Guard.alpha K_)(r1:2*press l< Guard.alpha K_)(b0:rate s K_< b)(b1:rate l K_< a) (W:Writ K_ T s l u a b δ d θ F)(g:14*d ≤ d1*SU.group.colorScale)(y:0<l)
    (v0:demands k s (Cube.More n))(v1:demands k l (Cube.More n)) : Nonempty (Spice n (Word (Cube.More n) s l k) d1 u (wager s l) (costFull s l k)):=by
 let N:=Cube.More n; obtain ⟨u,t⟩:= investment _ hk N _ _ v0 W.hC r0 b0; obtain ⟨v,w⟩:= investment _ hk N _ _ v1 y r1 b1; have h(x:Word N s l k):Seal (read x) s l b a:=⟨t.hp,Wool.inducts t _, Wool.inducts w _⟩
 have hv(x:Word N s l k):Basic n (make s l _ _ F (read x) (signal x)) _ d1 (wager s l):= is_basic W g (h x)
 refine ⟨⟨⟨(u.coat.some,v.coat.some,Classical.arbitrary (PolicyW N))⟩,bornF ..,fun x=> make s l _ _ F (read x) (signal x), hv, ?_,paper_w u v t w⟩⟩ -- tune order params paper
 intro s' i c; obtain ⟨E,g⟩:= spun_f u v t w s' i c; exact ⟨E,fun x _=> turns W (h (E x)) s' i c (g x).1 (g x).2⟩
private lemma accept(k:ℕ)(hk:Nerve.King≤k)(d1 U:ℝ)(h:0<d1)(uU:0<U):∃ L r N u, 0<u ∧ u ≤ U ∧ ∀ n:Side,N≤ (Cube.More n).val→ ∃ K:Type,Nonempty (Spice n K d1 u r L):=by
 let d':ℝ:= d1*SU.group.colorScale/14; have he: 0<d':=by have := SU.group.colorScale_pos; unfold d'; positivity
 obtain ⟨ε,hp,T,l,s,u,a,b,δ,θ,F,hU,u0,t,j,m,v,K,H⟩:= sponsors (partK k) U uU d' he (Nat.succ_pos _); let Y:=limit k s+limit k l+1
 exact ⟨costFull s l k,wager s l,Y,u,hU,u0,fun n p=> ⟨Word (Cube.More n) s l k, proven (k:=k) hk j v m K H (by unfold d'; linarith) t (demand_full _ _ _ (by unfold Y at p; omega)) (demand_full _ _ _ (by unfold Y at p; omega))⟩⟩
theorem bright_spice (d1 U:ℝ)(h:0<d1)(uU:0<U):∃ L r N u, 0<u ∧ u ≤ U ∧∀ n:Side,N≤(Cube.More n).val→ ∃ K:Type, Nonempty (Spice n K d1 u r L):= by obtain ⟨k,hk⟩:=(show ∃ k:ℕ,Nerve.King≤k from ⟨_,le_rfl⟩); exact accept k hk d1 U h uU
end Fancy
end YM.CF.BProof.Mesh.Shore
