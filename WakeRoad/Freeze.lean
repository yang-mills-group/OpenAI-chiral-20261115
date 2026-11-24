import WakeRoad.Racers
/-! # Spin receipt before issuing Gaussian lane, arbitrary fixed arity -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open YM.WakeRoad
open YM.Stationary (Gaia)
open Ballad
namespace Hearth
variable {N:Side} {n j:ℕ}
variable (X:Fin n → Cover)(L:Fin n → Twah.DirSpin)(r:ℕ)(n_:Side) (M:Jill.Male)
private lemma dietary_bound (C:ℝ)(p:Billow C (lake n_ j M))(a b:Cover)(D E:Twah.DirSpin): ‖dietary 1 a b D E n_ j M‖≤ C:=by
 rw [dietary,in_transcript 1 a b D E,clear_canvas,hopF]; simp_rw [Twah.uncut, norm_mul,norm_pow]; norm_num; refine (norm_inner_le_norm ..).trans ?_; rw [Hiro.basis_cost,one_mul]; exact Hiro.roll_c p ..

abbrev postD (G:Fin n→Fin n→ℂ)(i k: Picture n) :ℂ:=
  if i.2.2=k.2.2 then 0 else if i.2.1 = k.2.1 then (if i.2.2 then G i.1 k.1 else -G k.1 i.1) else 0
lemma photo_rent (Ht:Even n_.val)(i a:Picture n): photo X L r n_ j M i a=postD (fun i k=>dietary r (X i) (X k) (L i) (L k) n_ j M) i a:=by
 obtain ⟨i,b,m⟩:=i; obtain ⟨a,c,t⟩:=a; by_cases p:b=c <;> cases m <;> cases t
 all_goals simp only [photo,toneChart, postD,reduceCtorEq,↓reduceIte]
 all_goals first| exact still .. | exact calm .. | exact rank_hint _ _ _ _ _ Ht _ _ | rw [flipcost,rank_hint _ _ _ _ _ Ht]; simp [p,eq_comm]

lemma post_bound (Y:Fin n → Fin n→ℂ)(C:ℝ)(p:0≤C)(h:∀ i j,‖Y i j‖ ≤ C) (i a : Picture n): ‖postD Y i a‖≤ C:= by unfold postD; split_ifs<;>simp [p,h]
lemma pigments_cap (n j:ℕ) (h:1≤j): ∃ C:ℝ,0≤ C∧∀ (X:Fin n→ Cover)(L:Fin n → Twah.DirSpin) (N:Side)(M:Jill.Male)(x:Wave (Single N))(_: Sea (spar j M (1:Pane N)) x)(_: Pad j N) (i:swatches n), ‖pigment X L 1 N (mateK N) x i‖ ≤ C:=by
 obtain ⟨H,hb,T⟩:= lake_local h
 choose f p hc using spin_shelf (n:=n) H
 refine ⟨∑ i:swatches n, f i,sum_nonneg (fun i _=> p i),fun X L N M x v e i=>?_⟩
 rw [pigment,noble_photo X L 1 N M _ v h e]; refine le_trans (hc i _ ?_) (single_le_sum (f:=f) (fun i _=> p i) (mem_univ _))
 intro i k; rw [photo_rent X L 1 N M e.1]; apply post_bound _ H hb.le; exact fun _ _=> dietary_bound N M H (T e.1 M) ..

abbrev spinOrbit (x:Fin n→Gaia)(L:Fin n→Twah.DirSpin)(i k: Picture n):ℂ:= postD (fun i k=>shotL (x i-x k) (L i) (L k)) i k
-- appointment after choosing f
variable (Y:ℕ→Fin n→ Cover)(R:ℕ→ℕ) (N':ℕ→ Side) {P:Fin n→Gaia}
variable (Yp:Tendsto R atTop atTop)(YP:Yard N' (fun i=> (R i:ℝ))) (Hx:∀ i a,Tendsto (fun k=>riseX (R k) (Y k i-Y k a)) atTop (𝓝 (P i-P a))) (H₀:∀ i a,P i=P a→∀ᶠ k:ℕ in atTop,Y k i=Y k a)
lemma post_moves (Y:ℕ→Fin n → Fin n→ℂ)(Q:Fin n → Fin n→ℂ)(h:∀ i j,Tendsto (fun m=> Y m i j) atTop (𝓝 (Q i j)))(i j:Picture n):Tendsto (fun m=>postD (Y m) i j) atTop (𝓝 (postD Q i j)):=by unfold postD; split_ifs; exact tendsto_const_nhds; exact h _ _; exact (h _ _).neg; exact tendsto_const_nhds
include YP Hx H₀
lemma orbit_cost (h:1≤j)(M:ℕ→Jill.Male)(i a:Picture n):
    Tendsto (fun k=> photo (Y k) L (R k) (N' k) j (M k) i a) atTop (𝓝 (spinOrbit P L i a)) := by
 rw [funext (fun k=>photo_rent (j:=j) (Y k) L (R k) (N' k) (M k) (YP.even k) i a)]
 refine post_moves _ _ (fun i a=>?_ ) _ _ -- placeholders `exact` accepts?
 let Z:= P i-P a; let b:=L i; let d:=L a; let u:= alignedα b sourceSlot; let v:=alignedβ d sourceSlot
 obtain ⟨c,hv,hT⟩:=lake_formal h
 simp_rw [dietary,in_transcript]; have ht:=Emu.tally (L:=fun i=> (R i:ℝ)) (fun i=>too (N' i)) M (fun i=> lakeP _ j (M i)) (fun i=>0) YP hv (by norm_num : (0:ℝ)<1) (fun x:Slot=>Eventually.of_forall fun i=>hT _ (YP.even i) _ x) u v (fun k=>Y k i) (fun k=>Y k a) Z ?_ (Hx i a) h (fun _=>1)
 · rw [show frank u v Z= shotL Z b d from if_pos rfl] at ht; exact ht
 by_cases p:P i=P a; · exact Or.inr ⟨sub_eq_zero.mpr p,H₀ _ _ p⟩
 exact Or.inl (sub_ne_zero.mpr p)

abbrev schedule (c:swatches n)(P:Fin n→Gaia)(L:Fin n→Twah.DirSpin) := spinFilm n (fun i=>walkC (tintM (c i))) (spinOrbit P L)
lemma spending (j:ℕ)(h:1≤j)(M:ℕ→Jill.Male)(t:∀ i,Pad j (N' i))(x:∀ i,Wave (Single (N' i)))(e:∀ i, Sea (spar j (M i) (1:Pane (N' i))) (x i))(c:swatches n):
    Tendsto (fun i=>(R i:ℂ)^(3*n)*pigment (Y i) L 1 (N' i) (mateK (N' i)) (x i) c) atTop (𝓝 (schedule c P L)):=by
 apply (spin_moves (fun i=>walkC (tintM (c i))) _ _ (orbit_cost L Y R N' YP Hx H₀ h M)).congr fun i=>Eq.symm ?_; rw [←noble_photo (Y i) L (R i) (N' i) (M i) _ (e i) h (t i),pigment_power,map_smul]; rfl
-- nested payment, even attains at any tolerances for all sufficiently high R-schedules,
-- no uniformity to be assumed in agenda sizes after that. prove reusable logistics
open Cache Glaze
set_option linter.unusedVariables false in
omit YP Hx H₀ in
lemma logistics {η:Type*}[TopologicalSpace η]{f:ℕ→(N:Side)→(M:Jill.Male)→Wave (Single N)→η}{z:η}
    (j:ℕ)(R:ℕ→ℕ)(h:Tendsto R atTop atTop)(e:∀ i,0<R i)
    (p:∀ (t:ℕ→ℕ)(W:StrictMono t)(N:ℕ→ Side), Yard N (fun i=> (R (t i):ℝ)) → ∀ (m:ℕ→Jill.Male)(x:∀ i,Wave (Single (N i)))(_:∀ i,Pad j (N i))(_:∀ i,Sea (spar j (m i) (1:Pane (N i))) (x i)), Tendsto (fun i=> f (t i) (N i) (m i) (x i)) atTop (𝓝 z)):
    ∀ S∈ 𝓝 z,∀ᶠ i:ℕ in atTop,∀ᶠ N:Side in atTop,Kea.Pad j N → ∀ M:Jill.Male,∀ x:Wave (Single N),Sea (spar j M (1:Pane N)) x→f i N M x∈S:= by
 intro S u; by_contra g; obtain ⟨t,v,w⟩:= extraction_of_frequently_atTop (not_eventually.mp g)
 let Q(k):= R (t k); have ht(k:ℕ):0<(Q k:ℝ):=Nat.cast_pos.mpr (e _)
 have he (k:ℕ):∃ (N:Side)(M:Jill.Male)(x:Wave (Single N)), Kea.Pad j N ∧ (Q k:ℝ)* Ember.pinch N ≤ (2:ℝ)⁻¹ ^k ∧ Sea (spar j M (1:Pane N)) x ∧ f (t k) N M x ∉ S:=by
   obtain ⟨n,h₁⟩:= Glaze.pick_depth (p:=(show 0<(2:ℝ)⁻¹ ^k/(Q k:ℝ) from (by have he:=ht k; positivity)))
   obtain ⟨N,F,H⟩:=(((not_eventually.mp (w k))).and_eventually (eventually_ge_atTop (⟨n+1,by omega⟩:Side))).exists
   push Not at F; obtain ⟨p,M,x,v,d⟩:=F
   exact ⟨N,M,x,p,(mul_comm _ _).le.trans ((le_div_iff₀ (ht _)).1 (h₁ (by change n+1≤N.val at H; omega))),v,d⟩
 choose N M x hn hR q a using he
 have hx:Yard N (fun i=> (Q i:ℝ)):=⟨ht,tendsto_natCast_atTop_atTop.comp (h.comp v.tendsto_atTop),squeeze_zero (fun i=>mul_nonneg (ht i).le (Ember.pinch_pos _).le) hR (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),fun i=>(hn i).1⟩
 obtain ⟨i,c⟩:=( (p t v N hx M x hn q).eventually u).exists; exact a i c

omit YP
include Yp
lemma amble (j:ℕ)(h:1≤j)(t:∀ i,0<R i)(a:swatches n): ∀ S∈𝓝 (schedule a P L),∀ᶠ i:ℕ in atTop,∀ᶠ N:Side in atTop,Kea.Pad j N → ∀ (M:Jill.Male)(x:Wave (Single N)),Sea (spar j M (1: Pane N)) x→ (R i:ℂ)^(3*n)* pigment (Y i) L 1 N (mateK N) x a ∈ S:= by
 apply logistics _ R Yp t; intro u p N H M x t h'; refine spending L (Y ∘ u) (R∘u) N H ?_ ?_ j h M t x h' a -- order
 · exact fun i j=>(Hx i j).comp p.tendsto_atTop
 exact fun i j c=> p.tendsto_atTop.eventually (H₀ i j c)
#print axioms amble
#print axioms pigments_cap
end Hearth
end YM.CF.Hiro
