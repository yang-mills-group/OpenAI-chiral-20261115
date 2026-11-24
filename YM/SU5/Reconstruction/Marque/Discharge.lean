import YM.SU5.Reconstruction.Marque.Post
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric Bornology BridgeClub Picket Anvil ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical Pointwise
variable {H:Hilbert} {S : OS.Semigroup H clock} (G: Gallery H S)
local notation "U"=> Picket.trans S
local notation "τ"=> parcelUp S
local notation "C"=> G.footprint
local notation "K"=> G.hue
local notation "M"=> G.lobby
variable (Ω:H)(j:Axis) (p:j≠clock)
local notation "W"=> Wedge clock j
local notation "D"=> stroll clock j p
variable (X:Chair G.lobby Ω j)
local notation "Z"=> X.boost
-- vac-only obligations
namespace Gallery
variable {G Ω j p X}
local notation "L"=>PoleHonor G p X
variable (G p X)
structure TinyBacking : Prop where
  reach (e:ℝ)(p0:0<e):∃ t,0<t ∧ t<e∧ G.Tilts Ω j X t
-- p unused
variable {G p X}
lemma closeLift {t:ℝ} (f:ℕ→ℝ) (v:Tendsto f atTop (𝓝 t)) (h:∀ i,L (f i)): L t:= by
 intro V q; refine promotes_bic (X.convex t) (G.tiles_meet V) ?_; rintro _ ⟨i,y,A,z,g,rfl⟩
 let A':= τ y A; let Q:= fun s:ℝ=>Fleet.Form (X.convex s) A'
 have ha(s:ℝ)(x:H):Q s x= Z s (A' (Z (-s) x)):=by change Z s (A' ((Z s)⁻¹ x))=_; rw [X.flip]
 have hx(s:ℝ): ‖Q s‖≤ ‖A'‖:= by apply (Q s).opNorm_le_bound (norm_nonneg _); intro x; rw [ha,(X.convex s).normV]; simpa only[(X.convex (-s)).normV] using (A'.le_opNorm (Z (-s) x))
 let T:= D t '' V; have ho:IsOpen T:= (D t).isOpenMap V q; let R:=strace y (C i)
 have hr:IsCompact R:= (G.close_footprint i).image (continuous_id.add continuous_const)
 have hv:= v.eventually (stamp_cont clock j p t R T ho hr (Set.image_mono g))
 have hy:∀ᶠ n in atTop,Q (f n)∈ (M T):= by
    refine hv.mono ?_; intro n e; let Y:=(D (f n))⁻¹' T; have h₁:IsOpen Y:=ho.preimage ((D (f n)).continuous); refine G.mono (Set.image_preimage_subset (D (f n)) T) ?_
    exact h n Y h₁ A' (G.mono (show R ⊆ Y from Set.image_subset_iff.mp e) (G.typeA z y)) _ (Fleet.arr _ _)
 have hq(x:H): Tendsto (fun n:ℕ=>Q (f n) x) atTop (𝓝 (Q t x)):= by
    have he:Tendsto (fun n:ℕ=> Z (-f n) x) atTop (𝓝 (Z (-t) x)):= (X.orbit _).continuousAt.tendsto.comp v.neg
    simp_rw [ha]; exact curlLimit (spirals v (X.orbit)) (A'.continuous.continuousAt.tendsto.comp he)
 obtain ⟨i₀,e⟩:= eventually_atTop.1 hy
 apply staysClosed (B:= Q t) (show Limited atTop (fun n:ℕ=> Q (f (n+i₀))) (Q t) from ⟨⟨_,norm_nonneg A', Eventually.of_forall fun n=> hx _⟩,fun x w=> tendsto_const_nhds.inner ((hq w).comp (tendsto_add_atTop_nat i₀))⟩) fun n:ℕ=> e (n+i₀) (by omega) -- order of add
variable (b: Authenticates G Ω j p X) (u:Fragment G Ω)(x:G.TinyBacking X)
include x b u
lemma firstLine {t:ℝ} (p0:0≤t): L t:= by
 let g(i:ℕ):ℝ:=((i+1:ℕ):ℝ)⁻¹; have he(i:ℕ): 0< g i := by unfold g; positivity
 choose f v using fun n:ℕ=> x.reach (g n) (he n)
 let a(n:ℕ):= ⌊t/(f n)⌋₊; let d(n:ℕ):= (a n:ℝ)* f n; have e:∀ n:ℕ,L (d n):=fun n=> many (a n) (tilt_bound b u (v n).2.2) -- check signature Tilt parameter
 apply closeLift d ?_ e; apply tendsto_iff_dist_tendsto_zero.mpr; apply squeeze_zero' (g:=g) (Eventually.of_forall fun _=> dist_nonneg) (Eventually.of_forall ?_)
 · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) -- tune order
 intro i; have hk:=v i; have hx₁:a i ≤ t/f i:=Nat.floor_le (div_nonneg p0 (hk.1.le)); have hx₂: t/f i < (a i:ℝ)+1:= Nat.lt_floor_add_one _; have hy:= (le_div_iff₀ hk.1).mp hx₁; unfold d; rw[Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy)]; linarith [(div_lt_iff₀ hk.1).mp hx₂,hk.2.1]
variable (r:Axis)(Y:Chair G.lobby Ω r)(pr:r≠clock)(d:r≠j)(e:∀ V,IsOpen V→ Conveys Y.mirror (G.lobby V) (G.lobby (BridgeClub.turn clock r '' V)))
omit b x u
include e d pr
local notation "F"=> backward clock r
local notation "R"=> Y.mirror
lemma twistProp (s:ℝ)(g:L s): L (-s):= by
 have hz:Conveys R (M W) (M W):= by
    have hy:= e W (openWedge clock j); change Conveys R _ (M ((F) '' W)) at hy; rwa [allImage (F).surjective W W (fun x=> (lo pr.symm d p.symm x).symm)] at hy -- definaltion tune
 have H0:Fleet (R) true:=Y.confirm; have hp:R*Z s=Z (-s)*R:= by simpa only [beamRate,↓reduceIte] using (X.locksFlight X s H0 (show R Ω=Ω from Y.cool) hz)

 intro V p0; let Q:= (D s) '' (F '' V); have h₁:IsOpen (F '' V):=(F).isOpenMap _ p0; have h₂:IsOpen Q:=(D s).isOpenMap _ h₁
 have he (V:Set E4)(p0:IsOpen V): Promotes R (M V) (M (F '' V)):= fun x h y t=> ((e V p0) _ _ t).1 h
 have t:= promotes_trans (promotes_trans (he V p0) (g (F '' V) h₁) Y.confirm) (he Q h₂) (Y.confirm.times (X.convex s))
 rw [←mul_assoc,hp,mul_assoc,Y.well,mul_one, show ((F) '' Q)=D (-s) '' V from ?_] at t; exact t -- `show` placeholder
 unfold Q; rw [Set.image_image,Set.image_image];
 -- ordering images tune
 congr 1; ext1 x; change BridgeClub.turn _ _ ((D s) (BridgeClub.turn _ _ x))=_; rw [reverseDance _ _ _ p s (BridgeClub.turn clock r x) pr d,BridgeClub.turn_turn] -- passed x wrong
include b x u
lemma standBound (s:ℝ) : L s:= by rcases le_total 0 s with q|q; exact firstLine b u x q; nth_rw 1 [← neg_neg s]; exact twistProp r Y pr d e (-s) (firstLine b u x (neg_nonneg.mpr q)) -- parameter order
lemma crowds (s:ℝ)(V:Set E4)(p0:IsOpen V): Conveys (Z s) (M V) (M (D s '' V)):= by
 have h0:= (D s).isOpenMap V p0; refine fun A B p1=>⟨fun q=> standBound b u x r Y pr d e s V p0 A q B p1, fun q=>?_⟩;
 have ht:= standBound b u x r Y pr d e (-s) _ h0 B q A ((X.flip ..) ▸ p1.inv) -- direction
 rw [stroll_neg, Homeomorph.image_symm, Set.preimage_image_eq _ (D s).injective] at ht; exact ht
end Gallery
end YM.Marque.Flow
