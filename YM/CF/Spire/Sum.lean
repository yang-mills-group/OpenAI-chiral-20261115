import YM.CF.Spire.Velo
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
lemma siren (b:Bool)(a: Shape)(N:Side)(U:Bkg (More N))(x: Stun N)(v:Site (More N)→SU.E) : stir (xtra b) a (gauge v U) = gauge (fun i=>polarT b (v (a.anon N i))) (stir (xtra b) a U) ∧ fume (xtra b) a (feast v x)=feast (fun i=> polarT b (v (a.anon N i))) (fume (xtra b) a x):=by
 let K:=fun i=>polarT b (v (a.anon N i)); refine ⟨?_,?_⟩
 · funext ⟨i,d⟩; change (posDir d).read (stir _ _ _) i=(posDir d).read (gauge K (stir _ _ U)) i
   rw [veil_x, Step.gauge_read,Step.gauge_read, veil_x,map_mul,map_mul,map_inv]; unfold K; rw [salt]; rfl
 funext i; exact (xtra b).trek (v _) (x _)
variable {N:Side}(S:Sweep N)
def hum(m B :Side)(F:Duet m B)(U:Skin m B)(X:Stun (CSide m B)):ℂ:=(Fintype.card (Sweep (CSide m B)):ℂ)⁻¹ * ∑ i:Sweep (CSide m B), payZ i (song m B F (flashA i U) (fireA i X))
lemma song_x (m B :Side)(F :Duet m B)(U:Skin m B)(X:Stun (CSide m B))(S:Sweep (CSide m B)): hum m B F (flashA S U) (fireA S X)=payZ S (hum m B F U X):=by
 let N:=Sweep (CSide m B)
 have he :∑ i:N,payZ i (song m B F (flashA i U) (fireA i X))=∑ i:N, payZ (S*i) (song m B F (flashA (S*i) U) (fireA (S*i) X)):= (Equiv.sum_comp (Equiv.mulLeft S) _).symm -- tune
 let z:ℂ:= (Fintype.card N:ℂ)⁻¹; have hp(A:N→ℂ):payZ S (z*∑ i,A i)=z*∑ i,payZ S (A i):=by
   unfold payZ; cases wageZ S; rfl; change star _=z*∑ i, star (A i); rw [star_mul', star_sum,show star z=z by simp [z]]
 unfold hum; conv_rhs=> rw [he,hp]
 refine congrArg (fun x:ℂ=> z*x) ?_; apply sum_congr rfl; intro i _; rw [firing,lights,←warX]; unfold payZ; rw [sign_seq,Bool.xor_self]; rfl
variable {B m:Side}{F:Duet m B}{M:Tulip.Male}{p q e:ℝ}{j:ℕ}
variable (a:enoughV B e p)(h:0≤e)(f:Cane (CSide m B) j M e p F) (x:Skin m B)(g:Guard x e)
include h a f g
lemma song_gg (y:Stun (CSide m B))(k:Slow x (hook y) p)(L:Site (Domain m B)→E): hum m B F (gauge L x) (feast L y)=hum m B F x y:=by
 unfold hum; refine congrArg (fun x:ℂ=> (Fintype.card (Sweep (CSide m B)):ℂ)⁻¹*x) ?_; apply sum_congr rfl; intro i _; obtain ⟨hx,hv⟩:=siren i.charge (castX i) _ x y L; unfold flashA fireA; rw [hx,hv, song_g a h f _ (keepC (xtra i.charge) (castX i) _ e g) _ (swayX (xtra i.charge) (castX i) _ _ p k)]
lemma piano (hj:1≤j)(B':q≤p)(u:truckV (CSide m B) q p e)(w:ℝ)(hw:e≤ w)(R:∀ A:Bkg (Domain m B),Guard A w→ PaidG j w A)(y z:Stun (CSide m B))(p': Slow x (hook y) q)(t:Slow x (hook z) q) : hum m B F x z= hum m B F x y+F x y z:=by
 let A:= Sweep (CSide m B); let c:ℂ:= (Fintype.card A:ℂ); have hp:c≠0:=by unfold c; exact_mod_cast Fintype.card_ne_zero
 let H: A→ℂ:=fun i=>payZ i (song m B F (flashA i x) (fireA i y)); unfold hum
 rw [sum_congr rfl (g:=fun i=> H i+F x y z) ?_, sum_add_distrib, mul_add]; unfold H; congr 1; simp [A,nsmul_eq_mul,←mul_assoc, (show (Fintype.card (Sweep (CSide m B)):ℂ)≠0 from hp)]
 intro i _; have hk: Slow x (hook y) p:=fun m j=>(p' m j).trans_le B'; have hs:Slow x (hook z) p:=fun m j=>(t m j).trans_le B'
 let t':=castX i; let b:=xtra i.charge; rw [song_no a h f (flashA i x) (keepC b t' x e g) (fireA i y) (fireA i z) (swayX b t' x y p hk) (swayX b t' x z p hs),payZ,sin_add]; congr 1; let L:=(det_sub i.charge t'.s); change payZ i (F (stir _ _ _) (fume _ _ _) (fume _ _ _))=F x y z; rw [← cantor t' b _ L.choose_spec hj f R hw x g u B' y z p' t]; change cSignX (wageZ i) (cSignX (wageZ i) _)=_; rw [sign_seq,Bool.xor_self]; rfl
omit h a f g
-- convert q→baseline to q→p.
lemma truckW{N:Side}(k:truckV N p q e)(w:ℝ)(l:q≤w): truckV N p w e:=by
 intro x h y t z u; obtain ⟨f,yf,zf⟩:=k x h y t z u
 have he (a b: Stun N) : glideV x q a b → glideV x w a b:=by rintro ⟨g,h,f,x,z⟩; exact ⟨g,h,f,x,fun i h j k=>(z i h j k).trans_le l⟩
 exact ⟨_,he _ _ yf,he _ _ zf⟩
-- compensator s: no imaginary in exponential beta term
abbrev zen(z:ℂ):ℂ:= Complex.I * z.im
def candle(m B :Side)(F: Duet m B)(x:Skin m B):ℂ:=
 let X:=starfish m B x (cue_from x).choose
 zen (hum m B F x X-song m B F x X)
lemma zen_a(z x:ℂ):zen (z-x)=zen z-zen x:=by simp [zen,mul_sub]
variable {L:Side}{o:Odd L.val}{Y:Pricing j L o (Thread j)}
variable {P: Grasp Y B e} (K:Pearl P)(w:Stamped j L o Y)(k:P.roundZ≤ (CSide m B).val)(h₀:1≤j)
include h₀ K k w
lemma candleL(x:Skin m B)(g:Guard x e)(M:Tulip.Male)(y:Stun (CSide m B))(t:Slow x (hook y) K.q): candle m B (P.cost m M) x=zen (hum m B (P.cost m M) x y-song m B (P.cost m M) x y):=by
 let X:=starfish m B x (cue_from x).choose
 have he: Slow x (hook X) K.r:=starK K.ample P.baseY.1 g (cue_from x).choose_spec
 have hv:Slow x (hook X) K.q:=fun i j=>(he i j).trans_le K.wide; let f:= P.cost m M; have hc: K.q ≤ P.p := K.roof.trans P.small
 unfold candle; rw [piano P.topB P.baseY.1 (P.couture k M) x g h₀ hc (truckW (K.tick m) P.p P.small) Y.e P.gem (w.fields_one _ (P.needed.trans k)) X y hv t,song_no P.topB P.baseY.1 (P.couture k M) x g X y (fun i j=>(hv i j).trans_le hc) (fun i j=>(t i j).trans_le hc),add_sub_add_right_eq_sub] -- tune
lemma candle_cov (g:Guard x e)(M:Tulip.Male)(v:Site (Domain m B)→E): candle m B (P.cost m M) (gauge v x)=candle m B (P.cost m M) x:=by
 let X:=starfish m B x (cue_from x).choose; have he: Slow x (hook X) K.q:=fun i j=> (starK K.ample P.baseY.1 g (cue_from x).choose_spec i j).trans_le K.wide; have ht: Slow x (hook X) P.p:=fun i j=> (he i j).trans_le (K.roof.trans P.small)
 rw [candleL K w k h₀ _ (g.cov v) M (feast v X) (slow_g _ _ v he), candleL K w k h₀ x g M X he,song_g P.topB P.baseY.1 (P.couture k M) x g X ht,song_gg P.topB P.baseY.1 (P.couture k M) x g X ht]
end YM.CF.Spire
