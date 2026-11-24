import YM.CF.Spire.Stand
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch Drapes Peaks Dial Tulip Scroll Branch Paige Brace Vault Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
-- may use two arcs
variable {k n m B: Side}{p q e:ℝ}(g:Guide B e q p)
def glideV {N:Side}(x:Bkg (More N))(p:ℝ)(y z:Stun N): Prop:= ∃ H:ℝ→ Stun N, ContinuousOn H (Set.Icc 0 1) ∧ H 0=y ∧ H 1=z ∧∀ i∈Set.Icc 0 1, Slow x (hook (H i)) p
def truckV (N:Side)(p q e:ℝ): Prop:=∀ x:Bkg (More N),Guard x e→∀ y,Slow x (hook y) p→∀ z,Slow x (hook z) p→∃ v,glideV x q y v ∧ glideV x q z v
include g
lemma backpack (x:Skin m B)(z:Sheen m B)(S:Cue m)(h:Guard x e)(u:Slow x (hook z) q)(v:mantle m B x z S): glideV x p z (starfish m B x S):=by
 let V:=tailP m B z S; let w:=stick 1; have ht:=att_dome v h u; let P:=ark m B x V z; let A:=fun t:ℝ=> P t w; have he:= stick_in 1 (mem_singleton_self 1)
 refine ⟨A,?_,rise_zero _ _ _ _ _ _, (rise_one ..).trans (risingV _ V x S (fun _=>rfl)),fun _ l=> ark_bound ht g w he _ l⟩
 intro t h; apply ContinuousAt.continuousWithinAt
 apply continuousAt_pi.mpr; intro i; let T:=fun t:ℝ=>roofV m B x V z t w i; change ContinuousAt (Brace.box ∘ T) t
 refine (box_cont (norm_pos_iff.mp ((half_pos low_p).trans_le (angel ht g w he t h i)))).comp (f:=T) ?_
 unfold T roofV; fun_prop -- tune
lemma hike (hp:CSide m B=n): truckV n q p e:=by
 subst n; intro x h y hy z hz; obtain ⟨t,H,V⟩:=gets m B x y z; exact ⟨_,backpack g _ _ t h hy H,backpack g _ _ t h hz V⟩
omit g
lemma cSexp(b:Bool)(x:ℂ): Complex.exp (cSignX b x)=cSignX b (Complex.exp x):=by cases b; rfl; exact Complex.exp_conj x
variable (a:Shape){b r:Bool}(Q:ColorT b)(U: UNI SpinIdx)(h:JetS a.s b r U){f:Bkg (More n)→ Stun n → Stun n→ℂ}{M:Male}{j:ℕ}{w:ℝ}(s:1≤j)(t:Cane n j M e p f)(K:∀ A:Bkg (More n),Guard A w→ PaidG j w A)(H:e ≤ w)(x:Bkg (More n))(v:Guard x e)
include h s t K H v
lemma jar(y z: Stun n)(u:Slow x (hook y) p)(B:Slow x (hook z) p) : cSignX (b.xor r) (Complex.exp (f x y z))= Complex.exp (f (stir Q a x) (fume Q a y) (fume Q a z)):=by
 have he:= t.rhythm _ (keepC Q a x e v) (fume Q a y) (swayX Q _ _ y p u) (fume Q a z) (swayX Q a x z p B)
 apply smul_left_injective ℂ he.2; dsimp only; rw [he.1]
 have hx:=congr_arg (arum (prepU a U Q n) b r (mateK n)) (t.rhythm _ v y u z B).1; rw [arum_scale,arum_post _ _ _ h s _ K (v.shrink H),arum_post _ _ _ h s _ K (v.shrink H)] at hx; exact hx
lemma pit(y z: Stun n)(g:glideV x p y z):cSignX (b.xor r) (f x y z)= f (stir Q a x) (fume Q a y) (fume Q a z):=by
 obtain ⟨l,hk,h0,h1,hv⟩:=g; have he:(0:ℝ)∈ Set.Icc 0 1 := ⟨le_rfl,zero_le_one⟩; have hu: Slow x (hook y) p:=h0 ▸ hv 0 he
 let P:=fun z:ℝ=> (x,y,l z); let W:= fun z:ℝ=>(stir Q a x,fume Q a y,fume Q a (l z)); have hp:ContinuousOn P (Set.Icc 0 1):= continuousOn_const.prodMk (continuousOn_const.prodMk hk)
 have hf:ContinuousOn W (Set.Icc 0 1):= by
   have hh:Continuous (fume (N:=n) Q a):=continuous_pi fun i=>Q.X.continuous.comp (continuous_apply (a.anon n i)); exact continuousOn_const.prodMk (continuousOn_const.prodMk (hh.comp_continuousOn hk))
 have hz:=keepC Q a x e v; let V:=fun i:ℝ=> cSignX (b.xor r) (f x y (l i)); let T:= fun i:ℝ=> f (stir Q a x) (fume Q a y) (fume Q a (l i)); have ht:=t.cap.comp hp (fun i h=>⟨v,hu,hv i h⟩)
 have hy:= swayX Q a x y p hu; have hb:ContinuousOn T (Set.Icc 0 1) := t.cap.comp hf (fun i h'=>⟨hz,hy,swayX Q a _ (l i) p (hv i h')⟩)
 have hC (b:Bool) :Continuous (cSignX b):=by cases b; exact continuous_id; exact continuous_star
 have hk:= carry_log isPreconnected_Icc ((hC (b.xor r)).comp_continuousOn (show ContinuousOn (fun i=>f x y (l i)) _ from ht)) hb 0 he (fun i hi=>(cSexp _ _).trans (jar a Q U h s t K H x v y _ hu (hv i hi))) (show V 0=T 0 from ?_) 1 ⟨zero_le_one,le_rfl⟩
 · rw [←h1]; exact hk
 unfold V T; rw [h0, add_eq_left.mp (t.spore x v y hu _ hu _ hu),add_eq_left.mp (t.spore _ hz _ hy _ hy _ hy)]; simp [cSignX]
lemma cantor (l:truckV n q p e)(B:q≤p)(y z:Stun n)(u: Slow x (hook y) q)(k:Slow x (hook z) q) : cSignX (b.xor r) (f x y z)= f (stir Q a x) (fume Q a y) (fume Q a z):=by
 obtain ⟨v',hp,hf⟩:= l x v y u z k
 have hc:= pit a Q U h s t K H x v y v' hp; have hh:= pit a Q U h s t K H x v z v' hf
 obtain ⟨i,f',q,r',y'⟩:= hp; have hm:Slow x (hook v') p:=r' ▸ y' 1 ⟨zero_le_one,le_rfl⟩
 have ht:Slow x (hook y) p:=fun _ i=>(u _ i).trans_le B; have hQ: Slow x (hook z) p:=fun _ i=>(k _ i).trans_le B
 have hT:= t.spore _ (keepC Q a _ e v) _ (swayX Q a _ _ _ ht) _ (swayX Q a _ _ _ hQ) _ (swayX Q a _ _ _ hm)
 apply add_right_cancel; rw [← hh] at hT; exact ((sin_add _ _ _).symm.trans ((congr_arg (cSignX _) (t.spore x v y ht z hQ _ hm)).trans (hc.trans hT.symm))) -- tune
end YM.CF.Spire
