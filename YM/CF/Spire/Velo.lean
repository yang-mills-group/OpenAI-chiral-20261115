import YM.CF.Spire.Neon
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {N P: Side}{u:ℝ}
private lemma rim : low ≤ 1:=by
 change (magC margin 7)⁻¹ ≤ 1; exact inv_le_one_of_one_le₀ (show 1≤magC margin 7 from magC_inc _ margin_pos (show 0≤7 by norm_num)) -- tune
private lemma garnish(x:Vect)(h:‖x‖=1):ren x=x:=by rw [ren,h]; simp
-- Chord fields with prescribed common values
def mare(X Z:Stun N)(w:ℝ):Stun N:=fun i=> Brace.box (w • hook Z i+(1-w) • hook X i)
private lemma mane(X Z:Stun N)(i:Site (More N))(w:ℝ)(p:X i=Z i):mare X Z w i=X i:=by
 unfold mare; have hx:hook Z i=hook X i:=congrArg (fun x:Ballot=>x.val) p.symm; rw [hx,←add_smul,add_sub_cancel,one_smul]; apply Subtype.ext; rw [box_u (norm_pos_iff.mp (by rw [hookN]; norm_num))]; exact garnish _ (hookN ..)
lemma mare_l(X Z:Stun N): mare X Z 0=X:=by funext i; unfold mare; rw [zero_smul,sub_zero,one_smul,zero_add]; apply Subtype.ext; rw [box_u (norm_pos_iff.mp (by rw [hookN]; norm_num))]; exact garnish _ (hookN ..)
lemma mare_r(X Z:Stun N): mare X Z 1=Z:=by funext i; unfold mare; rw [one_smul,sub_self,zero_smul,add_zero]; apply Subtype.ext; rw [box_u (norm_pos_iff.mp (by rw [hookN]; norm_num))]; exact garnish _ (hookN ..)
private lemma trunk (X Z:Stun N)(t:Site (More N))(w:ℝ)(h:w∈Set.Icc 0 1)(g:‖hook X t-hook Z t‖ ≤1/2):low/2≤‖w • hook Z t+(1-w) • hook X t‖:=by
 let F:= w • hook Z t+(1-w) • hook X t
 have he:0≤w:= h.1; have hp:w≤1:= h.2
 have hg:‖F-hook X t‖ ≤1/2:=by rw [show F-hook X t=w • (hook Z t-hook X t) from by unfold F; module,norm_smul,Real.norm_of_nonneg he, norm_sub_rev]; exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans g
 have ht:= abs_norm_sub_norm_le F (hook X t); rw [hookN] at ht; have hx:= (abs_le.mp (ht.trans hg)).1; change low/2 ≤ ‖F‖; linarith [rim]
lemma mare_v(X Z:Stun N)(p:∀ i,‖hook X i-hook Z i‖≤ 1/2):ContinuousOn (mare X Z) (Set.Icc 0 1):=by
 intro z h; apply ContinuousAt.continuousWithinAt; apply continuousAt_pi.mpr; intro i; let f:= fun w:ℝ=> w • hook Z i+(1-w) • hook X i; change ContinuousAt (Brace.box ∘ f) z; have he:Continuous f:=by unfold f; fun_prop
 exact (box_cont (norm_pos_iff.mp ((half_pos low_p).trans_le (trunk X Z i z h (p i))))).comp (f:=f) he.continuousAt
lemma mare_z(U:Bkg (More N))(X Z:Stun N)(p:∀ i,‖hook X i-hook Z i‖≤ 1/2)(e:Slow U (hook X) u)(v:Slow U (hook Z) u)(w:ℝ)(h:w∈Set.Icc 0 1)(t:ℝ)(k: 4/low*(u+u)<t) :Slow U (hook (mare X Z w)) t:=by
 intro i j; let F(m):= w • hook Z m+(1-w) • hook X m
 have hf(i):low/2≤ ‖F i‖:=trunk X Z i w h (p i); have hh(i):hook (mare X Z w) i=ren (F i):= box_u (norm_pos_iff.mp ((half_pos low_p).trans_le (hf _)))
 let A:=U (i,j); let g:=i+step j; rw [hh,hh,turn_ren]; refine lt_of_le_of_lt ((ren_near (by rw [turn_norm]; exact hf _) (hf _)).trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) low_p.le))) k
 change ‖turn A (F g)-F i‖≤_; unfold F; rw [show ∀ v x:Vect,turn A (v+x)=turn A v+turn A x from fun v x=> map_add (spinV A) v x,turn_mul,turn_mul,add_sub_add_comm,←smul_sub,←smul_sub]
 apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,Real.norm_of_nonneg h.1, Real.norm_of_nonneg (sub_nonneg.mpr h.2)]; exact add_le_add ((mul_le_of_le_one_left (norm_nonneg _) h.2).trans (v i j).le) ((mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ h.1)).trans (e i j).le)
def equipV(G:Ratio N P)(X:Sew N P):Prop := ∀ t, X.2.1 ((ratio G).embed t)=X.2.2 t
lemma equip_p(G: Ratio N P)(U:Nom N P)(X:Stun N): equipV G (accordL G U X):=fun i=> adel ..
lemma equip_x(G:Ratio N P)(x:Sew N P)(g:equipV G x)(a:Shape){b:Bool}(Z:ColorT b):equipV G (lotX G a Z x):=by intro i; change Z.X (x.2.1 _) = _; rw [←Shape.foldsT,g]; rfl
lemma equip_l(G:Ratio N P)(X Y:Stun P)(U: Nom N P)(Z:Stun N)(p:equipV G (U,X,Z))(g:equipV G (U,Y,Z))(w:ℝ): equipV G (U,mare X Y w,Z):=by intro i; exact (mane X Y _ _ ((p i).trans (g i).symm)).trans (p i)
lemma portal_p(G:Ratio N P)(X:Sew N P)(p:equipV G X)(hx: X.1= X.1)(s:Slow X.1.1 (hook X.2.1) u)(g:0<u)(Y:Stun P)(v:equipV G (X.1,Y,X.2.2))(t:Slow X.1.1 (hook Y) u)(h:8*(G.count.val:ℝ)*u <1/2):∀ i,‖hook X.2.1 i-hook Y i‖≤1/2:=by
 intro i; let w:=dart G i; let P:=(ratio G).parent i; let e:=3 -- tune
 let c:= hook X.2.2 P; let F:= turn (travel X.1.1 i w) c; have he : stop i w=(ratio G).embed P:= Cube.arrive ..
 have hp:= (stroll_h X.1.1 _ u s w i); have hx:=stroll_h X.1.1 _ u t w i; rw [he,show hook X.2.1 _=c from congrArg (fun z:Ballot=>z.val) (p P)] at hp; rw [he,show hook Y _=c from congrArg (fun z:Ballot=>z.val) (v P)] at hx
 refine ((norm_sub_le_norm_sub_add_norm_sub _ F _).trans ((add_le_add ((norm_sub_rev _ _).trans_le hp) hx).trans ?_)); have hv:(w.length:ℝ)≤4*(G.count.val:ℝ):=by exact_mod_cast dartK G i
 nlinarith only [h, g,hv]
-- calc
variable {j:ℕ}{L A B m:Side}{ho:Odd L.val}{T:Script Male}{e:ℝ}{Y:Pricing j L ho T}
variable {g:Grasp Y B e} (K:Pearl g)(G:Ratio (CSide m B) (CSide A B)) (c:G.count=L)(x:Nom (CSide m B) (CSide A B))(V Z:Stun (CSide A B))(u:Stun (CSide m B))
include c
lemma mare_L(p:equipV G (x,V,u))(k:equipV G (x,Z,u))(l:JointB G x e)(r:Slow x.1 (hook V) K.q)(t:Slow x.1 (hook Z) K.q)(h:Slow x.2 (hook u) K.q): ContinuousOn (mare V Z) (Set.Icc 0 1) ∧ ∀ w∈Set.Icc (0:ℝ) 1, SectorK g G (x, mare V Z w,u):=by
 have he:=portal_p G ⟨x,V,u⟩ p rfl r (K.hp.trans_le K.wide) Z k t (by rw [c]; exact K.chute)
 refine ⟨mare_v _ _ he,fun w v=>?_⟩; have hx:= mare_z x.1 _ _ he r t w v _ K.small
 refine ⟨⟨⟨l.fg.shrink g.gem,l.cg.shrink g.gem,fun i=>(l.follow i).trans g.gem⟩
 ,fun i j=>(hx i j).trans_le g.tender, fun i j=>(h i j).trans_le (K.roof.trans g.tender),?_⟩,l,fun i j=>(hx i j).trans_le g.small,fun i j=>(h i j).trans_le (K.roof.trans g.small)⟩
 intro i; rw [show hook (x,mare V Z w,u).2.1 ((ratio G).embed i)=hook u i from congrArg (fun z:Ballot=>z.val) (equip_l G _ _ x _ p k w i)]; simpa using Y.range -- tune
end YM.CF.Spire
