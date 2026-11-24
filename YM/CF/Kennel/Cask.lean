import YM.CF.Kennel.Balm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Hull
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side}{k:ℕ}
lemma foilR(f:Dress N)(p:ripeF f)(a:Signed):ripeF (foil a f):=by
 intro U t; unfold foil; rw [van,p,GaugeT]; have hv: (t ∘ (incX a⁻¹).anon N) ∘ (incX a).anon N=t:=by
    funext x; obtain ⟨x,rfl⟩:∃ y, wrap _ y=x:=⟨natural x,nat_true _⟩; unfold Function.comp; rw [Shape.anno,Shape.anno, ← Nacre.palm,wink,inv_mul_cancel]; unfold Shape.motion incX; simp
 rw [hv]
lemma foilV(f:Dress N)(a:Signed)(x:Bkg _): foil a f (Yg (incX a) x)=ZoneH (incX a) (f x):=by unfold foil; rw [←kor,wink,mul_inv_cancel,blank]
lemma ripZ (f:Dress N): ripeF (0:Dress N):= fun _ _=> (map_zero _).symm
lemma ripP (f g:Dress N)(h:ripeF f)(p:ripeF g): ripeF (f+g):=by intro x t; rw [Pi.add_apply,Pi.add_apply,h,p,map_add]
lemma tos (p:Signed)(x:Cloud N): litX p (litX p⁻¹ x)=x:=by
 have he(i:ℝ): represent (i • litX p (litX p⁻¹ x))=represent (i • x):=by rw [←roomy, ←roomy, ←kor,wink,inv_mul_cancel,blank];
 let f:=litX p (litX p⁻¹ x)
 have hv: ∀ᶠ i:ℝ in 𝓝[≠] 0,i • litX p (litX p⁻¹ x)=i • x :=by
    filter_upwards [((ray_home f).mono_left nhdsWithin_le_nhds).eventually AnalyticNext.QuarticMatch.Joint.rec_end,((ray_home x).mono_left nhdsWithin_le_nhds).eventually AnalyticNext.QuarticMatch.Joint.rec_end] with i hi hv; rw [←hi,he,hv] -- tune
 obtain ⟨i,u,h⟩:= (hv.and (self_mem_nhdsWithin (a:=(0:ℝ)) (s:={(0:ℝ)}ᶜ))).exists; exact (smul_right_injective _ (show i≠0 from h)) u
lemma glazeM {V W:Rhyme N}(h:Glowing V)(p:Glowing W):Glowing (V-W):=by
 constructor; intro g x; filter_upwards [h.strong g x,p.strong g x] with i hi hp; rw [Pi.sub_apply,Pi.sub_apply,hi,hp]; unfold ActZ; rw [map_sub]
 intro t x; filter_upwards [h.way t x,p.way t x] with i hi hp; rw [Pi.sub_apply,Pi.sub_apply,hi,hp,map_sub]
lemma noct {V W:Rhyme N}(h:Nacre.Motion V)(p:Nacre.Motion W):Nacre.Motion (V-W):=by
 obtain ⟨w,f⟩:= glazeM ⟨h.gauge,h.slope⟩ ⟨p.gauge,p.slope⟩; constructor; exact w; exact f
 · intro i x; filter_upwards [h.plane i x,p.plane i x] with i hi hp; rw [Pi.sub_apply,Pi.sub_apply,hi,hp,map_sub]
 intro x y; filter_upwards [h.current x y,p.current x y] with i hi hp; rw [Pi.sub_apply,Pi.sub_apply,hi,hp]; unfold ActZ; rw [map_sub]
lemma tiltL {V W:Rhyme N}(h:Glowing V)(p:Nacre.crystal k V W):RaysX W:=by
 constructor
 · intro g x; let Z:=(twist (folk g N)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
   apply tendsto_nhds_unique (p (MarkT g x)); apply ((Z.continuous.tendsto _).comp (p x)).congr'; filter_upwards [(h.strong g x).filter_mono nhdsWithin_le_nhds] with i hi; change Z ((i^k)⁻¹ • _) = _; rw [map_smul,hi]; rfl
 intro t x; apply tendsto_nhds_unique (p (SubMotion t x)); apply (((ZoneH (lagX t)).continuous.tendsto _).comp (p x)).congr'; filter_upwards [(h.way t x).filter_mono nhdsWithin_le_nhds] with i hi; change ZoneH (lagX t) ((i^k)⁻¹ • _)=_; rw [map_smul,hi]
variable {m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e} (M:Male)
namespace Hull
variable (H:Hull j L ho a b d e n m A B G T F z Y V){U:Dress (CSide A B)}(p:relic U)
variable {J:Toy k (CSide A B)}(q: handy J)(v:Prints J)(w:0<k)
include H
lemma crownJ {U:Dress (CSide A B)}(p:relic U)(X:Cloud (CSide A B)→ Op (Single (CSide A B)))(h:Nacre.crystal k (U∘ represent) X): let g:= fderiv ℝ (Iteration.chartOf F z) 0; Nacre.crystal k (U∘ baby F z) (X ∘ g):=by
 intro g y; have hp:= p.2; obtain ⟨K,Q⟩:= asideF (hp.of_le (m:=(k:WithTop ℕ∞)) le_top) X h
 unfold Function.comp; rw [Q]; refine ((ride_eps (hp.of_le le_top) _ (H.native.kala.of_le le_top) H.native.icicle K).2 y).congr' ?_; filter_upwards [((ray_home y).eventually H.native.foldM).filter_mono nhdsWithin_le_nhds] with i ht; rw [ht]; rfl
variable (J)
include w
lemma foiled(i:Signed):
 Nacre.crystal k (foil i (cavil J) ∘ baby F z) (fun x=> ZoneH (incX i) (pyre J (litX i⁻¹ (fderiv ℝ (Iteration.chartOf F z) 0 x)))):=by
 apply H.crownJ ((relic_r k w J).2.2 i) (fun t=>ZoneH (incX i) (pyre J (litX i⁻¹ t))) -- tune
 intro x; refine (((ZoneH (n:=CSide A B) (incX i)).continuous.tendsto _).comp (peak_e (litX i⁻¹ x) J)).congr ?_; intro y; change ZoneH (incX i) ((y^k)⁻¹ • _)= (y^k)⁻¹ • foil i (cavil J) (represent (y • x)); rw [foil,roomy,map_smul]
include q
lemma decor(i:Signed): let S:=gallery L j ho G M; let Jk:=fderiv ℝ (Iteration.chartOf F z) 0
 ∀ x:Cloud (CSide m B), S (ZoneH (incX i) (pyre J (litX i⁻¹ (Jk x))))=ZoneH (incX i) (S (pyre J (Jk (litX i⁻¹ x)))):=by
 intro S Jk x
 let P:=cavil J; let V:=foil i P; have he:relic (0:Dress (CSide A B)):= relic_zero
 have ht:ripeF P:= cobblestone J q
 have hy:= H.breeze M (U:=0+P) (relic_up he (relic_r k w J).1) i (W:=0+V) (by simpa using foilR P ht i) (fun x=>by simp; exact foilV ..) (litX i⁻¹ x)
 have hp:= H.breeze M he i (W:=0) (ripZ P) (fun x=> (map_zero _).symm) (litX i⁻¹ x)
 let R:=𝓝[≠] (0:ℝ); let Fk:=emergence L j ho G F z M
 have hu:= H.breach M he k ((relic_r k w J).2.2 i) _ (H.foiled J w i) -- order
 have hz:= H.breach M he k ((relic_r k w J).1) _ (H.crownJ (relic_r k w J).1 (pyre J) (fun x=> peak_e x J)) (litX i⁻¹ x)
 apply tendsto_nhds_unique (hu x); apply (((ZoneH (incX i)).continuous.tendsto _).comp hz).congr'; filter_upwards [hy.filter_mono nhdsWithin_le_nhds,hp.filter_mono nhdsWithin_le_nhds] with t ht he; let z:=t • litX i⁻¹ x; change ZoneH (incX i) ((t^k)⁻¹ • ((Fk (0+P) z)-(Fk 0 z)))=(t^k)⁻¹ • ((Fk (0+V) (t • x))-(Fk 0 (t • x))); rw [map_smul,map_sub]; rw [tos] at ht he; rw [show ZoneH (incX i) (Fk (0+P) z)=_ from ht.symm,show ZoneH (incX i) (Fk 0 z)=_ from he.symm]
end Hull
end YM.CF.Kennel
