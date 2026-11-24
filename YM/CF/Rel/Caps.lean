import YM.CF.Rel.Apert
import YM.Push.STRESS_FLUX.Color
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{n:Side}{m l r:ℕ} {f:SpaceX G n}{C: G.Color →ₗᵢ[ℝ] G.Color}
private def barG (s:Signed) : InputZ G n →L[ℝ] InputZ G n:= LinearMap.toContinuousLinearMap
  { toFun:=fun a=>Bid.pulled a s, map_add':=by intro x y; funext b; simp only [Bid.pulled,Pi.add_apply]; split <;> abel
    map_smul':=by intro x y; funext b; simp only [Bid.pulled,Pi.smul_apply]; split <;> simp }
lemma barG_p(s:Signed)(x:InputZ G n): represent (barG s x)=pull s 0 (represent x):=by change represent (Bid.pulled x s)= _; simpa only [one_smul] using (Work.F03.represent_pulled s x 1).symm
lemma cake_rot {L:InputZ G n→L[ℝ] InputZ G n}(p:∀ᶠ x in 𝓝 0,(satX f) (L x)=star ((satX f) x))(he:ContDiffAt ℝ m (satX f) 0)(y:Fin m→ InputZ G n): cake m (satX f) (fun i=>L (y i))=star (cake m (satX f) y):=by
 let f':=satX f; let V:= (starL ℝ:ℂ≃L[ℝ]ℂ).toContinuousLinearMap -- tune
 have hp:f'∘ L =ᶠ[𝓝 0] (V ∘ f'):=p; have hm:= (hp.iteratedFDeriv ℝ m).eq_of_nhds; rw [Push.Uniform.iter_lin_at (L:=L) ((map_zero L).symm ▸ he),map_zero,V.iteratedFDeriv_comp_left he le_rfl] at hm
 change cake _ f' _= V (cake _ f' _); unfold cake; rw [_root_.smul_apply,_root_.smul_apply, map_smul]; congr 1; exact DFunLike.congr_fun hm y
def Vsail(C:G.Color→ₗᵢ[ℝ] G.Color)(x:InputZ G n):InputZ G n:=fun i=> C (x i)
private def signC(G:Gauge)(C:G.Color→ₗᵢ[ℝ]G.Color): InputZ G n →L[ℝ] InputZ G n:=LinearMap.toContinuousLinearMap {toFun:= Vsail C, map_add':=fun _ _=>funext fun _=>map_add C _ _,map_smul':=fun i a =>funext fun j=> map_smul C i (a j)}
def Twice(C:G.Color→ₗᵢ[ℝ] G.Color)(f:SpaceX G n):Prop:= (∀ᶠ x:InputZ G n in 𝓝 0,satX f (Vsail C x)=star (satX f x))∧∀ i:Axis, ∀ᶠ x:InputZ G n in 𝓝 0,f (pull (Signed.mirror i) 0 (represent x))=star (satX f x)
def wedgeL (i:PlaqAxes): G.Color →L[ℝ] InputZ G n:= LinearMap.toContinuousLinearMap
  {toFun:=cupB i,map_add':=by intro x y; funext a; simp only [cupB,Pi.add_apply]; split <;> simp_all [smul_add]
   map_smul':=by intro x y; funext a; simp only [cupB,Pi.smul_apply]; split <;> simp_all [smul_comm x]
  }
lemma wedge_roll (i:PlaqAxes)(C:G.Color→ₗ[ℝ] G.Color)(x:G.Color): cupB (n:=n) i (C x)= C ∘ cupB i x:=by ext1 j; simp only [cupB,Function.comp_apply]; split <;> simp_all
lemma clear_t (h:ContDiffAt ℝ (↑(2:ℕ)) (satX f) 0)(hf:Atom f 0 r)(hX:G.Simple)(he: Twice C f) (i j:PlaqAxes) (hv:Disjoint (plaquette i).val (plaquette j).val) (x y:G.Color): cake 2 (satX f) ![cupB i x,cupB j y]=0:=by
 let Q:=cake 2 (satX f); let V:G.Color→G.Color→ℂ:= fun x y=> Q ![cupB i x,cupB j y]; let T':Delph G 2:= Q.compContinuousLinearMap ![wedgeL i,wedgeL j]
 have he'(x y): V x y= T' ![x,y]:=by
    change Q _=Q _; apply congr_arg Q; funext a; fin_cases a<;> rfl
 let W:= ((continuousMultilinearCurryFin1 ℝ G.Color ℂ).toLinearEquiv.toLinearMap).comp T'.curryLeft.toLinearMap; let B:= (show (_→ₗ[ℝ]ℂ)≃ₗ[ℝ](G.Color→L[ℝ]ℂ) from LinearMap.toContinuousLinearMap).symm.toLinearMap.comp W
 have hB(u v): V u v=B u v:=by rw [he']; change _= continuousMultilinearCurryFin1 ℝ G.Color ℂ (T'.curryLeft u) v; rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]; congr 1; funext a; fin_cases a<;> rfl
 haveI : Nontrivial G.Color:=hX.nontrivial_color; obtain ⟨e,H⟩:=exists_norm_eq G.Color zero_le_one
 have ht(x y): V x y=inner ℝ x y • V e e:=by
    rw [hB,hB]; refine StressFlux.bilinear_invariant hX B ?_ H x y; intro g x y; rw [←hB,←hB]; unfold V; rw [show Q ![cupB i x,cupB j y]=_ from roll_o hf h g (![cupB i x,cupB j y])]; congr 1; funext u; fin_cases u<;> exact wedge_roll .. -- tune
 have hζ: V (C e) (C e)=star (V e e):=by
    refine Eq.trans ?_ (cake_rot (L:=signC G C) he.1 h ![cupB i e,cupB j e]); change Q _= Q _; congr 1; funext u; fin_cases u<;> exact wedge_roll ..
 have hγ:V e e=star (V e e):=by simpa [ht (C e) (C e),real_inner_self_eq_norm_sq,H] using hζ
 let L:= Signed.mirror i.val.1; have hφ(i':InputZ G n): (satX f ∘ barG L) i'=f (pull L 0 (represent i')):=by simp only [Function.comp_apply,satX,barG_p]
 have hq := cake_rot (f:=f) (L:=barG L) (he.2 i.val.1|>.mono (fun q hx=> (hφ q).trans hx)) h (![cupB i e,cupB j e]); have hp : (fun u: Fin 2=> barG L (![cupB i e,cupB j e] u))= ![-cupB i e,cupB j e]:= funext fun t=> by fin_cases t; change Bid.pulled (cupB i e) (Signed.mirror i.val.1)= (-cupB i e: InputZ G n); exact shave i e; change Bid.pulled (cupB j e) (Signed.mirror i.val.1)= (cupB j e: InputZ G n); exact spareCi j e _ (fun h=>Finset.disjoint_left.mp hv (mem_insert_self ..) h)
 rw [hp] at hq; change Q ![-_,_]=star (V e e) at hq; have hh : Q ![-cupB i e,cupB j e]= -V e e:=by rw [show ![-cupB i e,cupB j e]= ![cupB i (-e),cupB j e] from congr_arg (fun v:InputZ G n=>![v,cupB j e]) (map_neg (wedgeL i) e).symm, show Q _=_ from hB (-e) e, _root_.map_neg]; simp [hB e e]
 rw [hh,←hγ] at hq; change V x y=0; rw [ht, show V e e=0 from neg_eq_self.mp hq, smul_zero]
lemma clearF (hf: Atom f 0 r)(hG:G.Simple)(h:ContDiffAt ℝ (↑(2:ℕ)) (satX f) 0)(hp:10*(l+1)<n.val)(hr:Twice C f): Ridge f l:=by
 intro i s he; let P(j):= plaqEquiv.symm (i j); let a(j):=jewelG G (s j); have hx(j):plaquette (P j)=i j:= plaqEquiv.apply_symm_apply _
 let t:Fin 2→InputZ G n:=fun j=>cupB (P j) (a j); refine ⟨t,fun j x hi=>?_,?_⟩
 · obtain ⟨x,b⟩:=x; obtain ⟨b,rfl⟩:=plaqEquiv.surjective b; have h₁:= (theatre ..).mp (mem_product.mp hi).1; rw [←hx j]; change sumH _ (cupB _ _) (x,plaquette b)=if plaquette b=_ then _ else _; rw [cobraB]; · simp only [plaq_iff,eq_comm (a:=b)]; rfl
   rw [separation_comm]; dsimp only at h₁; omega
 rw [show t= ![cupB (P 0) (a 0),cupB (P 1) (a 1)] from funext fun i=>by fin_cases i<;> rfl]; exact clear_t h hf hG hr _ _ (by rw [hx,hx]; exact he) _ _
end YM.CF.Rel
