import YM.CF.Tarn.Pence
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {G' :Gauge}{r:ℕ}{i:Site c}{U V W :Config G' c}
def drift (G':Gauge)(i:Site c)(r:ℕ)(U V: Config G' c):Prop:=∀ x:Edge (Site c), separation i x.1 ≤ r →U x=V x
def patchU (c:Side)(G':Gauge):=Site c→ G'.El
def found (A:Set (Config G' c))(i:Site c)(r:ℕ)(V:Config G' c):Prop:=∃ g:Site c→ G'.El, ∃ u∈A,drift G' i r (Lattice.gauge g u) V
def salsa (A:Set (Config G' c))(i:Site c)(r:ℕ)(f:SpaceX G' c)(V:Config G' c):ℂ:= if h:found A i r V then f h.choose_spec.choose else 0
lemma dyadic (U:Config G' c)(g h:Site c→G'.El): Lattice.gauge g (Lattice.gauge h U)= Lattice.gauge (g*h) U:=by funext i; unfold Lattice.gauge; simp only [Pi.mul_apply]; group
lemma fix_s : Lattice.gauge (1:Site c→G'.El) U=U:=by ext1 i; simp [Lattice.gauge]
lemma drift.via (p:drift G' i r U V)(g:Site c→G'.El):drift G' i r (Lattice.gauge g U) (Lattice.gauge g V):=by intro i t; simp only [Lattice.gauge,p i t]
lemma drift.mate(p:drift G' i r U V)(h:drift G' i r V W):drift G' i r U W:=fun i t=> (p i t).trans (h i t)
lemma drift.face(p:drift G' i r U V):drift G' i r V U:=fun i t=> (p i t).symm
variable{A:Set (Config G' c)}{f:SpaceX G' c}
structure StampP(A:Set (Config G' c))(i:Site c)(r:ℕ)(f:SpaceX G' c):Prop where
 linked(u v: Config G' c)(p:u∈ A)(s:v∈A)(h g:Site c→G'.El): drift G' i r (Lattice.gauge h u) (Lattice.gauge g v)→ f u=f v
lemma glaze_r (p:∀ u∈A,∀ v∈A,∀ g:Site c→G'.El,drift G' i r (Lattice.gauge g u) v → f u=f v):StampP A i r f:=by refine ⟨fun u v x y h g he=>p _ x _ y (g⁻¹*h) ?_⟩; have hp:=he.via g⁻¹; rwa [dyadic,dyadic,inv_mul_cancel,fix_s] at hp
lemma land_s (p:StampP A i r f)(h:U∈A)(g:Site c→G'.El)(t:drift G' i r (Lattice.gauge g U) V): salsa A i r f V=f U:=by
 have ht:found A i r V:= ⟨g,U,h,t⟩
 unfold salsa; rw [dif_pos ht]; exact p.linked _ _ ht.choose_spec.choose_spec.1 h ht.choose g (ht.choose_spec.choose_spec.2.mate t.face)
lemma SpiceU (p:StampP A i r f): Rel.Atom (salsa A i r f) i r:=by
 refine ⟨fun U g=>?_,fun U V h=>?_⟩
 · by_cases he:found A i r U
   · rcases he with ⟨b,u,w,t⟩; rw [land_s p w _ t]; exact land_s p w (g*b) ((by rw [← dyadic]; exact t.via _))
   have hu:¬found A i r (Lattice.gauge g U):=fun h=>by
      obtain ⟨b,u,s,h⟩:=h; apply he; refine ⟨g⁻¹ * b,u,s,?_⟩; have hu:=h.via g⁻¹; rwa [dyadic,dyadic,inv_mul_cancel,fix_s] at hu
   unfold salsa; rw [dif_neg hu,dif_neg he]
 by_cases he:found A i r U
 · rcases he with ⟨b,u,v,t⟩; rw [land_s p v b t,land_s p v b (t.mate h)]
 have hx:¬found A i r V:=fun v=>by obtain ⟨g,u,q,t⟩:=v; exact he ⟨g,u,q,t.mate (drift.face h)⟩
 unfold salsa; rw [dif_neg he,dif_neg hx]
lemma kleur {n:ℕ}(Φ:SpaceX G' c)(o:Site c)(h:Rel.Atom Φ o r)(hp:1≤n)(v:Φ 1=0)(hx:ContDiffAt ℝ n (satX Φ) 0)(hG:G'.Simple): cFoot 2 (satX Φ):=by
 let A:= satX Φ; let p:= fderiv ℝ A 0; let K(g:G'.El):InputZ G' c →L[ℝ] InputZ G' c:= ContinuousLinearMap.pi (fun i=> (G'.adjoint g).toContinuousLinearMap ∘L (ContinuousLinearMap.proj i)); have he(g:G'.El): A ∘ K g=A:=by
    funext i; change Φ (represent _)= _; rw [show represent (K g i)=Lattice.gauge (fun _=>g) (represent i) from ?_,h.fixed]; rfl
    ext1 j; rw [Lattice.gauge,Work.F03.represent_link,Work.F03.represent_link]; exact Next.SectorChange.exp_adjoint ..
 have hh(g:G'.El): p.comp (K g)=p:=by
    let V:=K g; have ht: ContDiffAt ℝ n A (V 0):= (map_zero V).symm ▸ hx
    have hz:= ((ht.differentiableAt (by exact_mod_cast (show n≠0 by omega))).hasFDerivAt.comp 0 V.hasFDerivAt).fderiv; rw [map_zero V,show A ∘ V= A from he g] at hz; exact hz.symm
 have hp'(e: Blip c): p.comp (Nacre.put G' c e)=0:=by
    let f:= (p.comp (Nacre.put G' c e)).toLinearMap
    have ht(g:G'.El)(u:G'.Color): K g (Nacre.put G' c e u)= Nacre.put G' c e (G'.adjoint g u):=by
       ext1 i; change G'.adjoint g (Pi.single (M:=fun _=>G'.Color) (Trot c e) u i)=Pi.single (M:=fun _:Body 1 c=>G'.Color) (Trot c e) (G'.adjoint g u) i; by_cases h: i=Trot c e<;> simp [h, Pi.single_apply]
    have hz:f=0:=StressFlux.linear_invariant hG f (fun g u=> by change p (Nacre.put G' c e _)=_; rw [←ht]; exact DFunLike.congr_fun (hh g) _); exact ContinuousLinearMap.ext fun i=> DFunLike.congr_fun hz i -- tune CongrFun
 have he:p=0:= ContinuousLinearMap.ext (fun u=> by change p u=0; nth_rw 1 [put_sum u]; rw [map_sum]; exact sum_eq_zero (fun i _=> DFunLike.congr_fun (hp' i) _))
 intro j hu; interval_cases j
 · ext1 i; simp [satX,v]
 ext1 i; simp only [iteratedFDeriv_one_apply,show fderiv ℝ (satX Φ) 0=_ from he]; rfl
end YM.CF.Tarn
