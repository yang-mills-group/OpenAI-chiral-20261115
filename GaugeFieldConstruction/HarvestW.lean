import GaugeFieldConstruction.Ziska
import GaugeFieldConstruction.Rain
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes Tenant Phase.Sample
open Fock.Celeb
open Brace Dial
variable {K b c d r v e a:ℝ}{N m B:Side}
local notation "Λ"=> CSide m B
variable {L:Side}{j:ℕ}{ho: Odd L.val}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
abbrev Legume (T:tangD Λ) (j:ℕ) (i:Skin m B):= dir_g (spar j firstM i) (deriv (fun y:ℝ=>spar j firstM (bud T i y)) 0)
abbrev decl (P:Grasp Y B e)(m:Side)(T:tangD (CSide m B)):= Cloud (Honor P (m:=m) T)
private lemma tail_s (g:Pane N)(u:g∈ Clode N e): Guard g e:= interior_subset (s:={x:Pane N| Guard x e}) u
private lemma rain_H (T:tangD Λ)(p:P.roundZ≤(Λ).val) (h:∀ x∈Lobby m B e, let ψ:= changeM P x.1 firstM; HasDerivAt (fun i:ℝ=>changeM P (bud T x.1 i) firstM) (acts (dg (CloseS (m:=m) (B:=B) T j x)) ψ + Honor P T x • ψ) 0)(u:Pantry m B)(p':u∈Lobby m B e):decl P m T u.1=Honor P T u:=by
 let U:= u.1; let F:= Honor (m:=m) P T; have he(V:Pantry m B)(t: V∈ Lobby m B e)(m':V.1=U): F V= F u:=by
    let A:= changeM P U firstM; have he:= sea_g (P:=P) p U (tail_s U p'.1) firstM; have hp:A≠0:= norm_pos_iff.mp (he.2.symm ▸ zero_lt_one)
    apply smul_left_injective ℂ hp
    let g (w:Skin m B):= acts (dg (Legume T j w)) (changeM P w firstM)
    refine add_left_cancel (a:=g U) ?_
    have hv:= h V t; dsimp only at hv -- contradiction rewrite V tape not script
    change HasDerivAt (fun i:ℝ=> changeM P (bud T V.1 i) firstM) (g V.1+F V • changeM P V.1 firstM) 0 at hv; rw [m'] at hv; exact hv.unique (h u p')
 unfold decl Cloud; change (∫ v:Cue m, densP (U,v) • F (U,v) ∂Phase.rains m)= _; refine Eq.trans (integral_congr_ae (Eventually.of_forall (fun v=> ?_ : ∀ v:Cue m,densP (U,v) • F (U,v) = law m B U v • F u))) ?_
 · by_cases p:law m B U v=0; change Phase.law _ _ _ _ • _=_; rw [p,zero_smul,zero_smul]; rw [he (U,v) ⟨p'.1,p⟩ rfl]
 rw [integral_smul_const,Phase.rain_law,one_smul]
lemma whole_29 (P:Grasp Y B e)(W:Pearl P)(w:Stamped j L ho Y)(hv:1≤j)(κ:ℝ):∃ a c0 c1:ℝ,0<a∧0≤c0∧0≤c1 ∧∀ {m:Side},P.roundZ≤(CSide m B).val→∀ (T:tangD (CSide m B)),‖T‖≤1 →
 (∀ x∈Clode (CSide m B) e,let ψ:= changeM P x firstM; HasDerivAt (fun i:ℝ=>changeM P (bud T x i) firstM) (acts (dg (Legume (m:=m) (B:=B) T j x)) ψ + decl P m T x • ψ) 0 ∧ (decl P m T x).re=0) ∧
 ∀ i:V8 (CSide m B), HookP i T→ QBox κ a c0 e (Skye.ends i) (Legume (B:=B) (m:=m) T j) ∧ ABox κ a c1 e (Skye.ends i) (decl P m T):=by
 let v:=max 1 (κ+1); have he:κ<v:=(lt_add_one _).trans_le (le_max_right ..)
 obtain ⟨a,c,d,h,q,p,u⟩:= pollen P W w hv v; obtain ⟨K,hK,k⟩:=billed_FK B (show 1≤v from le_max_left ..); obtain ⟨C,hC,X⟩:=keepMon hK h
 refine ⟨a/2,C*c,C*d,half_pos h,mul_nonneg hC q,mul_nonneg hC p,@fun m e' T t=>?_⟩; obtain ⟨l,S⟩:=u e' T t; constructor
 · intro x hx ψ
   obtain ⟨V,hV⟩ : ∃ V:Cue m, law m B x V ≠0:=by by_contra! h; have he:= Phase.rain_law m B x; simp_rw [h,integral_zero] at he; exact zero_ne_one he
   have hg:(x,V)∈ Lobby m B e:=⟨hx,hV⟩
   rw [show decl P m T x= _ from rain_H T e' l (x,V) hg]; refine ⟨l (x,V) hg,?_⟩; unfold Honor; simp [Spire.zen]
 intro i e; obtain ⟨hp,hw⟩:= S i e
 obtain ⟨V,s,g,vV,G⟩:= hp.cost_k k (show 1 ≤ v from le_max_left ..) he hK X hC -- order method?
 refine ⟨⟨V,s,g,vV,fun x u=>?_⟩,hw.cost_r k (show 1≤ v from le_max_left ..) he hK X hC⟩
 rw [←G _ u]; ext l k; exact Eq.symm (rains_eq (e:=_) _ (fun z=> Legume T j (m:=m) (B:=B) z l k) (fun _ _=>rfl) x u)
#print axioms whole_29
end YM.CF.XGarden
end
