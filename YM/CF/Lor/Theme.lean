import YM.CF.Lor.Hot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Nacre Font
open BoreP Fief rates Braid Rel Souk Girt
variable{m X B M:Side}{G:Ratio (mid m B) (mid X B)}{e x β d:ℝ} {T:Roam m X B}(F:Tube G₅ T)
local notation "L"=> mid m B
local notation "K"=> More (mid m B)
local notation "K'"=> More (mid X B)
local notation "Y"=> Rent0 G e
local notation "S₀"=>portA (X:=X) (B:=B) (Stores.till x)
variable (G)
variable{k l:ℕ}{ρ a b η c C' D v u t:ℝ}
local notation "d'"=> Single L
section pay
local notation "Λ_"=> Directions SU.group K
variable (R: Monk SU.group T)(P:Monk SU.group T→ Rent0 G e)
local notation "R'"=> violet R
abbrev Waltz (F:Rent0 G e→ℂ) (A B:ℝ) := let p:= Cloak.starsW (x:=x) R (F∘ P); Allows k p 0 A∧ Allows k (p+ Cloak.starsW (x:=x) R' (F∘ P)) 0 B
section
variable {F₁ H:Rent0 G e→ℂ}
lemma waltz_c(o:ℝ)(p: Waltz G R P F₁ C' D (k:=k) (x:=x)): Waltz G R P (o • F₁) (|o| * C') (|o| * D) (k:=k) (x:=x):=by
 constructor <;> (first|apply (p.1.smul o).germ| apply (p.2.smul o).germ) <;> (filter_upwards with v; simp only [Cloak.starsW, Pi.smul_apply,Function.comp_apply, Pi.add_apply,smul_add,smul_sub])
lemma waltz_s {ι: Type} (M:Finset ι)(V:ι→Rent0 G e→ℂ)(C D:ι→ℝ)(h:∀ i∈M,Waltz G R P (V i) (C i) (D i) (k:=k) (x:=x)) : Waltz G R P (∑ i∈M,V i) (∑ i∈M,C i) (∑ i∈M,D i) (k:=k) (x:=x):=by
 constructor
 · apply (Jet.allows_sum (fun i g=>(h i g).1)).germ; filter_upwards with p; simp only [Cloak.starsW,Function.comp_apply,Finset.sum_apply,sum_sub_distrib]
 apply (Jet.allows_sum (fun i g=>(h i g).2)).germ; filter_upwards with p; simp only [Cloak.starsW,Function.comp_apply,Finset.sum_apply,sum_sub_distrib,Pi.add_apply,sum_add_distrib]
lemma waltz_nil(p:F₁=0)(ht:0≤a)(hv:0≤b):Waltz G R P F₁ a b (k:=k) (x:=x):=by subst p; unfold Waltz Cloak.starsW; simp only [Function.comp_apply,Pi.zero_apply,sub_zero]; exact ⟨Jet.allows_const _ (norm_zero.le.trans ht), (Jet.allows_const (n:=k) 0 (v:=(0+0:ℂ)) (le_trans (by simp) hv))⟩ -- tune le_trans
lemma waltz_m (p:Waltz G R P F₁ C' D (k:=k) (x:=x))(h:C'≤a)(hp:D≤b): Waltz G R P F₁ a b (k:=k) (x:=x):=⟨p.1.mono h,p.2.mono hp⟩
end
abbrev Area (o:Site K)(C U V:ℝ) : Prop:= ∀ (F:Y→ℂ)(i:mSeal X B), Grove (Tenant.terr _) i → i∈ portA (Stores.till x)→ o∈ Facet.mount (ratio G) i→ (∀ v w,(dressL G e).rel i v w→ F v=F w) → ∀ W,OrderD (LineE (k+2) G C e) (k+2) F W → Waltz G R P F (U * W) (V*W) (k:=k) (x:=x)
lemma valor (U V C z:ℝ)(p:0 ≤U)(u:0 ≤ V)(Y_ :Haze m X B G e)(i j:d')(h:Area (k:=k) (x:=x) G R P (place_x i) C U V)(θ: nomA m X B→ Op (Single L))(hp:0≤ρ)(hz:Hest.Ind G Y_ ρ z C (k+2) θ): Waltz G R P (fun v=>Corne.led G x Y_ v i j) (U*z) (V*z) (k:=k) (x:=x):=by
 obtain ⟨W,Kp,H⟩:=hz.port; let f(t:mSeal X B)(v:Y):= Y_ t v i j; let S':=portA (X:=X) (B:=B) (Stores.till x)
 have he : (fun v=> Corne.led G x Y_ v i j)= ∑ t∈S',f t:=funext fun v=>by rw [Finset.sum_apply]; exact Matrix.sum_apply ..
 let Q(t:mSeal X B):= W t i j; have hv(t:mSeal X B)(p':t∈S') : Waltz G R P (f t) (U*Q t) (V* Q t) (x:=x) (k:=k):=by
    by_cases hz:W t i j=0
    · unfold Q; rw [hz,mul_zero,mul_zero]; exact waltz_nil _ _ _ (funext fun v=>norm_le_zero_iff.mp ((Kp t).gate i j v|>.trans_eq hz)) le_rfl le_rfl
    obtain ⟨hp',hv,h⟩:= (Kp t).root i j hz; exact ‹Area (k:=k) (x:=x) _ _ _ _ _ _ _› (f t) t hp' p' (mem_image.mpr ⟨_,(mem_filter.mp hv).2,Ratio.embed_parent ..⟩) (fun u v p=>congrArg (fun w:Op d'=> w i j) ((Kp t).reads _ _ p)) _ ((Kp t).folk _ _)
 have hh := bound_w (i:=i) (j:=j) (M:=S') (fun i=> (Kp i).pos) H hp
 rw [he]; apply waltz_m _ _ _ (waltz_s _ _ _ _ _ _ _ hv) <;> rw [← Finset.mul_sum]
 exact mul_le_mul_of_nonneg_left hh p
 exact mul_le_mul_of_nonneg_left hh u -- tune
lemma prize (U V C z:ℝ)(p:0 ≤U)(u:0 ≤ V)(Y_ :Msca m X B G e)(i: Site K)(h:Area (k:=k) (x:=x) G R P i C U V)(θ:nomA m X B→ ℂ)(hp:0≤ρ)(hz:Tally Y_ θ η C ρ z (k+2)): let g:=G.count.val; Waltz G R P (fun v=>fJ G Y_ x v i) (U*((g:ℝ)^4*z)) (V*((g:ℝ)^4*z)) (k:=k) (x:=x):=by
 intro g; obtain ⟨W,H,Hp⟩:=hz.members; let S':=portA (X:=X) (B:=B) (Stores.till x); let t(u:mSeal X B):= turtle (ratio G) u i; let V'(u):= t u • Y_ u
 rw [show (fun v=> fJ G Y_ x v i)= ∑ u∈S',V' u from funext fun v=> (Finset.sum_apply v S' V').symm]
 let F'(u):= |t u| * W u; have hv(v)(x_0:v∈ S') : Waltz G R P (V' v) (U*F' v) (V*F' v) (k:=k) (x:=x) :=by -- fix shadow
    by_cases hp':W v=0
    · have hk:Y_ v=0:=funext fun i=>norm_le_zero_iff.mp ((H v).sumline i|>.trans_eq hp'); unfold V' F'; rw [hk,hp',smul_zero,mul_zero,mul_zero,mul_zero]; exact waltz_nil _ _ _ rfl le_rfl le_rfl
    by_cases hz:i∈ Facet.mount (ratio G) v; · unfold V' F'; rw [mul_left_comm U,mul_left_comm V]; exact waltz_c _ _ _ (t v) (h _ v ((H v).travel hp') x_0 hz (H v).reads _ (H v).plot)
    unfold V' F' t turtle; rw [if_neg hz,zero_smul,abs_zero,zero_mul,mul_zero,mul_zero]; exact waltz_nil _ _ _ rfl le_rfl le_rfl
 have hh: ∑ i∈ S', F' i ≤ (g:ℝ)^4*z:=owing _ _ _ (fun i=>(H i).pos) Hp _ hp _
 apply waltz_m _ _ _ (waltz_s _ _ _ _ _ _ _ hv) <;> rw [←Finset.mul_sum]
 exact mul_le_mul_of_nonneg_left hh p
 exact mul_le_mul_of_nonneg_left hh u
end pay
end YM.CF.Lor
