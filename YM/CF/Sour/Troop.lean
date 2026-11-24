import YM.CF.Sour.Tile
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
-- Goal transformed Echo on Ω, normal dagger later. support object D←image.W.K inverse.A.Sign canonical Fee.Real.T matter.Weight Z scaled accordingly.
abbrev Mx(s:Sweep n)(a:ℝ)(F:Raw (Openc (More n) a) (Single n)):Raw (Openc (More n) a) (Single n):=fun x=> ech s⁻¹ (F (fog s a x))
def curbV(s:Sweep n)(p q i j:JS):ℂ:= (γS s).val p i* star ((γS s).val q j)
abbrev noteU(s:Sweep n)(W:Toll JS)(p q:JS):=∑ i:JS,∑ j:JS, ‖curbV s p q i j‖ * W i j
lemma tea (s:Sweep n)(F:Op JS)(p q:JS): ech s F p q=∑ i:JS,∑ j:JS, curbV s p q i j * cSignX s.charge (F i j):=by
 unfold ech; rw [singT,twist_formula, mul_assoc, Matrix.mul_apply]; apply sum_congr rfl; intro i _; rw [Matrix.mul_apply,mul_sum]; apply sum_congr rfl; intro j _; unfold curbV; rw [mul_assoc]; congr 1; rw [mul_comm]; rw [show windX s.charge F i j=cSignX s.charge (F i j) from (by cases s.charge <;> rfl)]; rfl
lemma debtL(F:↥Ω→ℂ)(p:Looks _ F):Looks Ω fun X=>cSignX s.charge (F (fog s a X)):=by
 unfold fog; cases s with
 |mk r x b=>
          cases b
          · intro V u γ v; exact p V u (fog {s:=r,b:=x,charge:=false} a ∘ γ) (siteB (castX {s:=r,b:=x,charge:=false}) _ u v)
          exact realigns p _ fun V u γ v=> duet_h (castX {s:=r,b:=x,charge:=true}) (N:=n) _ u v
variable {Δ:Support (More n)} (F: Raw (Openc (More n) a) (Single n))(k:Toll (Single n))(p:Suite (badge _) (bail n a) (bail n a) Δ k F)
local notation "D₀"=> actY s⁻¹ Δ
local notation "V₀"=> forum n a
include p
lemma penny (i j x y:JS)(c:curbV s⁻¹ i j x y≠0): Expo (forum n a) (actY s⁻¹ Δ) i j (k x y) (fun d=> cSignX s.charge (F (fog s a d) x y)):=by
 let U(X:↥Ω):= F X x y; have he:= p.expo x y
 have hx(i j:JS)(g:(γS s⁻¹).val i j≠0)(w:node j.1.1∈Δ):node i.1.1∈ D₀:=by
    have hv: (boxA s⁻¹) (node i.1.1)=node j.1.1:= Tye.birth_l i j _ _ _ g; unfold actY; rw [mem_map_equiv]; exact hv.symm ▸ w
 have hu:Expo (forum n a) D₀ i j (k x y) (U ∘ fog s a):=by
    refine ⟨he.positive,fun t=>?_,fun d=> he.bounded _,fun d t=> ?_,he.connected.comp (gate_v ..)⟩
    · obtain ⟨g,v,l⟩:= he.triggered t; exact ⟨tock s Δ ▸ ((prow n (castX s)).plus g),hx i x (left_ne_zero_of_mul c) v, hx j y (fun t=> right_ne_zero_of_mul c ((congrArg star t).trans (star_zero _))) l ⟩
    have hv:= he.variation (fog s a d) (fog s a t); change _≤ k x y*_ at hv; have hZ:(forum n a).eval Δ (fog s a d) (fog s a t)=(forum n a).eval D₀ d t:=by change fare _ _ _/_=fare _ _ _ /_; unfold fog; rw [roseC, tock]; -- tune
    exact hv.trans_eq (congrArg _ hZ)
 cases z:s.charge; exact hu; exact hu.dual
lemma mini :Suite (badge _) (bail n a) (bail n a) D₀ (noteU s⁻¹ k) (Mx s a F):=by
 let P:=bail n a
 have hx(z):ech s (ech s⁻¹ z)=z:=by rw [paceK,inv_mul_cancel,beat_x]
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro g d; have ht:∀ Z:Op JS,ech s⁻¹ (ech s Z)=Z:=by intro Z; rw [paceK,mul_inv_cancel,beat_x]
   have hg:Injective (ech s):= by intro i j h; exact (ht i).symm.trans ((congrArg (ech s⁻¹) h).trans (ht j))
   apply hg; have he(Z W:Op JS):ech s (Z*W)=ech s Z*ech s W:=singm ..; unfold Mx; rw [he,he,hx,hx, show ech s ((P.run g).val)= _ from wardE s g,sway]; exact p.frame ..
 · intro i j; unfold Mx noteU; simp_rw [tea]; apply Expo.sumK; intro x _; apply Expo.sumK; intro y _; by_cases h:curbV s⁻¹ i j x y=0; · simp only [h,norm_zero,zero_mul]; exact Branch.nothing .. -- namespace
   exact (penny s a F k p i j x y h).discount _
 let F':= fun i=>windX s.charge (F (fog s a i)); have hv:(badge Ω).all F':=by
    intro i j; have he(v:↥Ω): F' v i j=cSignX s.charge (F (fog s a v) i j):=by unfold F'; exact (show ∀ k:Bool,∀ P:Op JS,windX k P i j=cSignX k (P i j) from (fun k P=>by cases k<;>rfl)) _ _
    simp_rw [he]; exact debtL s a _ (p.fuel i j)
 exact License.times _ (License.times (g:=F') _ (License.base _ ((γS s⁻¹).val)) hv) (License.base _ (star (γS s⁻¹).val)) -- tune universe
end YM.CF.Sour
