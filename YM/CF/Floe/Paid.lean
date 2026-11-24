import YM.CF.Floe.Lore
import YM.CF.Jet.Pilot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
open Jet
open scoped ContDiff
set_option synthInstance.maxSize 22000
variable{K b c d r R A C:ℝ}
variable {m B N:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{n:ℕ}
variable (H:Kelp N R→ℂ) (p:0<R)(h:Looks _ H)(hc:Continuous H)(hP:∀ i,‖H i‖ ≤ A)(x: E) (f:E→Tenant.Input N)(ht:∀ᶠ y in 𝓝 x, TenantK (f y))(hv:Allows n (fun y=>skin (f y)) x c)
abbrev phiN(n:ℕ)(c R:ℝ):ℝ:= composeCost n ((1+(2:ℝ)^n/R)^n) c
include H p h hc hP ht hv
lemma painV : Allows n (fun y=>equalizer H (skin (f y))) x (phiN n c R*A):=by
 let V:Own N:=⟨f x,ht.self_of_nhds⟩
 let W:=skin V.val; have he:=allows_looks h hc (Set.subset_iUnion (fun i:Own N=>ball (skin i.val) R) V) p n hP; have hpE := he.comp (f:=fun y:E=>skin (f y)) hv
 refine (show Allows _ _ _ _ from hpE.mono ?_); unfold phiN composeCost; ring_nf; rfl
omit H p h hc hP ht hv
variable{e:ℝ}
abbrev Tagged (e K:ℝ)(n:ℕ)(U:E→ Pack m B)(S:Set E):=∀ x∈S,U x∈ payer m B e ∧ TransK n (fun t=>(U t).1) x K∧ToR n (fun t=>(U t).2) x K -- implicit bind? include e n K
-- use constant cues in outer payment possible. quant currently general v.Fast.
lemma brimA(n:ℕ)(p:0<R)(q:1 ≤ K)(B:Side): ∃ T:ℝ,0 ≤ T∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](m:Side)(H:Kelp (CSide m B) R→ℂ),Looks _ H→Continuous H→∀ A:ℝ,(∀ i, ‖H i‖ ≤A) →∀ (F:E→Skin m B) (Y:E→ArrayF m) (T' S:Sq)(v:Hub m)(x:E)(e:ℝ)(t: Phase.Zone), T'∈Phase.zone t → S∈Phase.zone t → ‖S-T'‖ ≤ 2/(way B:ℝ) →Room B e → TransK n F x K→arr n Y x K → (∀ᶠ i in 𝓝 x,Guard (F i) e∧ Verified m B margin (F i) (Y i) t) → Allows n (fun i=> accessK m B T' S v (F i) (Y i) (fun x=>H (uθ x p))) x (T*A):=by
 obtain ⟨C,g,h⟩:=markA n q B
 refine ⟨phiN n C R,by unfold phiN composeCost; positivity,fun E _ _ _ m H u v A t F Y T' S L x e l hx hp k V s y ht=>?_⟩
 let f(i:E):=stationP m B T' S L (F i) (Y i); have hz:∀ᶠ i in 𝓝 x,TenantK (f i):=ht.mono fun i h=>drives V h.1 h.2 hx hp k L; obtain ⟨w,ωt⟩:= (show Guard (F x) e∧ Verified m B margin (F x) (Y x) l from ht.self_of_nhds)
 apply (painV H p u v t x f hz (h E m T' S F Y x s y L e l hx hp V w ωt)).germ
 exact hz.mono (fun i p'=> by dsimp only; rw [entrance (show TenantK (stationP m B T' S L (F i) (Y i)) from p')]; exact (show equalizer H _=_ from dif_pos (show skin (f i)∈ Kelp (CSide m B) R from (uθ ⟨f i,p'⟩ p).property))) -- orientation
end YM.CF.Floe
