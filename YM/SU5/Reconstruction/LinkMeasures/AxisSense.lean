import YM.SU5.Reconstruction.LinkMeasures.Quadrant
import YM.SU5.Reconstruction.PolarArchives.Console
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Tower Tower.SatinVerification PaymentCamera
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V:Universal Y H i k I E)(G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (S:Finset Cover)(s:ℕ)(w:Evens S)
local notation "μS" => actual S Λ l
local notation "W" => wingspan Λ l S
local notation "Bx" => PhaseChoice.transfer Y H G S s
local notation "Tx" => singer S w
local notation "rᵢ" i1:max => i (G.rows i1)
local notation "rₖ" i1:max => k (G.columns i1)

open Tower.Vacancy Tower.Selected Tower.FirstWindows PaymentCamera
local notation "q★" => Satori.qty S Λ l
open Tower.FirstWindows.PolarArchives Tower.Tilted Tower.Tilted.Ramp Tower.FirstWindows.WindRose Tower.PhaseChoice
variable (P:Tower.Tilted.Ramp)(gap:ℝ≥0)
open CF.Pannier.Chancel
variable (p:PhaseChoice.SupportedPhysically Λ l s S (Acres P gap))(m:Side)
variable (u:Hosp S ((tent Y H).c m))
local notation "L" => optic Y H V S s P
local notation "µ" => Domain Y H G false Set.univ
local notation "θD" => gust P (tent Y H)
include p
lemma rail_price (x y:Swatch S)(g:Zodiac ((tent Y H).c m)): L x y=L x (orbitC S (tent Y H) m y g):=by
 let f:= P.cuspF (tent Y H) (render S (tent Y H) x); let a:= orbitC S K m y g
 have ht:Tapestry.Circular S (g∘wrap _) (render S K y) (render S K a):= decorates K S _ y; have hv:=P.faces K (texture S K x)
 obtain ⟨z,h⟩:= both_colors ht hv (holy_grid S s P gap p)
 let U:=S∪ P.survey S
 exact (Papal.ledgerRule Y H V U s).gauge z _ _ ((hv.mono Finset.subset_union_right).mul ((texture S K y).mono Finset.subset_union_left)) ((hv.mono Finset.subset_union_right).mul ((texture S K a).mono Finset.subset_union_left)) h

include u
lemma panoramic (x y:Swatch S)(h: Continuous (appear S (tent Y H) m y)): L x (reynoldsC S K m y)=L x y := by
 let Q:= rView Y H V S s P x; change Q (∫ g,orbitC S (tent Y H) m y g∂domeLaw ((tent Y H).c m))=_
 have he(g):Q (orbitC S K m y g)=L x y:=(rail_price Y H V S s P gap p m x y g).symm
 rw [←(ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=ℂ) (𝕜:=ℂ) Q ((orbitC_cont S K m y u h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))]; simp_rw [he]; simp
lemma polls_S (x:Swatch S)(h:x∈ literal S): L (reynoldsC S K m x) (reynoldsC S K m x)= L x x:= by
 have v:= literal_measured S K m x h; rw [panoramic Y H V S s P gap p m u _ _ v,optic_mirror,panoramic Y H V S s P gap p m u _ _ v]; exact (optic_mirror Y H V S s P x x).symm
omit u p
noncomputable def Want : Prop:= ∀ (S:Finset Cover) (s:ℕ), PhaseChoice.SupportedPhysically Λ l s S (Acres P gap)→ ∀ x:Swatch S, 0≤ optic Y H V S s P x x
noncomputable def MaterialR : Prop:= ∀ (S:Finset Cover) (s:ℕ), PhaseChoice.SupportedPhysically Λ l s S (Acres P gap)→ ∀ x∈ literal S, Neutral (tent Y H) (render S (tent Y H) x) → 0 ≤ optic Y H V S s P x x
include p in
lemma primary (x:Swatch S)(h:x∈ literal S)(a:MaterialR Y H V P gap): 0≤ optic Y H V S s P x x:=by
 obtain ⟨m,h'⟩:= (Buffered.separates (tent Y H) S).exists; have e:Hosp S ((tent Y H).c m):=⟨h'⟩; rw [←polls_S Y H V S s P gap p m e x h]; exact a S s p (reynoldsC S (tent Y H) m x) (polled_lit S K m e x h) (neutralC S K m x e (literal_measured S K m x h))
private lemma c_limit {X:Type*}[TopologicalSpace X]{f:X→X→ℂ}(h:Continuous (Function.uncurry f)){x:ℕ→X}{y:X}(u:Tendsto x atTop (𝓝 y))(t:∀ i,0≤f (x i) (x i)): 0≤ f y y:= ge_of_tendsto (f:=fun i=>f (x i) (x i)) (h.continuousAt.tendsto.comp (u.prodMk_nhds u)) (Eventually.of_forall t)

include G in
lemma hj : MaterialR Y H V P gap → Want Y H V P gap:=fun u=> by
   intro S s p x; let B:= PhaseChoice.transfer Y H G S s; let Z:= wingspan Λ l S; obtain ⟨f,h,t,-⟩:= suggestions Y H V G S s x false nofun
   rw [optic_up Y H V G S s P gap p]; refine c_limit (X:=Swatch (wingspan Λ l S)) (optic_c Y H V (wingspan Λ l S) (s+1) P) t (fun i=> ?_); exact (optic_up Y H V G S s P gap p (f i) (f i)) ▸ primary Y H V S s P gap p (f i) (h i).1 u
lemma loops_root: MaterialR Y H V P gap ↔ Rectitude Y H V G P gap := by
 constructor
 · intro h; rintro ⟨x,s,F,f,rfl⟩ v; obtain ⟨⟨S,t,p⟩,_⟩:= (mem_insideAt F s).mp f; obtain ⟨g,u⟩:= accolade K S F t; subst F; exact (opamount Y H V G S s P gap p g g v) ▸ hj Y H V G P gap h S s p g
 intro h S s p x tx e; let a:= badge K S x; let f:= ticket Y H G s a; have he:a ∈ insideAt Λ l K true (Acres P gap) s:= by refine (mem_insideAt ..).mpr ⟨⟨S,texture ..,p⟩,fun _=> e⟩
 let v:f∈ Domain Y H G true (Acres P gap):=ticket_mem Y H G he
 let z: gust P K f*f∈µ := domain_le_lawDomain Y H G _ (pay_your Y H V G P gap v v)
 rw [opamount Y H V G S s P gap p x x z]; exact h ⟨f,v⟩ z
-- separate to avoid duplicate proof? reuse local lec migrate
include G in
lemma want_iff: Want Y H V P gap↔ MaterialR Y H V P gap:=⟨fun h S s p x _ _=> h S s p x,hj Y H V G P gap⟩
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.loops_root
