import YM.SU5.FiniteGaugeData.SalonG.Herd
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "D"=> Decko Y h a
local notation "X"=> (A.space:Type)
local notation "M" t:max=> store Y h t W' R a A
local notation "π"=>nectar Y h s W' R a
local notation "N" n:max=> energyS Λ d n
variable {f x:W (tent Y h)}(z:Plan Y h a d f)(y:Decko Y h a)(q:0<d)
local notation "V" z:max=> Wedge Y h s a d W' R A z q
local notation "δ"=> (energyS Λ d n)
-- consequence for insertions which themselves ARE period- and cutoff-dependent. Quantifiers for ANY adaptive paid Eff.Target-late with SMALL norm uniform all support and earning credits.A-Boire. Useful representation.Note caption.
section bean
variable {F G:Type*}[TopologicalSpace G]{P₁:ℕ→ℕ→ F→Prop}{U:F→G}
lemma uniformElig (C:G→Prop)(p:IsCompact (closure (Set.range U)))
   (h:∀ g:G,∃ v:Set G,v∈𝓝 g ∧ ∀ᶠ i in atTop,∀ᶠ k in atTop,∀ f:F,U f∈v→P₁ i k f→ C (U f)) :
   ∀ᶠ i in atTop,∀ᶠ k in atTop,∀ f:F,P₁ i k f→ C (U f) := by
 classical
 choose T hT P using h; obtain ⟨t,b,c⟩:=p.elim_nhds_subcover T (fun x _=>hT x)
 filter_upwards [(eventually_all_finset t).2 (fun i _=> P i)] with i p
 filter_upwards [(eventually_all_finset t).2 p] with k v f g
 have he:=c (subset_closure (Set.mem_range_self f)); obtain ⟨i,h⟩:= Set.mem_iUnion.mp he; obtain ⟨w,e⟩:= Set.mem_iUnion.mp h; exact v i w f e g
end bean
abbrev Lobby (B:ℝ):= {f:W (tent Y h) // ∃ h:Locator Kₜ f S, ‖reading Kₜ S f h‖≤ B}
variable (B ε:ℝ)(v':Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
include v'
lemma lobby_plan (f:Lobby Y h S B): Plan Y h a d f.val:= ⟨S,v',Classical.choose f.property⟩
local notation "b"=>Lobby Y h S B
include A q v'
abbrev transformAt (f:Lobby Y h S B) : A.space.Op:= Wedge Y h s a d W' R A (lobby_plan Y h S a d B v' f) q
lemma bookMenu : IsCompact (closure (Set.range (transformAt Y h S s a d W' R A q B v'))) := lounge Y h S s a d W' R A q B (fun f:Lobby Y h S B=>f.val) (lobby_plan Y h S a d B v') _ (fun i=> Classical.choose_spec i.property)
-- for each candidate violating norm target find OPEN room in op norm excluded at all late periods
omit v' q in
lemma density_purchase (x:A.space.Op)(p:1 < ‖x‖): ∃ i:ℕ, ∃ y:Decko Y h a, ∃ B₁:ℝ,0 < B₁ ∧
    ∀ᶠ z:A.space.Op in 𝓝 x, let y':= store Y h (s+i) W' R a A (warmV Y h a (energyS Λ d i) y)
                            ‖y'‖^2+B₁ < ‖z y'‖^2:= by
 obtain ⟨i,y,t⟩:∃ i:ℕ,∃ y: Decko Y h a, let y':= store Y h (s+i) W' R a A (warmV Y h a (energyS Λ d i) y); ‖y'‖ < ‖x y'‖:=by
    by_contra! hx; refine p.not_ge (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (warm_lift Y h s a d 0 W' R A _ (isClosed_le (x.continuous.norm) (continuous_norm.const_mul 1)) (fun i _ y=> (le_of_not_gt (hx i y)).trans_eq (one_mul _).symm)))
 let y':= store Y h (s+i) W' R a A (warmV Y h a (energyS Λ d i) y)
 have p:‖y'‖^2< ‖x y'‖^2:= (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr t
 let V':=(‖x y'‖^2-‖y'‖^2)/2
 exact ⟨i,y,V', by unfold V'; linarith,(show Continuous fun x:A.space.Op=> ‖x y'‖^2 from ((ContinuousLinearMap.apply ℂ A.space.space y').continuous.norm.pow _)).continuousAt (x:=x)|>.tendsto|>.eventually (lt_mem_nhds (show ‖y'‖^2+V'< ‖x y'‖^2 by unfold V'; linarith))⟩ -- maybe lemma

variable (B₁:ℝ)(w:0≤B)(p:0< ε)
include w p
lemma expanse : ∀ᶠ i:ℕ in atTop,∀ᶠ k in atTop,∀ y:Lobby Y h S B, Credential Y h s (u i) (v k) a d B₁ y.val→ ‖transformAt Y h S s a d W' R A q B v' y‖≤ 1+ε:=by
 apply uniformElig (fun x:A.space.Op => ‖x‖≤ 1+ε) (bookMenu Y h S s a d W' R A q B v')
 intro f
 rcases lt_or_ge ‖f‖ (1+ε) with t|t
 · let S': Set A.space.Op:={g|‖g‖ < 1+ε}; exact ⟨S',(continuous_norm (E:=A.space.Op)).continuousAt.tendsto (x:=f)|>.eventually (gt_mem_nhds t),Eventually.of_forall (fun _=> Eventually.of_forall (fun _ g p _=> (show ‖_‖ < _ from p).le))⟩ -- implicit
 obtain ⟨n,t₀,v₀,g,f'⟩:= density_purchase Y h s a d W' R A f (by linarith)
 let y':=(M (s+n)) (warmV Y h a (energyS Λ d n) t₀); let S': Set A.space.Op:={g| ‖y'‖^2+ v₀ < ‖g y'‖^2}; refine ⟨_, show S'∈𝓝 f from f',?_⟩
 filter_upwards [adaptive Y h S s a d n W' R A t₀ q v' B B₁ v₀ w g] with i F; filter_upwards [F] with k V' f t g'
 have he:= V' _ _ (Classical.choose_spec f.property) g'; change ‖y'‖^2+v₀<‖Wedge Y h s a d W' R A _ q y'‖^2 at t; unfold y' at t; rw [wedge_plus] at t; exact (t.not_ge he).elim

-- concrete threshold: all such cartridges f small -- REAL OPERATOR bound is paid at each gate, without picking f earlier/no smooth f etc.
theorem billboard : ∀ᶠ i:ℕ in atTop, ∀ᶠ k in atTop,∀ (f:W (tent Y h)) (e:Locator Kₜ f S), ‖reading Kₜ S f e‖≤ B → Credential Y h s (u i) (v k) a d B₁ f → ‖Wedge Y h s a d W' R A (f:=f) ⟨S,v',e⟩ q‖≤ 1+ε := (expanse Y h S s a d W' R A q B ε v' B₁ w p).mono fun i t=> t.mono fun k v f e t g=> v ⟨f,e,t⟩ g
#print axioms billboard
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
