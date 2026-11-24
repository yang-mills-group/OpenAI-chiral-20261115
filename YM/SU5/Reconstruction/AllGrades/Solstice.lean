import YM.SU5.Reconstruction.AllGrades.ParityComfort
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Fm"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open WindRose PolarArchives ConePrice SelectionAnalysis Chambers Brazier
variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "mK"=> marks (timeMesh Λ)
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Ω₀"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped a false (C a)
local notation "F₊"=> Domain Y H G false (flank a 0)
local notation "Sm" m:max=> strip a (-(m:ℝ)) (m:ℝ)
local notation "Qt" m:max=> flank a (m:ℝ)
local notation "bM" d:max=> strip a (-d) d
local notation "A₀"=> atlasAt Y H V G
local notation "Pt" m:max=> Pub Y H a m
local notation "Bk" d:max f:max => (((badge Y H V G D a b d (atlasAt Y H V G)) f))
local notation "Px" u:max f:max=> ticket Y H G u f
local notation "rF"=> studio (tent Y H) a 0 b
local notation "rW"=> studio (tent Y H) a 0 false
local notation "Δ"=> timeMesh Λ
local notation "Wq" n:max=> walkC Y H a b n
local notation "Tr"=> cruise Y H a b

/-! # Unconditional even Spacebody voter equivalence & movement. -/
open Nymph
local notation "SJ"=> displacement Y H V G.history G.clipped j false (C j) χ a (C a)
local notation "KJ"=> indoor Y H V G.history G.clipped a false (C a) SJ
local notation "Τ"=> voterAt Y H V G C j χ
local notation "Q" t:max => badge Y H V G D a false t Τ
local notation "B⚬" t:max x:max=> bud Y H V t G.history G.clipped a false (C a) SJ x
local notation "FA"=>studio (tent Y H) a 0 false
local notation "FW" t:max=> Tower.Field Y H t a 0 false
local notation "ρ" t:max u:max p:max x:max=> homePlane Y H V G D a false t u p x
local notation "Sx"=> Works Y H V G D a false Τ

/-! Mix awake at ROOT.Prepare ANY two graded studio badges, not sending supports to zero. -/
local notation "K♯"=> (i ∘ G.rows) ∘ D.indexN
local notation "K♮"=> (k ∘ G.columns) ∘ D.indexN
variable (t u:ℕ)(x y:studio (tent Y H) a 0 b)
  (V₁ V₂:Finset Cover) (p:InTest (tent Y H) true V₁ b x.val) (q:InTest (tent Y H) true V₂ b y.val)
local notation "Ea"=> W
local notation "pipelineX" r:max=> Garret.quarry Y H s (K♯ r) (K♮ r) b V₁ x.val (u-s)
local notation "pipelineY" r:max=> Garret.quarry Y H t (K♯ r) (K♮ r) b V₂ y.val (u-t)
local notation "PA" t:max x:max=> badge Y H V G D a b t (atlasAt Y H V G) x
local notation "PZ" t:max x:max=> badge Y H V G D a b t (voterAt Y H V G C j χ) x
variable (r: s ≤ u)(r':t ≤ u)
include V
private lemma sharp_tracks {x:ℕ→ Family (tent Y H)}{y:Family (tent Y H)}{U:Finset Cover} (p:BQueue U x y): Tendsto (fun q=> sharp Y H s (K♯ q) (K♮ q) (x q)) atTop (𝓝 (E s y)):=by
 refine (Garret.trend Y H V s p).congr_dist ?_
 obtain ⟨A,v,g,h⟩:=p.bdd; obtain ⟨c,_,e⟩:=G.history.implements s U; rw [Metric.tendsto_nhds]; intro δ h'; filter_upwards [h, D.thinned.tendsto_atTop.eventually (e (δ/(A+1)) (by positivity))] with z g h
 rw [Real.dist_0_eq_abs,abs_of_nonneg dist_nonneg, dist_comm, dist_eq_norm]; apply ((h _ (p.whereTo z) _ g).2.2.2.2.1).trans_lt; exact (by have h:δ/(A+1)*(A+1)=δ:= div_mul_cancel₀ _ (by positivity); nlinarith [div_pos h' (show 0<A+1 by linarith)])
private lemma Fitters (x:Family K)(p:InTest (tent Y H) true V₁ b x): ∃ A:ℝ,0<A∧
    pay (Garret.launch Y H G D b s u x) A∧(∀ᶠ r:ℕ in atTop,pay (Garret.quarry Y H s (K♯ r) (K♮ r) b V₁ x u) A)∧
    ∀e:ℝ,0< e→ ∀ᶠ r:ℕ in atTop,pay (Garret.quarry Y H s (K♯ r) (K♮ r) b V₁ x u-Garret.launch Y H G D b s u x) e:=by
  obtain ⟨C,v⟩:= valuation Y H p; have hv: pay x (C+1):=fun i x=>(v i x).trans (by linarith); have hx:0≤C:= pay_nonneg (show pay x C from v); obtain ⟨B,u',t⟩:=Garret.journey_on_prices Y H V s G D b V₁ u -- order highWire: `t` preceding b? see
  let q:=t 1 zero_lt_one; obtain ⟨i,b'⟩:= q.exists; refine ⟨_,mul_pos u' (show 0<C+1 by positivity),(b' x p _ hv).1,q.mono (fun i z=> (z x p _ hv).2.1),fun e t'=>?_⟩; filter_upwards [t (e/(C+1)) (by positivity)] with i h; let hp:= (h x p _ hv).2.2; rwa [div_mul_cancel₀ _ (by positivity)] at hp
local notation "S" t:max r:max=> volumeAround Λ l t r
abbrev sceneAt (i':ℕ):= poleForm (tent Y H) a 0 b (Garret.quarry Y H s (K♯ i') (K♮ i') b V₁ x.val (u-s)) (Garret.quarry Y H t (K♯ i') (K♮ i') b V₂ y.val (u-t))
local notation "fS"=> sceneAt Y H G D a b s t u x y V₁ V₂
include r r' p q
lemma crossroads:  -- tune
 Tendsto (fun z=> sharp Y H u (K♯ z) (K♮ z) (fS z)) atTop (𝓝 (inner ℂ (PA s x) (PA t y))) ∧ Tendsto (fun z=> price Y H V G C j χ u false (fS z)) atTop (𝓝 (inner ℂ (PZ s x) (PZ t y))) :=by
 let x₁t:=hP r x; let y₁t:=hP r' y; let z:= Ea x₁t.val y₁t.val; let S':= S (u-s) V₁; let U':= S (u-t) V₂; let T':= reflectedBox a 0 S' ∪ U'
 let A₁ := survives Y H V s G D p (u-s); let A₂:= survives Y H V t G D q (u-t); have ht: InTest K true T' false z:= NorthTapes.statement a 0 A₁ A₂
 let f(i):= if InTest K true T' false (fS i) then fS i else 0
 have hc(i:ℕ): InTest K true T' false (f i):=by unfold f; split; assumption; exact InTest.zero
 have hp: ∀ᶠ i in atTop,f i=fS i:=by
    filter_upwards [D.thinned.tendsto_atTop.eventually (living Y H V s V₁ G.history (u-s)),D.thinned.tendsto_atTop.eventually (living Y H V t V₂ G.history (u-t))] with i h g; unfold f; rw [if_pos (show InTest K true T' false (fS i) from NorthTapes.statement a 0 (h (u-s) le_rfl x.val b p) (g (u-t) le_rfl y.val b q))]
 obtain ⟨X,xv,h,hb,HX⟩:= Fitters Y H V G D b s (u-s) V₁ x.val p; obtain ⟨Y',yv,g,gb,HY⟩:= Fitters Y H V G D b t (u-t) V₂ y.val q
 have he{V:Family K}{x:ℝ}(p:pay V x): pay (Reflect.chord b • V) x:=by have h:=pay_scale p (Reflect.chord b); rwa [show ‖Reflect.chord b‖=1 from by cases b<;> simp[Reflect.chord],one_mul] at h
 have hq:BQueue T' f z:=by
    refine ⟨hc,ht,⟨X*Y',mul_pos xv yv,he (pay_mul (pay_flips K h a 0) g),?_⟩,?_⟩
    · filter_upwards [hb,gb,hp] with i h b e; rw [e]; exact he (pay_mul (pay_flips K h a 0) b)
    intro e q; let v:= e/(X+Y'); have hv:0<v:=by unfold v; positivity
    filter_upwards [gb,HX v hv,HY v hv,hp] with i g h' t p; rw [p]; unfold sceneAt z poleForm; rw [←smul_sub]; apply he; have ht:v*Y'+X*v=e:=by rw [mul_comm v,add_comm (Y'*v), ←add_mul]; exact mul_div_cancel₀ _ (by positivity)
    exact ht ▸ (floral_mir (tent Y H) a 0 h' t g h)
 rw [measures_forever _ _ _ _ _ a b _ r r', measures_forever _ _ _ _ _ a b _ r r']; exact ⟨(sharp_tracks Y H V G D u hq).congr' (hp.mono fun i h=>congrArg (sharp Y H u (K♯ i) (K♮ i)) h), (price_limit Y H V G C j χ u hq).congr' (hp.mono fun _ w=>congrArg (price Y H V G C j χ u false) w)⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.crossroads
