import YM.SU5.Selected.Euro.Single
/-! # Full μ-phase continuation at all committed heights.
 Narrow probes also average keeping narrow; cost estimator uses separate extension.
 Uniqueness/extreme claims only within classes named. For future RSpace positions (non-aligned registry),
 no assumption/product rule enters. Limits still physical buffer ℓ. -/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)

open Tapestry
namespace Palate
open YM.CF.Pannier.Chancel
open Altitude Exhibition Ether
local notation "ℳ" => Dome (tent Y H)
local notation "pS" => Cloud (Dome (tent Y H))
local notation "Q₀" => FiniteGaugeDataPoly (tent Y H)
local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Only" => Vacancy.observable (tent Y H) true
variable (χ : CapCharacter Y H V Q Qc j false C)
local notation "M" s:max => liftCap Y H V Q Qc j false C s
local notation "f₀" χ:max s:max => marked Y H V Q Qc j false C χ s
variable {Z:Rack Λ l}{P:Clay Λ l}(U:Exhibition Y H i k I E Z P)
local notation "J_χ" => Selection.bill Y H V Q Qc j C U
local notation "uF" s:max=> vistaFinish Y H s U
variable (s:ℕ)
abbrev ticket (x:Only): ℳ:=⟨x.val,x.property.1⟩
lemma ticket_neutral (x:Only): ticket Y H x ∈ enclave (tent Y H):= glint Y H x
abbrev fromDome (x:ℳ)(t:x∈enclave K): Only:=⟨x.val,x.property,fun _=> (enclave_spec K).mp t⟩
lemma tariff (x:Only) : (J_χ χ) (pinhole ℳ s (ticket Y H x))= (Single.single Y H (marked Y H V Q Qc j false C χ)) s x := engaged Y H V Q Qc j C U χ s _
local notation "Λu" => (well Λ K l true Set.univ Set.univ)
-- allowed states on Λu. keep precise dependence on D. protect equality on off-neutral x. competitors on Λu don't require *different* physical lift choices.
abbrev coneStates := ↑(well Λ (tent Y H) l true Set.univ Set.univ) →ₗ[ℂ] ℂ
noncomputable def cones (χ:CapCharacter Y H V Q Qc j false C) : coneStates Y H:= (J_χ χ).comp (Λu).val.toLinearMap

-- need any height roof where x∈ well this. x∈boardedDB may include formal representation >s, suffice if actual decomposition in well up to it. collapse then.
section label
noncomputable def bean (x:Only) : Λu:= ⟨pinhole ℳ s (ticket Y H x), oneSlotWell Λ K l true Set.univ Set.univ s (Set.mem_univ s) (by rw [fullKeep,vestibuleFull]; exact Algebra.mem_top) (ticket_neutral Y H x) ⟩ -- tune Algebra.mem_top

def gathering (A:coneStates Y H) : Sample Y H true:= fun s x=> A (bean Y H s x)
include U
-- Constrain on well WHOLE; covers same-resolution Cov, etc. This is exact triple-etc on actual D (from same history even if not stated via D; transfer explicit). Preserve comparisons on all heights with competitor; not mixed D.
structure constrained (A:coneStates Y H): Prop where
 speaks_ : Consensus Y H Q true (gathering Y H A)
 costs (s:ℕ)(x:↑(well Λ (tent Y H) l true Set.univ Set.univ)) (p:x.val ∈ well Λ (tent Y H) l true Set.univ (Set.univ∩ Set.Iic s)) (v:Only) (eq:(uF s) x.val= ticket Y H v):
    A x= gathering Y H A s v -- participation and height
include V Q Qc C
lemma gathering_cone : gathering Y H (cones Y H V Q Qc j C U χ)= Single.single Y H (marked Y H V Q Qc j false C χ):=funext fun s=>funext fun i=> tariff Y H V Q Qc j C χ U s i -- order
lemma authorized : constrained Y H Q U (cones Y H V Q Qc j C U χ):= by
 let m:= marked Y H V Q Qc j false C χ
 refine ⟨?_, fun s x p v e=>?_⟩
 · rw [gathering_cone]; exact Single.exact_together Y H Q m (all_together Y H V Q Qc j false C χ)
 rw [gathering_cone]; change (J_χ χ) x.val= (f₀ χ s) (feel Y H v); rw [cardHeight Y H V Q Qc j C U χ s (gateIssued Λ K l true Set.univ Set.univ s p), e]; rfl -- map ext
lemma solves {A A':coneStates Y H} (v:constrained Y H Q U A)(y:constrained Y H Q U A')(e: gathering Y H A= gathering Y H A'): A=A':= by
 apply LinearMap.ext; intro x; obtain ⟨s,p⟩:= declaredGate Λ K l true _ _ x.property; let i:= (uF s) x.val; have ht: i∈enclave K:= (conserveNeutral Y H V Q Qc j C U s p).2
 rw [v.costs s x p (fromDome Y H i ht) (by rfl),y.costs s x p (fromDome Y H i ht) (by rfl),e]
variable (ℜ : Birthplace Y H V Q Qc j false C χ)
omit U V Q Qc C in
private lemma coalesced_cone (A A':coneStates Y H)(z:ℝ)(t:ℝ): gathering Y H ((z:ℂ) • A+(t:ℂ) • A') = joinedReading Y H true z t (gathering Y H A) (gathering Y H A'):= rfl
lemma elemental (L : LoneVac Y H V Q Qc j false C ℜ)(x y:coneStates Y H)(u:constrained Y H Q U x)(v:constrained Y H Q U y) (a:ℝ)(p:0<a)(t:a<1)
    (e: cones Y H V Q Qc j C U χ= (a:ℂ) • x+ ((1-a:ℝ):ℂ) • y):x=cones Y H V Q Qc j C U χ∧ y=cones Y H V Q Qc j C U χ:=by
 let m:=cones Y H V Q Qc j C U χ; have p':= authorized Y H V Q Qc j C χ U; have e':= gathering_cone Y H V Q Qc j C χ U
 have he:gathering Y H m= joinedReading Y H true a (1-a) (gathering Y H x) (gathering Y H y):= (congrArg (gathering Y H) e).trans (coalesced_cone ..) -- uTune
 obtain ⟨v₀,v₁⟩:= (Single.owner Y H V Q Qc j C ℜ L).2 (gathering Y H x) (gathering Y H y) u.speaks_ v.speaks_ a p t (e'.symm.trans he)
 exact ⟨solves Y H V Q Qc j C U u p' (v₀.trans e'.symm), solves Y H V Q Qc j C U v p' (v₁.trans e'.symm)⟩
end label

section narrow
variable (m : Side)(S: Finset Cover)
local notation "ν" => (K).c m
variable (z: Roomy S ((tent Y H).c m))(u:Swatch S)
local notation "nΛ" => naturalHue K S m (Roomy.seats z) u
lemma narrow (p:InTest K false S false (render S K u)) : InTest K false S false (render S K nΛ):= by
 let u':= appear S K m u; let F:= nΛ; let U:=appear S K m F
 obtain ⟨t,h',v⟩:= p.only_cont m
 have t' : u'=toMark t:= h'; have w:U=molasses u':=funext fun x=> by unfold U F; rw [allPrint]; simp_rw [Ether.direct]; rfl
 have hu:Continuous u':= t' ▸ show Continuous (toMark t) from v.comp continuous_fst -- direction
 let e:=fun x:Pane ν=> U (x,1); have p0:U=toMark e:=by
    -- first cook
    funext ⟨x,y⟩; change U (x,y)=U (x,1); rw [w]; exact first_cook (fun x y b=> by unfold u'; change u' x=u' y; rw [t']; exact congrArg t b) (x,y) (x,1) rfl
 have q:Continuous e:=by unfold e; rw [w]; exact (sweet hu).comp (continuous_id.prodMk continuous_const)
 obtain ⟨u,h0,p1,_,_⟩:= completeBay K m S U (appearSupport S K m F) z false (fun _=> ⟨e,p0,q⟩)
 have h2:u=F:= appear_inj S K m (Roomy.seats z) p1; subst u; exact h0
-- estimator by gauge averaging (support narrow), returns Family. use to read separated diagnostics. unconditional if S within hosp; always found; label `nΛ`. Preserve site support yes, not separate charges. estimator single vs neutral.
noncomputable def etched {x:Family (tent Y H)}(p:InTest (tent Y H) false S false x):ℳ := badge K S (naturalHue K S m (Roomy.seats z) (fabric S K p.widen))
local notation "wΛ" p:max => etched Y H m S z p
variable {v':Family (tent Y H)}
include V Qc U C
lemma narrow_read (p:InTest (tent Y H) false S false v')(X:Set RSpace)(u: printedHere Λ l s S X):
    let F:= wΛ p
    let L:= pinhole ℳ s F
    L∈ well Λ K l false X {s} ∧ J_χ χ L= phaseRead Y H V Q Qc j C χ s v':=by
 intro f k; constructor
 · refine oneSlotWell Λ K l false X ({s}) s rfl ⟨S,?_,u⟩ ?_
   · unfold f etched; apply show InTest K false S false (render S K (naturalHue _ _ _ _ _)) from narrow Y H m S z (fabric S K p.widen) (by rw [render_fabric]; exact p)
   unfold f etched; exact hue_neutral K S m (Roomy.seats z) (fabric S K p.widen)
 -- use trans avoiding rewriting v'
 unfold k; rw [engaged]; exact (congrArg χ ( (hue_cap Y H V Q Qc j C s (Roomy.seats z) (fabric S K p.widen)).symm.trans (congrArg (M s) (Subtype.ext (render_fabric S K p.widen))) )).trans (phase_read Y H V Q Qc j C s χ ⟨v',aux_test p.widen,fun p=>by cases p⟩).symm
-- `Stamped` product-vs-marginals in WELL via same v comparator. Lode charged => small. Does not compare free
noncomputable def illumined {x:Family (tent Y H)}(p:InTest (tent Y H) false S false x):= J_χ χ (pinhole ℳ s (wΛ p))
local notation "r₀" p:max => illumined Y H V Q Qc j C χ U s m S z p
lemma price_of {p:InTest (tent Y H) false S false v'}{X:Set RSpace}(u:printedHere Λ l s S X): r₀ p= phaseRead Y H V Q Qc j C χ s v':= (narrow_read Y H V Q Qc j C χ U s m S z p X u).2
variable (i':ℕ)(x':Fin i' → Cover)(a': Set RSpace)(v':Family (tent Y H))(b':SU.Slot)(e:ℝ)(ρ: Witness Y H V Q Qc j C χ v' b' s S x' a' e)
include ρ
lemma narrow_footprint : ∃ (x:Family (tent Y H)) (t:x∈ Lode K (Window.family b') x' S) (g:PairsC→ℂ)(p:Coeff false S g),
    let v:= InTest.seed («K»:=tent Y H) p
    let f:=Lode_test t
    r₀ f=0 ∧ r₀ (v.mul f)≠ r₀ v * r₀ f := by
 suffices h' : ∃ (x:Family K), ∃ t:x∈Lode K (Window.family b') x' S, ∃ (g:PairsC→ℂ), ∃ p:Coeff false S g,
        ¬ phaseRead Y H V Q Qc j C χ s (scalar K g*x)=phaseRead Y H V Q Qc j C χ s (scalar K g)*phaseRead Y H V Q Qc j C χ s x by
    obtain ⟨x,v,g,p,h'⟩:=h'; let u:=InTest.seed («K»:=tent Y H) p; let f:=Lode_test v
    refine ⟨x,v,g,p,?_⟩; dsimp only; have hz:= price_of Y H V Q Qc j C χ U s m S z (p:=f) ρ.physical.confined; rw [price_of Y H V Q Qc j C χ U s m S z (p:=u.mul f) ρ.physical.confined,hz,price_of Y H V Q Qc j C χ U s m S z (p:=u) ρ.physical.confined]; exact ⟨(ρ.ward s S).footprint ρ.physical.inject v,h'⟩ -- dependent f?
 by_contra! w; exact ρ.survives w
-- quantitative lower on mixed well and survives for Lode *sum*; similar quantitative criterion at all components via gaps. phase_read for whole. stronger two pair read visible in well height at initiating positions.
lemma initiatingWell : let F:= ticket Y H (ρ.physical.enter Y H true)
    let t:= pinhole ℳ s F
    t∈well Λ K l false a' {s} ∧ e<‖J_χ χ t‖:=by intro f p; refine ⟨oneSlotWell Λ K l false a' ({s}) s rfl ⟨S,(FilTest ρ.physical.initiates),ρ.physical.confined⟩ (ticket_neutral Y H _),?_⟩; have h': J_χ χ p=phaseRead Y H V Q Qc j C χ s v':=(engaged Y H V Q Qc j C U χ s f).trans (phase_read Y H V Q Qc j C s χ (bidding Y H f)).symm; rw [h']; exact ρ.margin
end narrow
end Palate
end YM.CF.Buffered.Afterglow.Tower.Selection
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Palate
#print axioms price_of
#print axioms narrow_read
#print axioms narrow_footprint
#print axioms initiatingWell
#print axioms authorized
#print axioms elemental
end YM.CF.Buffered.Afterglow.Tower.Selection.Palate
