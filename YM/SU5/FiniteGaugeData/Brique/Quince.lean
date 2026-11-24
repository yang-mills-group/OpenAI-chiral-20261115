import YM.SU5.FiniteGaugeData.Brique.Vesta
import YM.SU5.FiniteGaugeData.Brique.Sequoia
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 430000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {g:ℝ}{u v:ℕ→ℕ} {I:ℕ→Family (tent Y h)→ℕ→ℂ} {E:ℕ→Family (tent Y h)→ℂ}
set_option quotPrecheck false
variable (K:Journey.Universal Y h u v I E)(s i k:ℕ) (Z:Finset Cover)
local notation "Kx" => tent Y h
local notation "Ω" => side Y i s
local notation "V" => storeH Λ.V
local notation "S₀" => (Y.voyage i).CapeT s
local notation "Ψ" k:max => Journey.compass Y i k s
local notation "ξ" => zen (slopeF Λ.W g) (V).C
local notation "σ0" => sold Y h s i
local notation "Σ" => region Z (side Y i s)
variable {D m n w:ℕ}{C c ε α θ:ℝ}
-- Linear form prices on the source torus (undo: supported even only). Does not require small Carnet across volume for propagation; use under `σ0` qualification. Coordinates released after lower price per volume & taking copies. 
include K in
lemma authority (H:Roomy Z (side Y i s)): ∃ L:Mark Ω→ₗ[ℂ]ℂ,∀ b:Family (tent Y h),InTest Kx true Z false b→L ((σ0) b)= E s b := by
 let M := (sold Y h s i).comp (composeQ Kx Z)
 have he : Injective M:= sold_catalog_inj Y h Z s i (roomy_hosp _ H)
 let A:=tune Y h Z s K; let B:=A.comp M.leftInverse; refine ⟨B,fun b t=>?_⟩; let v:= certifyAs Z (tent Y h) b t; rw [← Hierarchy.certified Z Kx b t]; exact congrArg A (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr he) v) -- syntax
variable {σ: Window.Family}
local notation "cV" => tailCost (storeH Λ.V).c (storeH Λ.V).C
local notation "Q" => ((Y.voyage i).X (Y.uv k)).gram s
section funds
-- pre-height (`Doctrine`) and receipts post choice
structure Mac (Λ:Preparation)(v:ℝ)(k:ℕ) : Prop where
 ripe : 0<v
 crisp : v<1
 pulse(N:Side)(p:k ≤ N.val) :∀ M:Tulip.Male, v ≤ pilotB N Λ.K.j M ∧ pilotB N Λ.K.j M ≤ 1-v
/- determine spatial density & rank-sector tilt power first. α chosen from only `zealous` and TODO prices. -/
variable {a t q η b:ℝ}{K₁ d j:ℕ}
structure Vast (Λ:Preparation) (α:ℝ) (v:ℝ)(k:ℕ) (d w:ℕ)(t δ:ℝ):Prop where
 font : Crags α Λ w δ
 mic : Mac Λ v k
 warmth : 0 < t
 -- Sparse density via lower d pitch. w generally later & greater. not required by comparison itself
 timbre : 2*tailCost (storeH Λ.V).c (storeH Λ.V).C d ≤ v/2
 love : tailCost (storeH Λ.V).c (storeH Λ.V).C w*(v/2)⁻¹+(2*tailCost (storeH Λ.V).c (storeH Λ.V).C w+t*(storeH Λ.V).C) ≤ δ-tailCost (storeH Λ.V).c (storeH Λ.V).C w
variable (P:Master Y s i)(O:s ≤ Y.uv k)
def per (v:ℝ)(m:ℕ) := (1+(v/2)⁻¹)^m
structure Community {c:Preparation}(σ:Window.Family){n:Side} (S U:Support (More n))(R:Finset (Site n))(o:Seat n) (F:Corset U S o)(W:Pane n→ℂ)(X:Mark n)(x:FC (Single n))(ι:Mark n →ₗ[ℂ]ℂ): Prop where
 unwear : Window.Brique.Free S X
 donor : covariant X
 marked : ι X≠0
 mark_shield: X=cargo F W x
 trio : ∃ t:List (Site n),t≠[] ∧ t.Nodup ∧ t.toFinset⊆ R ∧ Trio σ n (U\R.image node) t x
-- pose for individual resolution. H=boost^{-α}. Approximant of period is truly a basis member, with no stencil size restrictions beyond static S,U,R. master P requires ε.
include O P
lemma demographic (ι':Vast Λ α a K₁ d w t ε)(_p:Roomy Z (side Y i s))(T U:Support (More (side Y i s)))(M:Finset (Site (side Y i s)))(o:Seat (side Y i s))(F:Corset T (region Z Ω) o)(W:Pane (side Y i s)→ℂ)(x:CashMask F W U ((storeH Λ.V).e*t) ((Y.voyage i).CapeT s))(ι:Mark Ω→ₗ[ℂ]ℂ)(sT: Sparse d M)(σ : Window.Family)(qY: Lattice.halo w (M.image node)⊆ T)(x0:Lattice.halo w T⊆ U)(kX:U⊆ region Z Ω)(v₀:K₁ ≤ (side Y i s).val)(h₁: θ < ‖ι (cargo F W 1)‖)
 (L:∀ b:Mark (side Y i s), (∀ x,‖b x‖ ≤ per a M.card) → AtSupport false (region Z Ω) b → ∀ B:Mark (side Y i s), (∀ x,‖B x‖ ≤ per a M.card) → AtSupport false (region Z Ω) B →(∀ x:Orbit _, B (drawn ((Y.voyage i).CapeT s) x)= b (drawn ((Y.voyage i).CapeT s) x))→Crater w (tailCost (V).c (V).C w) ε (posters Y s i k P O w).bleed.peg (region Z Ω) B M.card false → ‖ι b‖≤θ): ∃ A y, Community (c:=Λ) σ (region Z Ω) T M o F W A y ι:= by
 let H:=ι'.mic; let G:=posters Y s i k P O w; let N:= side Y i s; let Φ:= ((Y.voyage i).X (Y.uv k)).gram s; let M0:=Φ.J.M; let f: Op (Single N):=Dial.spar Λ.K.j M0 1; let Hκ : Guard (1:Pane N) Λ.d:= guard0 Λ.dpos.le; have hG:IsStarProjection f:= G.bleed.pin _ Hκ; let xG:=G.bleed.peg.Ft false; have hpθ:xG 1=funde Λ.K.j M0 N 1:= jewel Λ.K.j Φ.J; have hθ:f=funde Λ.K.j M0 N 1 := (by unfold f Dial.spar; rw [profile_trivial]);
 let P0:= (storeH Λ.V).posse; let C':=(storeH Λ.V).C; let b:=a/2; have he:0<b:= half_pos H.ripe
 let Z₀:= P0.sparks P.2 M0 Λ.d P.1
 obtain ⟨A,hp,tr⟩:=casing_neighbor Z₀ d (1:Pane N) Hκ; have hj:1≤Λ.K.j:=by rw [Λ.kJ]; decide
 have hb:‖implant M f‖ ≤ 1-b:=by
    have he:(1-a)+2*cV d ≤ 1-b:=by unfold b; linarith only [ι'.timbre]
    refine le_trans ?_ he; exact combined hp tr sT (sub_nonneg.mpr H.crisp.le) (fun i _=> hθ ▸ coords _ hj _ H.ripe.le (H.pulse N v₀ _) i)
 obtain ⟨Y₀,Y'⟩:=prepared_trick σ M T f hj M0 hθ hG qY hb he (casing_neighbor Z₀ w _ Hκ); have hx:Etude σ M T (xG 1) (cV w*b⁻¹) b⁻¹ Y₀:= hpθ.symm ▸ hθ ▸ Y'
 let V' := (storeH Λ.V); have oZ:Casing N G.bleed.peg.e xG V'.c C' V'.e:= V'.posse.tanker Φ.J P.2 (Brush Λ.V _ (credit_full Y s i k O)) Λ.d P.1;
 have hT:M.image node⊆ T:=Subset.trans (halo_subset ..) qY; have hR:T⊆ region Z (side Y i s):= Subset.trans (Subset.trans (halo_subset ..) x0) kX
 have he(B:FC (Single N))(w':Etude σ M T (xG 1) (cV w*b⁻¹) b⁻¹ B): ‖ι (cargo F W B)‖ ≤ θ:=by
    have hv:∀ z,‖cargo F W B z‖ ≤ per a M.card:= fun z=> (cargo_bound _ x.faces B _).trans w'.weight; let X:= cargo F W B; have hs:= Stump.value (F:=F) x.faces hT hR w'
    exact L X hv hs.zone (cared U X) (fun z=> (cared_cost X U z).trans (hv z)) (cared_area X hs kX) (stampEq x B) (paid_copy (Z:=G.bleed.peg) oZ x w' x0 Λ.dpos.le (mul_nonneg (Real.exp_pos _).le P0.value.le) ι'.love kX)
 obtain ⟨A,ps,p,pH,h,v',w',x'⟩:= centBuys (Z:=G.bleed.peg) oZ ι hx Λ.dpos.le h₁ he
 exact ⟨cargo F W A,A,delivered F x.faces hR (w'.fines (fun i v=>hT (mem_image_of_mem _ (v' (List.mem_toFinset.mpr v)))) sdiff_subset), cargos F x.faces A ps, x', rfl,p,pH,h,v',w'⟩ -- term order F arguments
end funds
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
